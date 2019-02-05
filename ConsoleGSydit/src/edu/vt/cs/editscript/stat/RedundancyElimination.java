package edu.vt.cs.editscript.stat;

import java.lang.reflect.Type;
import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.jgrapht.Graph;
import org.jgrapht.alg.isomorphism.VF2GraphIsomorphismInspector;
import org.jgrapht.graph.DefaultDirectedGraph;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.reflect.TypeToken;

import edu.vt.cs.editscript.json.ScriptEdge;
import edu.vt.cs.editscript.json.ScriptNode;
import edu.vt.cs.graph.ReferenceNode;
import edu.vt.cs.sql.SqliteManager;

/**
 * A pair of isomorphism subgraphs can be a subset of another pair. Thus, 
 * the data will be refined and a new table script_stat_refined_mapping
 * will store the refined data. The subset pairs will not appear in the 
 * new table.<br/>
 * Sadly, there is no such subset mappings<br/>
 * I will eliminate the isomorphism mappings within 2 graphs.
 * 
 * @author Ye Wang
 * @since 04/13/2017
 *
 */
public class RedundancyElimination {
	
	private static boolean executeFromScratch = true;
	
	public static void main(String[] args) throws SQLException {
		Connection conn = SqliteManager.getConnection();
		Statement stmt = conn.createStatement();
		
		if (executeFromScratch)
			stmt.executeUpdate("DROP TABLE IF EXISTS script_stat_refined_mapping");
		
		stmt.executeUpdate("CREATE TABLE IF NOT EXISTS script_stat_refined_mapping (bn1 TEXT, gn1 INTEGER, bn2 TEXT, gn2 INTEGER, mapping_num INTEGER, subgraph1 TEXT, subgraph2 TEXT, node_map TEXT, edge_map TEXT)");
		
		
		// Get distinct subgraph pairs
		ResultSet rs = stmt.executeQuery("SELECT COUNT(*) FROM (SELECT DISTINCT bn1, gn1, bn2, gn2 FROM script_stat_mapping_with_script)");
		rs.next();
		int distinctPairNum = rs.getInt(1);
		rs.close();
		
		String sql1 = "SELECT mapping_num, subgraph1, subgraph2, node_map, edge_map "
				+ "FROM script_stat_mapping_with_script WHERE bn1=? AND gn1=? AND bn2=? AND gn2=?";
		PreparedStatement pstmt = conn.prepareStatement(sql1);
		
		Gson gson = new Gson();
		Gson gson2 = new GsonBuilder().enableComplexMapKeySerialization().create();
		Type scriptEdgeListType = new TypeToken<List<ScriptEdge>>(){}.getType();
		Type nodeMapType = new TypeToken<Map<ScriptNode, ScriptNode>>(){}.getType();
		Type edgeMapType = new TypeToken<Map<ScriptEdge, ScriptEdge>>(){}.getType();
		
		for (int offset = 0; offset< distinctPairNum; offset++) {
			
			System.out.println(offset + 1 + " / " + distinctPairNum);
			
			rs = stmt.executeQuery("SELECT DISTINCT bn1, gn1, bn2, gn2 FROM script_stat_mapping_with_script LIMIT 1 OFFSET " + offset);
			rs.next();
			String bn1 = rs.getString(1);
			int gn1 = rs.getInt(2);
			String bn2 = rs.getString(3);
			int gn2 = rs.getInt(4);
			rs.close();
			
			pstmt.setString(1, bn1);
			pstmt.setInt(2, gn1);
			pstmt.setString(3, bn2);
			pstmt.setInt(4, gn2);
			rs = pstmt.executeQuery();
			List<IsoPairData> dataList = new ArrayList<>();
			while (rs.next()) {
				int mappingNum = rs.getInt(1);
				String subgraph1 = rs.getString(2);
				String subgraph2 = rs.getString(3);
				String nodeMap = rs.getString(4);
				String edgeMap = rs.getString(5);
				
				List<ScriptEdge> sg1 = gson.fromJson(subgraph1, scriptEdgeListType);
				List<ScriptEdge> sg2 = gson.fromJson(subgraph2, scriptEdgeListType);
				
				Map<ScriptNode, ScriptNode> nMap = null;
				try {
					nMap = gson.fromJson(nodeMap, nodeMapType);
				} catch (com.google.gson.JsonSyntaxException e) {
					System.out.printf("%s, %d, %s, %d, %d", bn1, gn1, bn2, gn2, mappingNum);
					System.out.println();
					System.out.println(nodeMap);
					System.exit(-1);
				}
				Map<ScriptEdge, ScriptEdge> eMap = gson.fromJson(edgeMap, edgeMapType);
				
				IsoPairData pairData = new IsoPairData(mappingNum, sg1, sg2, nMap, eMap);
				dataList.add(pairData);
			}
			
			// Check redundant graphs
			Set<IsoPairData> redundancySet = new HashSet<>();
			for (int i = 0; i < dataList.size(); i++) {
				IsoPairData iso1 = dataList.get(i);
				if (redundancySet.contains(iso1))
					continue;
				for (int j = 0; j < dataList.size(); j++) {
					if (i == j)
						continue;
					IsoPairData iso2 = dataList.get(j);
					if (redundancySet.contains(iso2))
						continue;
					boolean iso2IsRedundant = checkSubsetRedundancy(iso1, iso2);
					if (iso2IsRedundant)
						redundancySet.add(iso2);
					if (haveSameStructure(iso1, iso2)) {
						redundancySet.add(iso2);
					}
					
					
				}
			}
			
			List<IsoPairData> targetDataList = new ArrayList<>(dataList);
			targetDataList.removeAll(redundancySet);
			
			// store data in table script_stat_refined_mapping
			String sql2 = "INSERT INTO script_stat_refined_mapping (bn1, gn1, bn2, gn2, mapping_num, subgraph1, subgraph2, node_map, edge_map) VALUES (?,?,?,?,?,?,?,?,?)";
			PreparedStatement ps = conn.prepareStatement(sql2);
			ps.setString(1, bn1);
			ps.setInt(2, gn1);
			ps.setString(3, bn2);
			ps.setInt(4, gn2);
			for (IsoPairData d: targetDataList) {
				ps.setInt(5, d.mappingNum);
				ps.setString(6, gson2.toJson(d.sg1, scriptEdgeListType));
				ps.setString(7, gson2.toJson(d.sg2, scriptEdgeListType));
				ps.setString(8, gson2.toJson(d.nMap, nodeMapType));
				ps.setString(9, gson2.toJson(d.eMap, edgeMapType));
				ps.executeUpdate();
			}
			ps.close();
			
		} // end for-loop offset
		
		
		pstmt.close();
		stmt.close();
		conn.close();
	}

	/**
	 * Check if dataB is a subset of dataA
	 * @param dataA
	 * @param dataB
	 * @return true if dataB is a subset of dataA
	 */
	private static boolean checkSubsetRedundancy(IsoPairData dataA, IsoPairData dataB) {
		for (ScriptEdge e: dataB.sg1) {
			if (!dataA.sg1.contains(e))
				return false;
			else {
				ScriptEdge edgeInSg2DataA = dataA.eMap.get(e);
				ScriptEdge edgeInSg2DataB = dataB.eMap.get(e);
				if (!edgeInSg2DataA.equals(edgeInSg2DataB))
					return false;
			}
			
		}
		
		return true;
	}
	
	public static Comparator<ScriptNode> nodeComparator = new Comparator<ScriptNode>() {
		@Override
		public int compare(ScriptNode n1, ScriptNode n2) {
			// TODO Auto-generated method stub
			return n1.getType() - n2.getType();
		}
	};
	
	public static Comparator<ScriptEdge> edgeComparator = new Comparator<ScriptEdge>() {
		@Override
		public int compare(ScriptEdge e1, ScriptEdge e2) {
			// TODO Auto-generated method stub
			return e1.getType() - e2.getType();
		}
	};
	
	/**
	 * Check if dataB and dataA are isomorphism with respect to node type and edge type
	 * @param dataA
	 * @param dataB
	 * @return true if they are isomorphism
	 */
	private static boolean haveSameStructure(IsoPairData dataA, IsoPairData dataB) {
		Graph<ScriptNode, ScriptEdge> gA = buildGraph(dataA.sg1);
		Graph<ScriptNode, ScriptEdge> gB = buildGraph(dataB.sg2);
		
		VF2GraphIsomorphismInspector<ScriptNode, ScriptEdge> isoInspector =
				new VF2GraphIsomorphismInspector<>(gA, gB, nodeComparator, edgeComparator);
		return isoInspector.isomorphismExists();
	}
	
	public static Graph<ScriptNode, ScriptEdge> buildGraph(List<ScriptEdge> edges) {
		Graph<ScriptNode, ScriptEdge> g = new DefaultDirectedGraph<ScriptNode, ScriptEdge>(ScriptEdge.class);
		for (ScriptEdge e: edges) {
			ScriptNode src = e.getSrc();
			ScriptNode dst = e.getDst();
			g.addVertex(src);
			g.addVertex(dst);
			g.addEdge(src, dst, e);
		}
		return g;
	}


}

class IsoPairData {
	int mappingNum;
	List<ScriptEdge> sg1;
	List<ScriptEdge> sg2;
	Map<ScriptNode, ScriptNode> nMap;
	Map<ScriptEdge, ScriptEdge> eMap;
	
	public IsoPairData(int mappingNum, List<ScriptEdge> sg1, List<ScriptEdge> sg2, Map<ScriptNode, ScriptNode> nMap, Map<ScriptEdge, ScriptEdge> eMap) {
		this.mappingNum = mappingNum;
		this.sg1 = sg1;
		this.sg2 = sg2;
		this.nMap = nMap;
		this.eMap = eMap;
	}
}
