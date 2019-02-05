package edu.vt.cs.editscript.stat;

import java.lang.reflect.Type;
import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.Comparator;
import java.util.List;

import org.jgrapht.Graph;
import org.jgrapht.alg.isomorphism.VF2GraphIsomorphismInspector;

import com.google.gson.Gson;
import com.google.gson.reflect.TypeToken;

import edu.vt.cs.editscript.json.ScriptEdge;
import edu.vt.cs.editscript.json.ScriptNode;
import edu.vt.cs.sql.SqliteManager;

/**
 * Now the pattern mapping is stored in the form of pairs. I want to convert
 * these pairs to groups. For example, we have 2 pairs, (g1,g2), (g2,g3). There
 * are 3 graphs in these 2 pairs. I will convert the 2 pairs to a group
 * {g1, g2, g3}, which contains 3 graphs and has no duplicate graphs.
 * 
 * @author Ye Wang
 * @since 04/19/2017
 *
 */
public class PairToGroupConversion {
	
	private static boolean executeFromScratch = true;
	
	private static Comparator<ScriptNode> nodeComparator = new Comparator<ScriptNode>() {
		@Override
		public int compare(ScriptNode n1, ScriptNode n2) {
			if (n1.getType() != n2.getType())
				return 1;
			if (!n1.getName().equals(n2.getName()))
				return 1;
			return 0;
		}
	};
	
	private static Comparator<ScriptEdge> edgeComparator = new Comparator<ScriptEdge>() {
		@Override
		public int compare(ScriptEdge e1, ScriptEdge e2) {
			if (e1.getType() != e2.getType())
				return 1;
			return 0;
		}
	};

	public static void main(String[] args) throws SQLException {
		// For every pattern, we read data from table script_stat_data_with_pattern.
		Connection conn = SqliteManager.getConnection();
		Statement stmt = conn.createStatement();
		
		if (executeFromScratch)
			stmt.executeUpdate("DROP TABLE IF EXISTS script_stat_pair_to_group");
		
		stmt.executeUpdate("CREATE TABLE IF NOT EXISTS script_stat_pair_to_group (pattern_id INTEGER, bug_name TEXT, graph_num INTEGER, subgraph TEXT)");
		
		ResultSet rs = stmt.executeQuery("SELECT MAX(pattern_id) FROM script_stat_grouped_pattern");
		rs.next();
		int maxPatternId = rs.getInt(1);
		rs.close();
		
		Gson gson = new Gson();
		Type scriptEdgeListType = new TypeToken<List<ScriptEdge>>(){}.getType();
		
		PreparedStatement ps = conn.prepareStatement("SELECT subgraph FROM script_stat_pair_to_group WHERE pattern_id=? AND bug_name=? AND graph_num=?");
		
		PreparedStatement insertStmt = conn.prepareStatement("INSERT INTO script_stat_pair_to_group (pattern_id,bug_name,graph_num,subgraph) VALUES (?,?,?,?)");
		
		for (int patternId = 1; patternId <= maxPatternId; patternId++) {
			rs = stmt.executeQuery("SELECT bn1,gn1,bn2,gn2,mapping_num,subgraph1,subgraph2 FROM script_stat_data_with_pattern WHERE pattern_id=" + patternId);
			while (rs.next()) {
				String bn1 = rs.getString(1);
				int gn1 = rs.getInt(2);
				String bn2 = rs.getString(3);
				int gn2 = rs.getInt(4);
				int mappingNum = rs.getInt(5);
				String jsonSubgraph1 = rs.getString(6);
				String jsonSubgraph2 = rs.getString(7);
				
				List<ScriptEdge> edgeSubgraph1 = gson.fromJson(jsonSubgraph1, scriptEdgeListType);
				List<ScriptEdge> edgeSubgraph2 = gson.fromJson(jsonSubgraph2, scriptEdgeListType);
				
				Graph<ScriptNode, ScriptEdge> subgraph1 = RedundancyElimination.buildGraph(edgeSubgraph1);
				Graph<ScriptNode, ScriptEdge> subgraph2 = RedundancyElimination.buildGraph(edgeSubgraph2);
				
				ps.setInt(1, patternId);
				// check if subgraph1 is already in script_stat_pair_to_group
				ps.setString(2, bn1);
				ps.setInt(3, gn1);
				boolean graph1AlreadyInTable = false;
				ResultSet rs1 = ps.executeQuery();
				while (rs1.next()) {
					String jsonGraphInTable = rs1.getString(1);
					List<ScriptEdge> edgeGraphInTable = gson.fromJson(jsonGraphInTable, scriptEdgeListType);
					Graph<ScriptNode, ScriptEdge> graphInTable = RedundancyElimination.buildGraph(edgeGraphInTable);
					
					VF2GraphIsomorphismInspector<ScriptNode, ScriptEdge> isoInspector =
							new VF2GraphIsomorphismInspector<>(subgraph1, graphInTable, nodeComparator, edgeComparator);
					if (isoInspector.isomorphismExists()) {
						graph1AlreadyInTable = true;
						break;
					}
				}
				rs1.close();
				if (!graph1AlreadyInTable) {
					insertStmt.setInt(1, patternId);
					insertStmt.setString(2, bn1);
					insertStmt.setInt(3, gn1);
					insertStmt.setString(4, jsonSubgraph1);
					insertStmt.executeUpdate();
				}
				
				// check if subgraph2 is already in script_stat_pair_to_group
				ps.setString(2, bn2);
				ps.setInt(3, gn2);
				boolean graph2AlreadyInTable = false;
				ResultSet rs2 = ps.executeQuery();
				while (rs2.next()) {
					String jsonGraphInTable = rs2.getString(1);
					List<ScriptEdge> edgeGraphInTable = gson.fromJson(jsonGraphInTable, scriptEdgeListType);
					Graph<ScriptNode, ScriptEdge> graphInTable = RedundancyElimination.buildGraph(edgeGraphInTable);
					
					VF2GraphIsomorphismInspector<ScriptNode, ScriptEdge> isoInspector =
							new VF2GraphIsomorphismInspector<>(subgraph2, graphInTable, nodeComparator, edgeComparator);
					if (isoInspector.isomorphismExists()) {
						graph2AlreadyInTable = true;
					}
				}
				rs2.close();
				if (!graph2AlreadyInTable) {
					insertStmt.setInt(1, patternId);
					insertStmt.setString(2, bn2);
					insertStmt.setInt(3, gn2);
					insertStmt.setString(4, jsonSubgraph2);
					insertStmt.executeUpdate();
				}
			}
			rs.close();
			
		}
		
		insertStmt.close();
		ps.close();
		stmt.close();
		conn.close();
	}
}
