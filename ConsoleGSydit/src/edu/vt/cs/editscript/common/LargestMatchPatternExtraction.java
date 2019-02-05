package edu.vt.cs.editscript.common;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import org.jgrapht.Graph;
import org.jgrapht.GraphMapping;
import org.jgrapht.alg.isomorphism.VF2SubgraphIsomorphismInspector;

import com.google.gson.Gson;

import edu.vt.cs.editscript.json.GraphDataJson;
import edu.vt.cs.editscript.json.GraphDataJson.GraphEdge;
import edu.vt.cs.editscript.json.GraphDataJson.GraphNode;
import edu.vt.cs.sql.SqliteManager;

/**
 * This class extracts the patterns from largest matches and 
 * store them in the database table largest_match_pattern
 * @author Ye Wang
 * @since 06/10/2017
 *
 */
public class LargestMatchPatternExtraction {

	public static void main(String[] args) throws SQLException {
		Connection conn = SqliteManager.getConnection();
		Statement stmt = conn.createStatement();
		
		stmt.executeUpdate("DROP TABLE IF EXISTS largest_match_pattern");
		stmt.executeUpdate("CREATE TABLE IF NOT EXISTS largest_match_pattern "
				+ "(pattern_id INTEGER, shape TEXT, node_num INTEGER, edge_num INTEGER)");
		
		ResultSet rs = stmt.executeQuery("SELECT COUNT(*) FROM largest_match");
		int totalNum = 0;
		if (rs.next())
			totalNum = rs.getInt(1);
		rs.close();
		
		Gson gson = new Gson();
		
		Map<Graph<GraphNode, GraphEdge>, Integer> patternSet = new HashMap<>();
		
		for (int offset = 0; offset < totalNum; offset++) {
			rs = stmt.executeQuery("SELECT * FROM largest_match LIMIT 1 OFFSET " + offset);
			String jsonSubgraph = rs.getString("subgraph1");
			Graph<GraphNode, GraphEdge> subgraph = gson.fromJson(jsonSubgraph, GraphDataJson.class).getJgrapht();
			if (!subgraph.edgeSet().isEmpty())
				addPattern(patternSet, subgraph);
		}
		
		Set<Graph<GraphNode, GraphEdge>> finalPatternSet = new HashSet<>();
		for (Graph<GraphNode, GraphEdge> g: patternSet.keySet()) {
			if (patternSet.get(g) > 1)
				finalPatternSet.add(g);
		}
		
		
		PreparedStatement ps = conn.prepareStatement("INSERT INTO largest_match_pattern "
				+ "(pattern_id,shape,node_num,edge_num) VALUES (?,?,?,?)");
		int patternId = 0;
		for (Graph<GraphNode, GraphEdge> pattern: finalPatternSet) {
			patternId++;
			ps.setInt(1, patternId);
			ps.setString(2, GraphDataJson.convert(pattern).toJson());
			ps.setInt(3, pattern.vertexSet().size());
			ps.setInt(4, pattern.edgeSet().size());
			ps.executeUpdate();
		}
		
		ps.close();
		stmt.close();
		conn.close();
		
	}
	
	private static void addPattern(Map<Graph<GraphNode, GraphEdge>, Integer> patternSet, Graph<GraphNode, GraphEdge> added) {
//		Set<Graph<GraphNode, GraphEdge>> toBeRemoved = new HashSet<>();
//		boolean patternAlreayExists = false;
		for (Graph<GraphNode, GraphEdge> g: patternSet.keySet()) {
			if (isGraphASubgraphOfGraphB(added, g) && isGraphASubgraphOfGraphB(g, added)) {
				patternSet.put(g, patternSet.get(g) + 1);
				return;
			}
			
//			if (isGraphASubgraphOfGraphB(added, g))
//				return;
//			else if (isGraphASubgraphOfGraphB(g, added))
//				toBeRemoved.add(g);
		}
		Graph<GraphNode, GraphEdge> symbolGraph = ExactMatchFinder.generateSymbolGraph(added).getJgrapht();
		patternSet.put(symbolGraph, 1);
		
		
		
//		patternSet.removeAll(toBeRemoved);
//		Graph<GraphNode, GraphEdge> symbolGraph = ExactMatchFinder.generateSymbolGraph(added).getJgrapht();
//		patternSet.add(symbolGraph);
	}
	
	private static Comparator<GraphNode> vertexComparator = new Comparator<GraphNode>(){
		@Override
		public int compare(GraphNode n1, GraphNode n2) {
			return n1.getType() - n2.getType();
		}
	};
	
	private static Comparator<GraphEdge> edgeComparator = new Comparator<GraphEdge>(){
		@Override
		public int compare(GraphEdge e1, GraphEdge e2) {
			return e1.getType() - e2.getType();
		}
	};
	
	public static boolean isGraphASubgraphOfGraphB(Graph<GraphNode, GraphEdge> gA, Graph<GraphNode, GraphEdge> gB) {
		VF2SubgraphIsomorphismInspector<GraphNode,GraphEdge> isoInspector =
				new VF2SubgraphIsomorphismInspector<>(gA, gB, vertexComparator, edgeComparator);
		Iterator<GraphMapping<GraphNode, GraphEdge>> isoIter = isoInspector.getMappings();
		
		while (isoIter.hasNext()) {
			GraphMapping<GraphNode, GraphEdge> mapping = isoIter.next();
			boolean allNodesContained = true;
			for (GraphNode n: gA.vertexSet()) {
				if (mapping.getVertexCorrespondence(n, true) == null) {
					allNodesContained = false;
					break;
				}
			}
			if (allNodesContained) {
				boolean allEdgesContained = true;
				for (GraphEdge e: gA.edgeSet()) {
					if (mapping.getEdgeCorrespondence(e, true) == null) {
						allEdgesContained = false;
						break;
					}
				}
				if (allEdgesContained)
					return true;
			}
		}
		
		return false;
	}
}
