package edu.vt.cs.empirical;

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
import org.jgrapht.graph.DefaultDirectedGraph;

import com.google.gson.Gson;

import edu.vt.cs.editscript.json.GraphDataJson;
import edu.vt.cs.editscript.json.GraphDataJson.GraphEdge;
import edu.vt.cs.editscript.json.GraphDataJson.GraphNode;
import edu.vt.cs.editscript.json.GraphDataWithNodesJson;
import edu.vt.cs.graph.ReferenceNode;
import edu.vt.cs.sql.SqliteManager;

/**
 * 
 * @author Ye Wang
 * @since 03/19/2018
 *
 */
public class LMatchPatternExtraction {
	
	private String largestMatchTable;
	
	private String patternTable;
	
	public LMatchPatternExtraction(String largestMatchTable, String patternTable) {
		this.largestMatchTable = largestMatchTable;
		this.patternTable = patternTable;
	}
	
	public void execute() throws SQLException {
		Connection conn = SqliteManager.getConnection();
		Statement stmt = conn.createStatement();
		
		stmt.executeUpdate("DROP TABLE IF EXISTS " + patternTable);
		stmt.executeUpdate("CREATE TABLE IF NOT EXISTS " + patternTable
				+ " (pattern_id INTEGER, shape TEXT, node_num INTEGER, edge_num INTEGER)");
		
		ResultSet rs = stmt.executeQuery("SELECT COUNT(*) FROM " + largestMatchTable);
		int totalNum = 0;
		if (rs.next())
			totalNum = rs.getInt(1);
		rs.close();
		
		Gson gson = new Gson();
		
		Map<Graph<GraphNode, GraphEdge>, Integer> patternSet = new HashMap<>();
		
		for (int offset = 0; offset < totalNum; offset++) {
			rs = stmt.executeQuery("SELECT * FROM " + largestMatchTable + " LIMIT 1 OFFSET " + offset);
			String jsonSubgraph = rs.getString("subgraph1");
			Graph<GraphNode, GraphEdge> subgraph = gson.fromJson(jsonSubgraph, GraphDataWithNodesJson.class).getJgrapht();
			if (!subgraph.edgeSet().isEmpty())
				addPattern(patternSet, subgraph);
		}
		
		Set<Graph<GraphNode, GraphEdge>> finalPatternSet = new HashSet<>();
		for (Graph<GraphNode, GraphEdge> g: patternSet.keySet()) {
			if (patternSet.get(g) > 1)
				finalPatternSet.add(g);
		}
		
		
		PreparedStatement ps = conn.prepareStatement("INSERT INTO " + patternTable
				+ " (pattern_id,shape,node_num,edge_num) VALUES (?,?,?,?)");
		int patternId = 0;
		for (Graph<GraphNode, GraphEdge> pattern: finalPatternSet) {
			patternId++;
			ps.setInt(1, patternId);
			ps.setString(2, GraphDataWithNodesJson.convertToJsonClass(pattern).toJson());
			ps.setInt(3, pattern.vertexSet().size());
			ps.setInt(4, pattern.edgeSet().size());
			ps.executeUpdate();
		}
		
		ps.close();
		stmt.close();
		conn.close();
	}
	

	public static void main(String[] args) throws SQLException {
		String[] projects = {"aries", "cassandra", "derby", "mahout"};
		for (String project: projects) {
			String largestMatchTable = "em_largest_match_" + project;
			String patternTable = "em_largest_match_pattern_" + project;
			LMatchPatternExtraction extraction = new LMatchPatternExtraction(largestMatchTable, patternTable);
			extraction.execute();
		}
	}
	
	/**
	 * Used by convertToSymbolGraph
	 */
	private static GraphDataJson graphJson = new GraphDataJson();
	
	private static Graph<GraphNode, GraphEdge> convertToSymbolGraph(Graph<GraphNode, GraphEdge> g) {
		Map<GraphNode, GraphNode> symbolNodeMap = new HashMap<>();
		Graph<GraphNode, GraphEdge> symGraph = new DefaultDirectedGraph<GraphNode, GraphEdge>(GraphEdge.class); 
		int nodeNum = 0;
		for (GraphNode n: g.vertexSet()) {
			int nodeType = n.getType();
			String typeString = ReferenceNode.getTypeString(nodeType);
			String symbolName = typeString + nodeNum;
			GraphNode symbolNode = graphJson.new GraphNode(symbolName, nodeType);
			symbolNodeMap.put(n, symbolNode);
			symGraph.addVertex(symbolNode);
			nodeNum++;
		}
		for (GraphEdge e: g.edgeSet()) {
			GraphNode oldSrc = e.getSrc();
			GraphNode oldDst = e.getDst();
			int edgeType = e.getType();
			int edgeDep = e.getDep();
			GraphNode symbolSrc = symbolNodeMap.get(oldSrc);
			GraphNode symbolDst = symbolNodeMap.get(oldDst);
			GraphEdge symbolEdge = graphJson.new GraphEdge(symbolSrc, symbolDst, edgeType, edgeDep);
			symGraph.addEdge(symbolSrc, symbolDst, symbolEdge);
		}
		return symGraph;
	}
	
	private static void addPattern(Map<Graph<GraphNode, GraphEdge>, Integer> patternSet, Graph<GraphNode, GraphEdge> added) {
		for (Graph<GraphNode, GraphEdge> g: patternSet.keySet()) {
			if (isGraphASubgraphOfGraphB(added, g) && isGraphASubgraphOfGraphB(g, added)) {
				patternSet.put(g, patternSet.get(g) + 1);
				return;
			}
		}
		Graph<GraphNode, GraphEdge> symbolGraph = convertToSymbolGraph(added);
		patternSet.put(symbolGraph, 1);
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