package edu.vt.cs.editscript.common;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;

import org.jgrapht.Graph;
import org.jgrapht.GraphMapping;
import org.jgrapht.alg.isomorphism.VF2GraphIsomorphismInspector;
import org.jgrapht.alg.isomorphism.VF2SubgraphIsomorphismInspector;
import org.jgrapht.graph.DefaultDirectedGraph;

import com.google.gson.Gson;

import edu.vt.cs.editscript.json.GraphDataJson;
import edu.vt.cs.editscript.json.GraphDataJson.GraphEdge;
import edu.vt.cs.editscript.json.GraphDataJson.GraphNode;
import edu.vt.cs.graph.ReferenceNode;
import edu.vt.cs.sql.SqliteManager;

/**
 * This class find the exact matches between commits.
 * If graph A of commit 1 is a subgraph of graph B of commit 2 or vice versa,
 * commit 1 and commit 2 are a pair of exact matches.
 * We uses the bug name from database table unique_bug, and the graph data is
 * stored in the table edit_script_table.
 * The result is stored in the table exact_match
 * 
 * @author Ye Wang
 * @since 05/24/2017
 *
 */
public class ExactMatchFinder {

	private static boolean executeFromScratch = true;
	
	public static void main(String[] args) throws Exception {
		Connection conn = SqliteManager.getConnection();
		Statement stmt = conn.createStatement();
		
		if (executeFromScratch)
			stmt.executeUpdate("DROP TABLE IF EXISTS exact_match");
		
		stmt.executeUpdate("CREATE TABLE IF NOT EXISTS exact_match (bn1 TEXT, gn1 INTEGER, "
				+ "bn2 TEXT, gn2 INTEGER, matched_graph TEXT, g1_graph TEXT, g2_graph TEXT, "
				+ "symbol_graph TEXT, node_num INTEGER, edge_num INTEGER)");
		
		ResultSet rs = stmt.executeQuery("SELECT DISTINCT bug_name FROM edit_script_table WHERE bug_name IN (SELECT bug_name FROM unique_bug)");
		List<String> bugNameList = new ArrayList<>();
		while (rs.next())
			bugNameList.add(rs.getString(1));
		rs.close();
		
		stmt.close();
		conn.close();
		
		for (int i = 0; i < bugNameList.size() - 1; i++) {
//			if (i < 312)
//				continue;
			System.out.println("########" + i);
			String bugName1 = bugNameList.get(i);
			List<Graph<GraphNode, GraphEdge>> graphList1 = getCommitGraphList(bugName1);
			for (int j = i + 1; j < bugNameList.size(); j++) {
//				if (j < 337)
//					continue;
//				System.out.println(j);
				String bugName2 = bugNameList.get(j);
				List<Graph<GraphNode, GraphEdge>> graphList2 = getCommitGraphList(bugName2);
				extractExactMatches(bugName1, graphList1, bugName2, graphList2);
			}
		}
		System.out.println("Done!");
		
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
	
	private static void extractExactMatches(String bugName1, List<Graph<GraphNode, GraphEdge>> graphList1, String bugName2, List<Graph<GraphNode, GraphEdge>> graphList2) throws SQLException {
		for (int gn1 = 0; gn1 < graphList1.size(); gn1++) {
			Graph<GraphNode, GraphEdge> g1 = graphList1.get(gn1);
			for (int gn2 = 0; gn2 < graphList2.size(); gn2++) {
				Graph<GraphNode, GraphEdge> g2 = graphList2.get(gn2);
				VF2SubgraphIsomorphismInspector<GraphNode,GraphEdge> isoInspector =
						new VF2SubgraphIsomorphismInspector<>(g1, g2, vertexComparator, edgeComparator);
				final Iterator<GraphMapping<GraphNode, GraphEdge>> isoIter = isoInspector.getMappings();
				
				Runnable task = new Runnable() {
					@Override
					public void run() {
						isoIter.hasNext();
					}
				};
				ExecutorService executorService = Executors.newSingleThreadExecutor();
				Future<?> future = executorService.submit(task);
				boolean isoIteratorTimeOut = false;
				try {
					future.get(5, TimeUnit.SECONDS);
				} catch (InterruptedException e) {
					e.printStackTrace();
				} catch (ExecutionException e) {
					e.printStackTrace();
				} catch (TimeoutException e) {
					future.cancel(true);
					isoIteratorTimeOut = true;
				} finally {
					executorService.shutdown();
				}
				
				if (isoIteratorTimeOut)
					continue;
				
				while (isoIter.hasNext()) {
					GraphMapping<GraphNode, GraphEdge> mapping = isoIter.next();
					boolean g1IsSubgraphOfG2 = true;
					for (GraphNode n: g1.vertexSet()) {
						if (mapping.getVertexCorrespondence(n, true) == null) {
							g1IsSubgraphOfG2 = false;
							break;
						}
					}
					for (GraphEdge e: g1.edgeSet()) {
						if (mapping.getEdgeCorrespondence(e, true) == null) {
							g1IsSubgraphOfG2 = false;
							break;
						}
					}
					boolean g2IsSubgraphOfG1 = true;
					for (GraphNode n: g2.vertexSet()) {
						if (mapping.getVertexCorrespondence(n, false) == null) {
							g2IsSubgraphOfG1 = false;
							break;
						}
					}
					for (GraphEdge e: g2.edgeSet()) {
						if (mapping.getEdgeCorrespondence(e, false) == null) {
							g2IsSubgraphOfG1 = false;
							break;
						}
					}
					GraphDataJson graphJson = null;
					int nodeNum = 0;
					int edgeNum = 0;
					if (g1IsSubgraphOfG2) {
						graphJson = generateSymbolGraph(g1);
						nodeNum = g1.vertexSet().size();
						edgeNum = g1.edgeSet().size();
						
					} else if (g2IsSubgraphOfG1) {
						graphJson = generateSymbolGraph(g2);
						nodeNum = g2.vertexSet().size();
						edgeNum = g2.edgeSet().size();
					}
					if (g1IsSubgraphOfG2 || g2IsSubgraphOfG1) {
						String matchedGraph = null;
						if (g1IsSubgraphOfG2 && g2IsSubgraphOfG1)
							matchedGraph = "both";
						else if (g1IsSubgraphOfG2)
							matchedGraph = "g1";
						else
							matchedGraph = "g2";
						Connection conn = SqliteManager.getConnection();
						PreparedStatement ps = conn.prepareStatement("INSERT INTO exact_match (bn1,gn1,bn2,gn2,matched_graph,g1_graph,g2_graph,symbol_graph,node_num,edge_num) VALUES (?,?,?,?,?,?,?,?,?,?)");
						ps.setString(1, bugName1);
						ps.setInt(2, gn1);
						ps.setString(3, bugName2);
						ps.setInt(4, gn2);
						ps.setString(5, matchedGraph);
						Gson gson = new Gson();
						ps.setString(6, gson.toJson(GraphDataJson.convert(g1)));
						ps.setString(7, gson.toJson(GraphDataJson.convert(g2)));
						ps.setString(8, gson.toJson(graphJson));
						ps.setInt(9, nodeNum);
						ps.setInt(10, edgeNum);
						ps.executeUpdate();
						ps.close();
						conn.close();
						break;
					}
				}
			}
		}
	}
	
	public static GraphDataJson generateSymbolGraph(Graph<GraphNode, GraphEdge> g) {
		GraphDataJson graphJson = new GraphDataJson();
		Map<GraphNode, GraphNode> symbolNodeMap = new HashMap<>();
		int nodeNum = 0;
		for (GraphNode n: g.vertexSet()) {
			int nodeType = n.getType();
			String typeString = ReferenceNode.getTypeString(nodeType);
			String symbolName = typeString + nodeNum;
			GraphNode symbolNode = graphJson.new GraphNode(symbolName, nodeType);
			symbolNodeMap.put(n, symbolNode);
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
			graphJson.addEdge(symbolEdge);
		}
		return graphJson;
	}
	
	public static List<Graph<GraphNode, GraphEdge>> getCommitGraphList(String bugName) throws SQLException {
		List<String> jsonList = getCommitGraphJsonList(bugName);
		List<Graph<GraphNode, GraphEdge>> graphList = convertJsonListToGraphList(jsonList);
		return graphList;
	}
	
	private static List<String> getCommitGraphJsonList(String bugName) throws SQLException {
		Connection conn = SqliteManager.getConnection();
		Statement stmt = conn.createStatement();
		
		ResultSet rs = stmt.executeQuery("SELECT graph_data FROM edit_script_table WHERE bug_name=\"" + bugName + "\" ORDER BY graph_num ASC");
		List<String> graphJsonList = new ArrayList<>();
		while (rs.next()) {
			graphJsonList.add(rs.getString(1));
		}
		rs.close();
		
		stmt.close();
		conn.close();
		
		return graphJsonList;
	}
	
	public static Graph<GraphNode, GraphEdge> convertGraphJsonToObject(String json) {
		Gson gson = new Gson();
		GraphDataJson graphData = gson.fromJson(json, GraphDataJson.class);
		Graph<GraphNode, GraphEdge> graph = graphData.getJgrapht();
		return graph;
	}
	
	private static List<Graph<GraphNode, GraphEdge>> convertJsonListToGraphList(List<String> jsonList) {
		List<Graph<GraphNode, GraphEdge>> graphList = new ArrayList<>();
		for (String json: jsonList) {
			graphList.add(convertGraphJsonToObject(json));
		}
		return graphList;
	}
}
