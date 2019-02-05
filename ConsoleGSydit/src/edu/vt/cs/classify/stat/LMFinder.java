package edu.vt.cs.classify.stat;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;

import org.jgrapht.Graph;
import org.jgrapht.GraphMapping;
import org.jgrapht.alg.isomorphism.VF2SubgraphIsomorphismInspector;
import org.jgrapht.graph.DefaultDirectedGraph;

import com.google.gson.Gson;

import edu.vt.cs.editscript.common.GraphPair;
import edu.vt.cs.editscript.json.GraphDataWithNodesJson;
import edu.vt.cs.editscript.json.GraphDataJson.GraphEdge;
import edu.vt.cs.editscript.json.GraphDataJson.GraphNode;
import edu.vt.cs.sql.SqliteManager;

/**
 * 
 * This class finds the largest matches between two graphs.
 * This class is based on edu.vt.cs.editscript.common.LargestMatchFinder, which 
 * the author wants to remain, because of its potential future reuse. Therefore,
 * the author wrote this new class to incorporate new features.
 * 
 * 
 * @author Ye Wang
 * @since 03/05/2018
 *
 */
public class LMFinder {
	
	private boolean executeFromScratch;
	
	private String editScriptTable;
	
	private String largestMatchTable;
	
	public LMFinder(String editScriptTable, String largestMatchTable, boolean executeFromScratch) {
		this.editScriptTable = editScriptTable;
		this.largestMatchTable = largestMatchTable;
		this.executeFromScratch = executeFromScratch;
	}
	
	public LMFinder(String editScriptTable, String largestMatchTable) {
		this(editScriptTable, largestMatchTable, true);
	}
	
	/**
	 * This method is used to replace ExactMatchFinder.getCommitGraphList(String)
	 * @param bugName
	 * @throws SQLException
	 */
	private List<Graph<GraphNode, GraphEdge>> getCommitGraphList(String bugName) throws SQLException {
		Connection conn = SqliteManager.getConnection();
		Statement stmt = conn.createStatement();
		
		ResultSet rs = stmt.executeQuery("SELECT graph_data FROM " + editScriptTable + " WHERE bug_name=\"" + bugName + "\" ORDER BY graph_num ASC");
		List<String> graphJsonList = new ArrayList<>();
		while (rs.next()) {
			graphJsonList.add(rs.getString(1));
		}
		rs.close();
		
		stmt.close();
		conn.close();
		
		List<Graph<GraphNode, GraphEdge>> graphList = new ArrayList<>();
		Gson gson = new Gson();
		for (String json: graphJsonList) {
			GraphDataWithNodesJson graphData = gson.fromJson(json, GraphDataWithNodesJson.class);
			Graph<GraphNode, GraphEdge>	graph = graphData.getJgrapht();
			graphList.add(graph);
		}
		
		return graphList;
	}
	
	public void executeForCommitType(String commitType) throws SQLException {
		Connection conn = SqliteManager.getConnection();
		Statement stmt = conn.createStatement();
		
		if (executeFromScratch)
			stmt.executeUpdate("DROP TABLE IF EXISTS " + largestMatchTable);
		
		stmt.executeUpdate("CREATE TABLE IF NOT EXISTS " + largestMatchTable
				+ " (commit_type TEXT, bn1 TEXT, gn1 INTEGER,"
				+ "bn2 TEXT, gn2 INTEGER, graph1 TEXT, graph2 TEXT,subgraph1 TEXT,"
				+ "subgraph2 TEXT, node_num INTEGER, edge_num INTEGER)");
		
		String bugNameQuery = "SELECT DISTINCT bug_name FROM " + editScriptTable + " WHERE commit_type='" + commitType + "'";
		ResultSet rs = stmt.executeQuery(bugNameQuery);
		List<String> bugNameList = new ArrayList<>();
		while (rs.next())
			bugNameList.add(rs.getString(1));
		rs.close();
		
		stmt.close();
		conn.close();
		
		System.out.println("Total: " + bugNameList.size());
		for (int i = 0; i < bugNameList.size(); i++) {
			System.out.println("########" + (i + 1) + "/" + bugNameList.size());
			
			
			
			String bugName1 = bugNameList.get(i);
			List<Graph<GraphNode, GraphEdge>> graphList1 = getCommitGraphList(bugName1);
			for (int graphNum1 = 0; graphNum1 < graphList1.size(); graphNum1++) {
				Graph<GraphNode, GraphEdge> g1 = graphList1.get(graphNum1);
				Set<GraphPair> matchesForG1 = new HashSet<>();
				for (int j = 0; j < bugNameList.size(); j++) {
					if (i == j) continue;
					String bugName2 = bugNameList.get(j);
					List<Graph<GraphNode, GraphEdge>> graphList2 = getCommitGraphList(bugName2);
					for (int graphNum2 = 0; graphNum2 < graphList2.size(); graphNum2++) {
						Graph<GraphNode, GraphEdge> g2 = graphList2.get(graphNum2);
						Set<GraphPair> clonedMatches = new HashSet<>(matchesForG1);
						boolean timeOut = isTimeOut(new MatchExtraction(clonedMatches, g1, g2, bugName1, bugName2, graphNum1, graphNum2), 15);
						if (!timeOut)
							matchesForG1 = clonedMatches;
					}
					
				}
				
				// To fix a bug introduced by an unexpected result of JGraphT
//				System.out.println("Post-processing...");
				postProcessMatches(matchesForG1);
//				System.out.println("Post-process is done");
				
				storeMatches(matchesForG1, commitType);
			}
			
			
		}
		
		return;
	}
	
	public void execute() throws SQLException {
		Connection conn = SqliteManager.getConnection();
		Statement stmt = conn.createStatement();
		ResultSet rs = stmt.executeQuery("SELECT DISTINCT commit_type FROM " + editScriptTable);
		List<String> commitTypeList = new ArrayList<>();
		while (rs.next()) {
			String commitType = rs.getString(1);
			commitTypeList.add(commitType);
		}
		stmt.close();
		conn.close();
		for (String commitType: commitTypeList) {
			System.out.println("Commit Type: " + commitType);
			this.executeForCommitType(commitType);
		}
		System.out.println("Done!");
	}

	public static void main(String[] args) throws SQLException {
		String editScriptTable = "classification_initial_graph_aries";
		String largestMatchTable = "largest_match_initial";
		LMFinder finder = new LMFinder(editScriptTable, largestMatchTable);
		finder.execute();
	}
	
	private static void postProcessMatches(Set<GraphPair> matches) {
		Set<GraphPair> pairToBeRemoved = new HashSet<>();
		for (GraphPair checkingPair: matches) {
			Graph<GraphNode, GraphEdge> checkingSg = checkingPair.sg1;
			for (GraphPair pair: matches) {
				if (checkingPair == pair)
					continue;
				Graph<GraphNode, GraphEdge> sg = pair.sg1;
				boolean checkingSgIsSubgraphOfSg = true;
				for (GraphNode n: checkingSg.vertexSet()) {
					if (!sg.containsVertex(n)) {
						checkingSgIsSubgraphOfSg = false;
						break;
					}
				}
				if (checkingSgIsSubgraphOfSg) {
					pairToBeRemoved.add(checkingPair);
					break;
				}
			}
		}
		matches.removeAll(pairToBeRemoved);
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
	
	static void extractMatches(Set<GraphPair> pairCandidates,
			Graph<GraphNode, GraphEdge> g1, Graph<GraphNode, GraphEdge> g2,
			String bugName1, String bugName2, int graphNum1, int graphNum2) {
		VF2SubgraphIsomorphismInspector<GraphNode,GraphEdge> isoInspector =
				new VF2SubgraphIsomorphismInspector<>(g1, g2, vertexComparator, edgeComparator);
		Iterator<GraphMapping<GraphNode, GraphEdge>> isoIter = isoInspector.getMappings();
		
		while (isoIter.hasNext()) {
			GraphMapping<GraphNode, GraphEdge> mapping = isoIter.next();
			
			// Extract subgraphs
			Graph<GraphNode, GraphEdge> subgraph1 = new DefaultDirectedGraph<>(GraphEdge.class);
			Graph<GraphNode, GraphEdge> subgraph2 = new DefaultDirectedGraph<>(GraphEdge.class);
			for (GraphNode nodeInG1: g1.vertexSet()) {
				GraphNode nodeInG2 = mapping.getVertexCorrespondence(nodeInG1, true);
				if (nodeInG2 != null) {
					subgraph1.addVertex(nodeInG1);
					subgraph2.addVertex(nodeInG2);
				}
			}
			
			for (GraphEdge edgeInG1: g1.edgeSet()) {
				GraphEdge edgeInG2 = mapping.getEdgeCorrespondence(edgeInG1, true);
				if (edgeInG2 != null) {
					GraphNode srcNodeG1 = g1.getEdgeSource(edgeInG1);
					GraphNode dstNodeG1 = g1.getEdgeTarget(edgeInG1);
					subgraph1.addEdge(srcNodeG1, dstNodeG1, edgeInG1);
					GraphNode srcNodeG2 = g2.getEdgeSource(edgeInG2);
					GraphNode dstNodeG2 = g2.getEdgeTarget(edgeInG2);
					subgraph2.addEdge(srcNodeG2, dstNodeG2, edgeInG2);
				}
			}
			
			// Construct GraphPair
			GraphPair pair = new GraphPair();
			pair.bn1 = bugName1;
			pair.bn2 = bugName2;
			pair.gn1 = graphNum1;
			pair.gn2 = graphNum2;
			pair.g1 = g1;
			pair.g2 = g2;
			pair.sg1 = subgraph1;
			pair.sg2 = subgraph2;
			
			// Add GraphPair to candidate set
			if (!subgraph1.edgeSet().isEmpty())
				addGraphPair(pairCandidates, pair);
			
		}
	}
	
	private static boolean isTimeOut(Runnable task, long timeInSeconds) {
		ExecutorService executorService = Executors.newSingleThreadExecutor();
		Future<?> future = executorService.submit(task);
		boolean isoIteratorTimeOut = false;
		try {
			future.get(timeInSeconds, TimeUnit.SECONDS);
		} catch (InterruptedException e) {
			e.printStackTrace();
		} catch (ExecutionException e) {
			e.printStackTrace();
		} catch (TimeoutException e) {
			future.cancel(true);
			isoIteratorTimeOut = true;
			executorService.shutdownNow();
			if (!executorService.isTerminated())
				System.err.println("Not terminated");
			else
				System.err.println("Terminated!!");
		} finally {
			if (!executorService.isShutdown())
				executorService.shutdownNow();
		}
		
		return isoIteratorTimeOut;
	}
	
	private static void addGraphPair(Set<GraphPair> pairCandidates, GraphPair addedPair) {
		Graph<GraphNode, GraphEdge> addedSg = addedPair.sg1;
		Set<GraphPair> toBeRemoved = new HashSet<>();
		for (GraphPair p: pairCandidates) {
			Graph<GraphNode, GraphEdge> subgraph = p.sg1;
			if (isGraphASubgraphOfGraphB(addedSg, subgraph))
				return;
			else if (isGraphASubgraphOfGraphB(subgraph, addedSg)) {
				toBeRemoved.add(p);
			}
		}
		pairCandidates.removeAll(toBeRemoved);
		pairCandidates.add(addedPair);
	}
	
	private static boolean isGraphASubgraphOfGraphB(Graph<GraphNode, GraphEdge> gA, Graph<GraphNode, GraphEdge> gB) {
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
	
	private void storeMatches(Set<GraphPair> matches, String commitType) throws SQLException {
		Connection conn = SqliteManager.getConnection();
		Statement stmt = conn.createStatement();
		PreparedStatement ps = conn.prepareStatement("INSERT INTO " + largestMatchTable
				+ " (commit_type,bn1,gn1,"
				+ "bn2,gn2,graph1,graph2,subgraph1,subgraph2,node_num,edge_num) VALUES "
				+ "(?,?,?,?,?,?,?,?,?,?,?)");
		
		Gson gson = new Gson();
		for (GraphPair p: matches) {
			ps.setString(1, commitType);
			ps.setString(2, p.bn1);
			ps.setInt(3, p.gn1);
			ps.setString(4, p.bn2);
			ps.setInt(5, p.gn2);
			ps.setString(6, gson.toJson(GraphDataWithNodesJson.convertToJsonClass(p.g1)));
			ps.setString(7, gson.toJson(GraphDataWithNodesJson.convertToJsonClass(p.g2)));
			ps.setString(8, gson.toJson(GraphDataWithNodesJson.convertToJsonClass(p.sg1)));
			ps.setString(9, gson.toJson(GraphDataWithNodesJson.convertToJsonClass(p.sg2)));
			ps.setInt(10, p.sg1.vertexSet().size());
			ps.setInt(11, p.sg1.edgeSet().size());
			ps.executeUpdate();
			
		}
		ps.close();
		stmt.close();
		conn.close();
		
	}
	
	
}

class MatchExtraction implements Runnable {
	
	Set<GraphPair> matchesForG1;
	Graph<GraphNode, GraphEdge> g1;
	Graph<GraphNode, GraphEdge> g2;
	String bugName1;
	String bugName2;
	int graphNum1;
	int graphNum2;
	
	MatchExtraction(Set<GraphPair> matchesForG1, Graph<GraphNode, GraphEdge> g1,
			Graph<GraphNode, GraphEdge> g2, String bugName1, String bugName2,
			int graphNum1, int graphNum2) {
		this.matchesForG1 = matchesForG1;
		this.g1 = g1;
		this.g2 = g2;
		this.bugName1 = bugName1;
		this.bugName2 = bugName2;
		this.graphNum1 = graphNum1;
		this.graphNum2 = graphNum2;
	}
	

	@Override
	public void run() {
		LMFinder.extractMatches(matchesForG1, g1, g2, bugName1, bugName2, graphNum1, graphNum2);
	}
	
}
