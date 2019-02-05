package edu.vt.cs.editscript.common;

import java.lang.reflect.Type;
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
import org.jgrapht.alg.isomorphism.VF2SubgraphIsomorphismInspector;
import org.jgrapht.graph.DefaultDirectedGraph;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.reflect.TypeToken;

import edu.vt.cs.editscript.json.EditScriptJson;
import edu.vt.cs.editscript.json.EditScriptJson.EditOperationJson;
import edu.vt.cs.editscript.json.GraphDataJson;
import edu.vt.cs.editscript.json.GraphDataJson.GraphEdge;
import edu.vt.cs.editscript.json.GraphDataJson.GraphNode;
import edu.vt.cs.editscript.json.ScriptEdge;
import edu.vt.cs.editscript.json.ScriptNode;
import edu.vt.cs.graph.ReferenceEdge;
import edu.vt.cs.graph.ReferenceNode;
import edu.vt.cs.sql.SqliteManager;

/**
 * Find the common edit scripts between two graphs
 * @author Ye Wang
 * @since 03/26/2017
 *
 */
public class CommonScriptFinder {
	
	private Comparator<GraphNode> graphNodeComparator;
	private Comparator<GraphEdge> graphEdgeComparator;
	
	private Comparator<ScriptNode> scriptNodeComparator;
	private Comparator<ScriptEdge> scriptEdgeComparator;
	
	private Gson fGson;
	
	static boolean executeFromBeginning = true;

	public static void main(String[] args) throws SQLException {
		if (executeFromBeginning) {
			Connection connection = SqliteManager.getConnection();
			Statement statement = connection.createStatement();
			statement.executeUpdate("DROP TABLE IF EXISTS edit_script_mapping");
			connection.close();
		}
		
		
		
		// create a table in database
		Connection connection = SqliteManager.getConnection();
		Statement statement = connection.createStatement();
		statement.executeUpdate("CREATE TABLE IF NOT EXISTS edit_script_mapping (bn1 TEXT, gn1 INTEGER, bn2 TEXT, gn2 INTEGER, mapping_num INTEGER, subgraph1 TEXT, subgraph2 TEXT, node_map TEXT, edge_map TEXT)");
		
		//*****DEBUG******
//		statement.executeUpdate("CREATE TABLE IF NOT EXISTS temp_mapping_amount (i INTEGER, j INTEGER, mapping_amount INTEGER)");
//		statement.executeUpdate("CREATE TABLE IF NOT EXISTS temp_isomorphism (mapping_num INTEGER, sg1 TEXT, sg2 TEXT, node_map TEXT, edge_map TEXT)");
		//****************
		
		connection.close();
		
		Type nodeMapType = new TypeToken<HashMap<ScriptNode, ScriptNode>>(){}.getType();
		Type edgeMapType = new TypeToken<HashMap<ScriptEdge, ScriptEdge>>(){}.getType();
		
		// compare every pair of graphs
		CommonScriptFinder finder = new CommonScriptFinder();
		List<GraphIndex> graphIndices = finder.getAllGraphs();
//		graphIndices = graphIndices.subList(0, 5);
		for (int i = 0; i < graphIndices.size() - 1; i++) {
			
			//*****DEBUG******
//			i = 466;
			System.out.println("i=" + i);
			//****************
			
			GraphScriptData data1 = finder.getGraphScriptData(graphIndices.get(i));
			GraphDataJson graphDataJson1 = data1.getGraphData();
			Graph<GraphNode, GraphEdge> g1 = graphDataJson1.getJgrapht();
			EditScriptJson editScriptJson1 = data1.getEditScript();
			Graph<ScriptNode, ScriptEdge> scriptGraph1 = GraphBuilder.create(g1, editScriptJson1);
			
//			System.out.println(data1.getBugName() + ", " + data1.getGraphNum());
			
			
			
			for (int j = i + 1; j < graphIndices.size(); j++) {
				
				//*****DEBUG******
//				j = 43;
//				System.out.println("j=" + j);
				//****************
				
				
				GraphScriptData data2 = finder.getGraphScriptData(graphIndices.get(j));
				GraphDataJson graphDataJson2 = data2.getGraphData();
				Graph<GraphNode, GraphEdge> g2 = graphDataJson2.getJgrapht();
				EditScriptJson editScriptJson2 = data2.getEditScript();
				Graph<ScriptNode, ScriptEdge> scriptGraph2 = GraphBuilder.create(g2, editScriptJson2);
				
//				System.out.println(data2.getBugName() + ", " + data2.getGraphNum());
				
				VF2SubgraphIsomorphismInspector<ScriptNode, ScriptEdge> isoInspector =
						new VF2SubgraphIsomorphismInspector<>(scriptGraph1, scriptGraph2, finder.scriptNodeComparator, finder.scriptEdgeComparator);
				Iterator<GraphMapping<ScriptNode, ScriptEdge>> isoIterator = isoInspector.getMappings();
				
				int mappingNum = 0;
				
				
				final Iterator<GraphMapping<ScriptNode, ScriptEdge>> finalIsoIterator = isoIterator;
				Runnable task = new Runnable() {
					@Override
					public void run() {
						finalIsoIterator.hasNext();
					}
				};
				ExecutorService executorService = Executors.newSingleThreadExecutor();
				Future<?> future = executorService.submit(task);
				boolean isoIteratorTimeOut = false;
				try {
					future.get(5, TimeUnit.SECONDS);
				} catch (InterruptedException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				} catch (ExecutionException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				} catch (TimeoutException e) {
					// TODO Auto-generated catch block
//					e.printStackTrace();
					future.cancel(true);
					isoIteratorTimeOut = true;
				} finally {
					executorService.shutdown();
				}
				
				if (isoIteratorTimeOut)
					continue;
				
				
				
				while (isoIterator.hasNext()) {
					
					// avoid too many mappings
					if (mappingNum > 1000)
						break;
//					System.out.println("mapping="+mappingNum);
					
					GraphMapping<ScriptNode, ScriptEdge> mapping = isoIterator.next();

					
					// find subgraphs through mappings, and export subgraphs
					Graph<ScriptNode, ScriptEdge> subgraph1 = new DefaultDirectedGraph<ScriptNode, ScriptEdge>(ScriptEdge.class);
					Graph<ScriptNode, ScriptEdge> subgraph2 = new DefaultDirectedGraph<ScriptNode, ScriptEdge>(ScriptEdge.class);
					boolean editScriptsMatch = true;
//					List<List<EditOperationJson>> lcsList = new ArrayList<>();
					
					
					Map<ScriptNode, ScriptNode> nodeMap = new HashMap<>();
					Map<ScriptEdge, ScriptEdge> edgeMap = new HashMap<>();
					
					
					for (ScriptNode vertexInG1: scriptGraph1.vertexSet()) {
						ScriptNode vertexInG2 = mapping.getVertexCorrespondence(vertexInG1, true);
						if (vertexInG2 != null) {
							
							nodeMap.put(vertexInG1, vertexInG2);
							
							subgraph1.addVertex(vertexInG1);
							subgraph2.addVertex(vertexInG2);
//							
//							List<EditOperationJson> script1 = null;
//							List<EditOperationJson> script2 = null;
//							// in the common subgraph, compare the edit script of each node, if the edit script is available
//							if (vertexInG1.getType() == ReferenceNode.DM || vertexInG1.getType() == ReferenceNode.CM) {
//								script1 = editScriptJson1.getOldScript(vertexInG1.getName());
//							} else if (vertexInG1.getType() == ReferenceNode.AM) {
//								script1 = editScriptJson1.getNewScript(vertexInG1.getName());
//							}
//							if (vertexInG2.getType() == ReferenceNode.DM || vertexInG2.getType() == ReferenceNode.CM) {
//								script2 = editScriptJson2.getOldScript(vertexInG2.getName());
//							} else if (vertexInG2.getType() == ReferenceNode.AM) {
//								script2 = editScriptJson2.getNewScript(vertexInG2.getName());
//							}
//							List<EditOperationJson> lcs = null;
//							if (script1 != null && script2 != null) {
//								lcs = CommonScriptFinder.extractLcs(script1, script2);
//								lcsList.add(lcs);
//							}
//							if (editScriptsMatch) {
//								if (lcs == null)
//									editScriptsMatch = false;
//								else if (script1.isEmpty() || script2.isEmpty())
//									editScriptsMatch = false;
//								else if (lcs.size() * 2 <= script1.size() || lcs.size() * 2 <= script2.size())
//									editScriptsMatch = false;
//							}
						}
					}
					for (ScriptEdge edgeInG1: scriptGraph1.edgeSet()) {
						ScriptEdge edgeInG2 = mapping.getEdgeCorrespondence(edgeInG1, true);
						if (edgeInG2 != null) {
							
							edgeMap.put(edgeInG1, edgeInG2);
							
							subgraph1.addEdge(edgeInG1.getSrc(), edgeInG1.getDst(), edgeInG1);
							subgraph2.addEdge(edgeInG2.getSrc(), edgeInG2.getDst(), edgeInG2);
						}
					}
					
					
					if (editScriptsMatch) {
						Gson gson = finder.getGson();
						Connection connection2 = SqliteManager.getConnection();
						String sql = "INSERT INTO edit_script_mapping (bn1, gn1, bn2, gn2, mapping_num, subgraph1, subgraph2, node_map, edge_map) VALUES (?,?,?,?,?,?,?,?,?)";
						PreparedStatement stmt = connection2.prepareStatement(sql);
						stmt.setString(1, data1.getBugName());
						stmt.setInt(2, data1.getGraphNum());
						stmt.setString(3, data2.getBugName());
						stmt.setInt(4, data2.getGraphNum());
						stmt.setInt(5, mappingNum);
						stmt.setString(6, gson.toJson(convertToScriptEdges(subgraph1))); // subgraph1
						stmt.setString(7, gson.toJson(convertToScriptEdges(subgraph2))); // subgraph2
						stmt.setString(8, gson.toJson(nodeMap, nodeMapType));
						stmt.setString(9, gson.toJson(edgeMap, edgeMapType));
//						stmt.setString(10, gson.toJson(lcsList)); // lcs
						
						stmt.executeUpdate();
						connection.close();
					}
					
					mappingNum++;
				} // while
				
				
			} // for j
		} // for i
		
		System.out.println("Oh Ye!");
	}
	
	
	public CommonScriptFinder() {
		graphNodeComparator = new Comparator<GraphNode>() {
			@Override
			public int compare(GraphNode n1, GraphNode n2) {
				return n1.getType() - n2.getType();
			}
		};
		graphEdgeComparator = new Comparator<GraphEdge>() {
			@Override
			public int compare(GraphEdge e1, GraphEdge e2) {
				return e1.getType() - e2.getType();
			}
		};
		
		scriptNodeComparator = new Comparator<ScriptNode>() {
			@Override
			public int compare(ScriptNode n1, ScriptNode n2) {
				
				if (n1.getType() != n2.getType())
					return -1;
				
				int type = n1.getType();
				if (type == ReferenceNode.CM || type == ReferenceNode.AM || type == ReferenceNode.DM) {
					// Compare edit script
					List<EditOperationJson> script1 = n1.getScript();
					List<EditOperationJson> script2 = n2.getScript();
					if (script1 == null && script2 == null)
						return 0;
					else if (script1 == null)
						return -1;
					else if (script2 == null)
						return -1;
					else if (script1.isEmpty() || script2.isEmpty())
						return -1;
					else {
						// Both scripts are not null and not empty
						List<EditOperationJson> lcs = CommonScriptFinder.extractLcs(script1, script2);
						if (lcs.size() * 2 > script1.size() && lcs.size() * 2 > script2.size())
							return 0;
						else
							return -1;
					}
				} else {
					// type is AF or DF
					return 0;
				}
			}
		};
		scriptEdgeComparator = new Comparator<ScriptEdge>() {
			@Override
			public int compare(ScriptEdge e1, ScriptEdge e2) {
				return e1.getType() - e2.getType();
			}
		};
		
		fGson = new GsonBuilder().enableComplexMapKeySerialization().create();
	}
	
	public static List<ScriptEdge> convertToScriptEdges(Graph<ScriptNode, ScriptEdge> g) {
		List<ScriptEdge> edges = new ArrayList<>();
		edges.addAll(g.edgeSet());
		return edges;
	}
	
	public Gson getGson() {
		return fGson;
	}
	
	// Longest common subsequence
	private static List<EditOperationJson> extractLcs(List<EditOperationJson> s1, List<EditOperationJson> s2) {
		LongestCommonSubseq<EditOperationJson> lcs = new LongestCommonSubseq<>(s1, s2);
		return lcs.getResultList();
	}
	
	private GraphScriptData getGraphScriptData(GraphIndex index) throws SQLException {
		Connection connection = SqliteManager.getConnection();
		
		String sql = "SELECT graph_data, edit_script FROM edit_script_table WHERE bug_name=? AND graph_num=?";
		PreparedStatement stmt = connection.prepareStatement(sql);
		
		String bugName = index.getBugName();
		int graphNum = index.getGraphNum();
		
		stmt.setString(1, bugName);
		stmt.setInt(2, graphNum);
		ResultSet rs = stmt.executeQuery();
		String graphDataString = rs.getString(1);
		String editScriptString = rs.getString(2);
		connection.close();
		
		return new GraphScriptData(bugName, graphNum, graphDataString, editScriptString);
	}
	
	private class GraphScriptData {
		private String bugName;
		private int graphNum;
		
		private GraphDataJson graphData;
		private EditScriptJson editScript;
		
		
		GraphScriptData(String bugName, int graphNum, String graphDataString, String editScriptString) {
			this.bugName = bugName;
			this.graphNum = graphNum;
			Gson gson = new Gson();
			this.editScript = gson.fromJson(editScriptString, EditScriptJson.class);
			this.graphData = gson.fromJson(graphDataString, GraphDataJson.class);
		}
		
		String getBugName() {
			return bugName;
		}
		
		int getGraphNum() {
			return graphNum;
		}
		
		GraphDataJson getGraphData() {
			return graphData;
		}
		
		EditScriptJson getEditScript() {
			return editScript;
		}
	}
	
	private List<GraphIndex> getAllGraphs() throws SQLException {
		Connection connection = SqliteManager.getConnection();
		Statement statement = connection.createStatement();
		
		List<GraphIndex> graphIndices = new ArrayList<>();
		ResultSet rs = statement.executeQuery("SELECT bug_name, graph_num FROM edit_script_table WHERE bug_name IN (SELECT bug_name FROM unique_bug)");
		while (rs.next()) {
			String bugName = rs.getString(1);
			int graphNum = rs.getInt(2);
			graphIndices.add(new GraphIndex(bugName, graphNum));
		}
		
		connection.close();
		return graphIndices;
		
	}
	
	private class GraphIndex {
		private String bugName;
		private int graphNum;
		
		GraphIndex(String bugName, int graphNum) {
			this.bugName = bugName;
			this.graphNum = graphNum;
		}
		
		String getBugName() {
			return bugName;
		}
		
		int getGraphNum() {
			return graphNum;
		}
	}

}
