package edu.vt.cs.classify.stat;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;

import org.jgrapht.Graph;

import com.google.gson.Gson;

import edu.vt.cs.editscript.json.GraphDataWithNodesJson;
import edu.vt.cs.editscript.json.GraphDataJson.GraphEdge;
import edu.vt.cs.editscript.json.GraphDataJson.GraphNode;
import edu.vt.cs.graph.ReferenceEdge;
import edu.vt.cs.graph.ReferenceNode;
import edu.vt.cs.sql.SqliteManager;

/**
 * Count the numbers of different types of nodes and edges for each graph
 * @author Ye Wang
 * @since 03/04/2018
 *
 */
public class NodeEdgeCounter {
	
	private String graphTable = "classification_initial_graph_aries";
	
	private String resultTable = "classification_initial_graph_nodes_edges";
	
	public NodeEdgeCounter() {
		
	}
	
	public void execute() throws SQLException {
		Connection conn = SqliteManager.getConnection();
		Statement stmt = conn.createStatement();
		
		stmt.executeUpdate("DROP TABLE IF EXISTS " + resultTable);
		stmt.executeUpdate("CREATE TABLE " + resultTable
				+ " (commit_type TEXT,bug_name TEXT,graph_num INTEGER,"
				+ "cm INTEGER,am INTEGER,dm INTEGER,"
				+ "af INTEGER,df INTEGER,cf INTEGER,"
				+ "fa INTEGER,mi INTEGER,mo INTEGER)");

		ResultSet rs = stmt.executeQuery("SELECT COUNT(*) FROM " + graphTable);
		rs.next();
		int totalNum = rs.getInt(1);
		
		
		Gson gson = new Gson();
		
		PreparedStatement ps = conn.prepareStatement("INSERT INTO " + resultTable
				+ " (commit_type,bug_name,graph_num,cm,am,dm,af,df,cf,fa,mi,mo)"
				+ " VALUES (?,?,?,?,?,?,?,?,?,?,?,?)");
		for (int offset = 0; offset < totalNum; offset++) {
			System.out.println(offset + 1 + "/" + totalNum);
			rs = stmt.executeQuery("SELECT commit_type,bug_name,graph_num,graph_data FROM " + graphTable + " LIMIT 1 OFFSET " + offset);
			rs.next();
			String commitType = rs.getString(1);
			String bugName = rs.getString(2);
			int graphNum = rs.getInt(3);
			String graphData = rs.getString(4);
			
			// parse the graph data
			GraphDataWithNodesJson graphDataWithNodesJson = gson.fromJson(graphData, GraphDataWithNodesJson.class);
			Graph<GraphNode, GraphEdge> graph = graphDataWithNodesJson.getJgrapht();
			
			// count number
			int cmCount = 0;
			int amCount = 0;
			int dmCount = 0;
			int afCount = 0;
			int dfCount = 0;
			int cfCount = 0;
			for (GraphNode n: graph.vertexSet()) {
				int typeInt = n.getType();
				String nodeType = ReferenceNode.getTypeString(typeInt);
				switch (nodeType) {
				case "CM":
					cmCount++;
					break;
				case "AM":
					amCount++;
					break;
				case "DM":
					dmCount++;
					break;
				case "AF":
					afCount++;
					break;
				case "DF":
					dfCount++;
					break;
				case "CF":
					cfCount++;
					break;
				}
			}
			int fieldAccessCount = 0;
			int methodInvokeCount = 0;
			int methodOverrideCount = 0;
			for (GraphEdge e: graph.edgeSet()) {
				int typeInt = e.getType();
				String edgeType = ReferenceEdge.getTypeString(typeInt);
				switch (edgeType) {
				case "FIELD_ACCESS":
					fieldAccessCount++;
					break;
				case "METHOD_INVOKE":
					methodInvokeCount++;
					break;
				case "METHOD_OVERRIDE":
					methodOverrideCount++;
					break;
				}
			}
			
			
			ps.setString(1, commitType);
			ps.setString(2, bugName);
			ps.setInt(3, graphNum);
			ps.setInt(4, cmCount);
			ps.setInt(5, amCount);
			ps.setInt(6, dmCount);
			ps.setInt(7, afCount);
			ps.setInt(8, dfCount);
			ps.setInt(9, cfCount);
			ps.setInt(10, fieldAccessCount);
			ps.setInt(11, methodInvokeCount);
			ps.setInt(12, methodOverrideCount);
			ps.executeUpdate();
		}
		

		ps.close();
		stmt.close();
		conn.close();
	}

	public static void main(String[] args) throws SQLException {
		NodeEdgeCounter counter = new NodeEdgeCounter();
		counter.execute();
	}
}
