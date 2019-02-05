package edu.vt.cs.editscript.common;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.ArrayList;
import java.util.List;

import org.jgrapht.Graph;

import com.google.gson.Gson;

import edu.vt.cs.editscript.json.GraphDataJson;
import edu.vt.cs.editscript.json.GraphDataJson.GraphEdge;
import edu.vt.cs.editscript.json.GraphDataJson.GraphNode;
import edu.vt.cs.sql.SqliteManager;

/**
 * Get the number of the unique common patterns over all four projects.
 * @author Ye Wang
 * @since 08/29/2017
 */
public class UniquePatternCounter {
	
	private String[] patternTables = {"aries_largest_match_pattern",
			"cassandra_largest_match_pattern",
			"derby_largest_match_pattern",
			"mahout_largest_match_pattern"};
	
	private String resultTable = "unique_pattern_over_all_projects";
	
	private static Gson gson = new Gson();
	
	private List<Graph<GraphNode, GraphEdge>> uniquePatterns = new ArrayList<>();
	
	public UniquePatternCounter() {
		
	}
	
	private void addPattern(Graph<GraphNode, GraphEdge> added) {
		Connection conn = SqliteManager.getConnection();
		try {
			Statement stmt = conn.createStatement();
			ResultSet rs = stmt.executeQuery("SELECT shape FROM " + resultTable);
			boolean shapeAlreadyExists = false;
			while (rs.next()) {
				String shapeJson = rs.getString(1);
				Graph<GraphNode, GraphEdge> shape = getGraphFromJson(shapeJson);
				if (LargestMatchPatternExtraction.isGraphASubgraphOfGraphB(added, shape)
						&& LargestMatchPatternExtraction.isGraphASubgraphOfGraphB(shape, added)) {
					shapeAlreadyExists = true;
					break;
				}
			}
			
			if (!shapeAlreadyExists) {
				PreparedStatement ps = conn.prepareStatement("INSERT INTO " + resultTable + " (shape) VALUES (?)");
				ps.setString(1, GraphDataJson.convert(added).toJson());
				ps.executeUpdate();
			}
			
			stmt.close();
			conn.close();
			
		} catch (SQLException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	
	public static Graph<GraphNode, GraphEdge> getGraphFromJson(String json) {
		return gson.fromJson(json, GraphDataJson.class).getJgrapht();
	}
	
	private void processTable(String tableName) {
		Connection conn = SqliteManager.getConnection();
		try {
			Statement stmt = conn.createStatement();
			ResultSet rs = stmt.executeQuery("SELECT COUNT(*) FROM " + tableName);
			rs.next();
			int totalNum = rs.getInt(1);
			stmt.close();
			conn.close();
			
			for (int offset = 0; offset < totalNum; offset++) {
//				System.out.println(offset);
				conn = SqliteManager.getConnection();
				stmt = conn.createStatement();
				rs = stmt.executeQuery("SELECT shape FROM " + tableName + " LIMIT 1 OFFSET " + offset);
				rs.next();
				String shapeJson = rs.getString(1);
				stmt.close();
				conn.close();
				
				Graph<GraphNode, GraphEdge> shape = getGraphFromJson(shapeJson);
				addPattern(shape);
			}
			
			
			
			
		} catch (SQLException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	
	private void setUpResultTable() {
		Connection conn = SqliteManager.getConnection();
		try {
			Statement stmt = conn.createStatement();
			stmt.executeUpdate("DROP TABLE IF EXISTS " + resultTable);
			stmt.executeUpdate("CREATE TABLE IF NOT EXISTS " + resultTable
					+ " (shape TEXT)");
			stmt.close();
			conn.close();
		} catch (SQLException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
	}
	
	public void execute() {
		setUpResultTable();
		for (String table: patternTables) {
//			System.out.println(table);
			processTable(table);
		}
		
		Connection conn = SqliteManager.getConnection();
		Statement stmt;
		try {
			stmt = conn.createStatement();
			ResultSet rs = stmt.executeQuery("SELECT COUNT(*) FROM " + resultTable);
			System.out.println(rs.getInt(1));
			stmt.close();
			conn.close();
		} catch (SQLException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
	}

	public static void main(String[] args) {
		UniquePatternCounter counter = new UniquePatternCounter();
		counter.execute();
	}
}
