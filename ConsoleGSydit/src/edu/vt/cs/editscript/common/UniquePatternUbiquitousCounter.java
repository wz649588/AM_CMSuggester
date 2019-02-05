package edu.vt.cs.editscript.common;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;

import org.jgrapht.Graph;

import edu.vt.cs.editscript.json.GraphDataJson.GraphEdge;
import edu.vt.cs.editscript.json.GraphDataJson.GraphNode;
import edu.vt.cs.sql.SqliteManager;

public class UniquePatternUbiquitousCounter {

	private String resultTable = "ubiquitous_pattern";
	
	private String uniquePatternTable = "unique_pattern_over_all_projects";
	
	private String[] patternTables = {"aries_largest_match_pattern",
			"cassandra_largest_match_pattern",
			"derby_largest_match_pattern",
			"mahout_largest_match_pattern"};
	
	public void execute() {
		Connection conn = SqliteManager.getConnection();
		try {
			Statement stmt = conn.createStatement();
			stmt.executeUpdate("DROP TABLE IF EXISTS " + resultTable);
			stmt.executeUpdate("CREATE TABLE IF NOT EXISTS "  + resultTable + " (shape TEXT)");
			
			ResultSet rs = stmt.executeQuery("SELECT shape FROM " + uniquePatternTable);
			
			
			while (rs.next()) {
				String uniqueShapeJson = rs.getString(1);
				Graph<GraphNode, GraphEdge> uniqueShape = UniquePatternCounter.getGraphFromJson(uniqueShapeJson);
				
				Statement stmt2 = conn.createStatement();
				boolean patternExistsInAllTables = true;
				for (String patternTable: patternTables) {
					ResultSet rs2 = stmt2.executeQuery("SELECT shape FROM " + patternTable);
					boolean patternExistsInCurrentTable = false; 
					while (rs2.next()) {
						String shapeJson = rs2.getString(1);
						Graph<GraphNode, GraphEdge> shape = UniquePatternCounter.getGraphFromJson(shapeJson);
						if (LargestMatchPatternExtraction.isGraphASubgraphOfGraphB(uniqueShape, shape)
								&& LargestMatchPatternExtraction.isGraphASubgraphOfGraphB(shape, uniqueShape)) {
							patternExistsInCurrentTable = true;
							break;
						}
					}
					if (!patternExistsInCurrentTable) {
						patternExistsInAllTables = false;
						break;
					}
				}
				stmt2.close();
				
				if (patternExistsInAllTables) {
					PreparedStatement ps = conn.prepareStatement("INSERT INTO " + resultTable + " (shape) VALUES (?)");
					ps.setString(1, uniqueShapeJson);
					ps.executeUpdate();
					ps.close();
				}
			}
			
			rs = stmt.executeQuery("SELECT COUNT(*) FROM " + resultTable);
			System.out.println(rs.getInt(1));
			
			stmt.close();
			conn.close();
			
		} catch (SQLException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	
	public static void main(String[] args) {
		UniquePatternUbiquitousCounter counter = new UniquePatternUbiquitousCounter();
		counter.execute();
	}
}
