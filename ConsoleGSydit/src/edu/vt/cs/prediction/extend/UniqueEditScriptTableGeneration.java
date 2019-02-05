package edu.vt.cs.prediction.extend;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;

import edu.vt.cs.sql.SqliteManager;

public class UniqueEditScriptTableGeneration {
	
	private String project;
	
	private String commitTable;
	
	private String graphTable;
	
	private String resultTable;
	
	public UniqueEditScriptTableGeneration(String project) {
		this.project = project;
		commitTable = "unique_commits_" + project;
		graphTable = "dp_edit_script_table_" + project;
		resultTable = "edit_script_table_" + project;
	}
	
	public void execute() {
		Connection conn = SqliteManager.getConnection();
		try {
			Statement stmt = conn.createStatement();
			
			stmt.executeUpdate("DROP TABLE IF EXISTS " + resultTable);
			stmt.executeUpdate("CREATE TABLE IF NOT EXISTS " + resultTable 
					+ " (bug_name TEXT,graph_num INTEGER,graph_data TEXT,edit_script TEXT)");
			
			PreparedStatement ps = conn.prepareStatement("INSERT INTO "
					+ resultTable + " (bug_name,graph_num,graph_data,edit_script) VALUES (?,?,?,?)");

			
			ResultSet rs = stmt.executeQuery("SELECT bug_name,graph_num,graph_data,edit_script FROM " + graphTable);
			while (rs.next()) {
				String bugName = rs.getString(1);
				int graphNum = rs.getInt(2);
				String graphData = rs.getString(3);
				String editScript = rs.getString(4);
				
			    Statement stmt2 = conn.createStatement();
			    ResultSet rs2 = stmt2.executeQuery(String.format("SELECT COUNT(*) FROM %s WHERE bug_name='%s'", commitTable, bugName));
				rs2.next();
				if (rs2.getInt(1) > 0) {
//					stmt2.executeUpdate("");
					ps.setString(1, bugName);
					ps.setInt(2, graphNum);
					ps.setString(3, graphData);
					ps.setString(4, editScript);
					ps.executeUpdate();
				}
				stmt2.close();
				
				
			}
			ps.close();
			stmt.close();
			conn.close();
			
		} catch (SQLException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	public static void main(String[] args) {
		String[] projects = {"aries", "cassandra", "mahout"};
		for (String project: projects) {
			UniqueEditScriptTableGeneration generation = new UniqueEditScriptTableGeneration(project);
			generation.execute();
		}
	}
}
