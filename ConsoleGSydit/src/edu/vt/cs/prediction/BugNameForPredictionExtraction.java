package edu.vt.cs.prediction;

import java.sql.Connection;
import java.sql.SQLException;
import java.sql.Statement;

import edu.vt.cs.sql.SqliteManager;

public class BugNameForPredictionExtraction {
	
	public static void main(String[] args) throws SQLException {
		Connection conn = SqliteManager.getConnection();
		Statement stmt = conn.createStatement();
		stmt.executeUpdate("DROP TABLE IF EXISTS prediction_cm_bug");
		stmt.executeUpdate("CREATE TABLE IF NOT EXISTS prediction_cm_bug (bug_name TEXT)");
		stmt.executeUpdate("INSERT INTO prediction_cm_bug (bug_name) "
				+ "SELECT DISTINCT(bug_name) FROM prediction_cm2 WHERE bug_name IN "
				+ "(SELECT bug_name FROM unique_bug)");
		stmt.close();
		conn.close();
	}
}
