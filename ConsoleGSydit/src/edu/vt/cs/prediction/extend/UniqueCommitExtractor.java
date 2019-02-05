package edu.vt.cs.prediction.extend;

import java.sql.Connection;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import edu.vt.cs.sql.SqliteManager;

/**
 * 
 * @author Ye Wang
 *
 */
public class UniqueCommitExtractor {
	
	private String project;
	
	private String inputTable;
	
	private String resultTable;
	
	public UniqueCommitExtractor(String project) {
		this.project = project;
		inputTable = "prediction_cm_" + project + "_commits";
		resultTable = "unique_commits_" + project;
	}
	
	private void setUpResultTable() {
		Connection conn = SqliteManager.getConnection();
		try {
			Statement stmt = conn.createStatement();
			stmt.executeUpdate("DROP TABLE IF EXISTS "  + resultTable);
			stmt.executeUpdate("CREATE TABLE IF NOT EXISTS " + resultTable + " (bug_name TEXT)");
			stmt.close();
			conn.close();
		} catch (SQLException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	
	public void execute() {
		setUpResultTable();
		Set<String> bugNumSet = new HashSet<>();
		Connection conn = SqliteManager.getConnection();
		try {
			Statement stmt = conn.createStatement();
			ResultSet rs = stmt.executeQuery("SELECT bug_name FROM " + inputTable);
			List<String> allCommits = new ArrayList<>();
			while (rs.next()) {
				String bugName = rs.getString(1);
				allCommits.add(bugName);
			}
			for (String commitName: allCommits) {
				String bugNum = CommitNameExtraction.parseBugNum(commitName);
				if (!bugNumSet.contains(bugNum)) {
					bugNumSet.add(bugNum);
					stmt.executeUpdate(String.format("INSERT INTO %s (bug_name) VALUES ('%s')", resultTable, commitName));
				}
			}
			stmt.close();
			conn.close();
		} catch (SQLException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	public static void main(String[] args) {
		String[] projects = {"cassandra", "mahout", "aries"};
		for (String project: projects) {
			UniqueCommitExtractor extractor = new UniqueCommitExtractor(project);
			extractor.execute();
		}
		
	}
}
