package scripts;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import edu.vt.cs.sql.SqliteManager;

/**
 * This class is only for one-time use. It extracts the commit
 * whose category is bug, new feature, or improvement. Also,
 * it eliminate the duplicate commits for the same issue.
 * @author Ye Wang
 * @since 06/26/2018
 */
public class UniqueClassificationCommitExtraction {

	public UniqueClassificationCommitExtraction() {
		
	}
	
	private String getIssueID(String commitName) {
		int dashPos = commitName.indexOf('-');
		int begin = dashPos + 1;
		int end = begin;
		while(end < commitName.length() && Character.isDigit(commitName.charAt(end)))
			end++;
		return commitName.substring(begin, end);
	}
	
	private String getIssueType(String commitName) {
		int firstUnderscoreIndex = commitName.indexOf('_');
		int secondUnderscoreIndex = commitName.indexOf('_', firstUnderscoreIndex + 1);
		String commitType = commitName.substring(firstUnderscoreIndex + 1, secondUnderscoreIndex);
		return commitType.replace(" ", "");
	}
	
	public void execute(String project) throws SQLException {
		Connection conn = SqliteManager.getConnection();
		Statement stmt = conn.createStatement();
		
		String outputTable = "classify_commits_u_" + project;
		stmt.executeUpdate("DROP TABLE IF EXISTS " + outputTable);
		stmt.executeUpdate("CREATE TABLE " + outputTable + " (bug_name TEXT, commit_type TEXT)");
		
		String graphTable = "classify_graph_" + project;
		ResultSet rs = stmt.executeQuery("SELECT DISTINCT bug_name FROM " + graphTable);
		List<String> uniqueCommits = new ArrayList<>();
		Set<String> issueSet = new HashSet<>();
		while (rs.next()) {
			String bugName = rs.getString(1);
			String issue = getIssueID(bugName);
			if (!issueSet.contains(issue)) {
				uniqueCommits.add(bugName);
				issueSet.add(issue);
			}
		}
		rs.close();
		stmt.close();
		List<String> classificationCommits = new ArrayList<>();
		for (String commit: uniqueCommits) {
			String type = getIssueType(commit);
			if (type.equals("Bug") || type.equals("NewFeature") || type.equals("Improvement")) {
				classificationCommits.add(commit);
			}
		}
		PreparedStatement ps = conn.prepareStatement("INSERT INTO " + outputTable
				+ "(bug_name,commit_type) VALUES (?,?)");
		for (String commit: classificationCommits) {
			String type = getIssueType(commit);
			ps.setString(1, commit);
			ps.setString(2, type);
			ps.executeUpdate();
		}
		ps.close();
		conn.close();
		System.out.println(project + ": " + classificationCommits.size());
	}
	
	
	
	public static void main(String[] args) throws SQLException {
		String[] projects = {"aries", "cassandra", "derby", "mahout"};
		for (String project: projects) {
			UniqueClassificationCommitExtraction extraction = new UniqueClassificationCommitExtraction();
			extraction.execute(project);
		}
		
	}
}
