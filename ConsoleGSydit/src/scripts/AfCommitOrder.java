package scripts;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.ArrayList;
import java.util.List;

import edu.vt.cs.sql.SqliteManager;

/**
 * To consider the temporal order of the 
 * @author Ye Wang
 * @since 07/08/2018
 *
 */
public class AfCommitOrder {
	
//	private static String command = "git --git-dir=/Users/Vito/git/aries/.git show -s --format=%ct 13e8e0f";
	
	private String project;
	
	private String gitRepo;
	
	public AfCommitOrder(String project) {
		this.project = project;
		this.gitRepo = getGitRepoPath(project);
	}
	
	private final static String getGitRepoPath(String project) {
		String path = null;
		switch (project) {
		case "aries":
			path = "/Users/zijianjiang/Documents/NaM/git/aries/.git";
			break;
		case "cassandra":
			path = "/Users/zijianjiang/Documents/NaM/git/cassandra/.git";
			break;
		case "mahout":
			path = "/Users/zijianjiang/Documents/NaM/git/mahout/.git";
			break;
		case "activemq":
			path = "/Users/zijianjiang/Documents/NaM/git/activemq/.git";
			break;
		case "uima":
			path = "/Users/zijianjiang/Documents/NaM/git/uima/.git";
			break;
		}
		return path;
	}
	
	private int getTimestamp(String commitHash) {
		String commandTemplate = "git --git-dir=%s show -s --format=%%ct %s";
		String command = String.format(commandTemplate, gitRepo, commitHash);
		Process p = null;
		try {
			p = Runtime.getRuntime().exec(command);
		} catch (IOException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}
		try {
			p.waitFor();
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
        BufferedReader stdInput = new BufferedReader(new InputStreamReader(
                p.getInputStream()));
        String output = null;
		try {
			output = stdInput.readLine();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		int timestamp = -1;
		try {
			timestamp = Integer.parseInt(output);
		} catch (NumberFormatException e) {
			e.printStackTrace();
		}
        return timestamp;
	}
	
	public void exec() throws SQLException {
		if (project.equals("derby")) {
			processDerby();
			return;
		}
		
		Connection conn = SqliteManager.getConnection();
		Statement stmt = conn.createStatement();
		
		String inputTable = "unique_commits_" + project;
		String outputTable = "af_commit_order_" + project;
		
		stmt.executeUpdate("DROP TABLE IF EXISTS " + outputTable);
		stmt.executeUpdate("CREATE TABLE " + outputTable + " (bug_name TEXT, ordering INTEGER)");
		
		ResultSet rs = stmt.executeQuery("SELECT bug_name FROM " + inputTable);
		List<String> commitNames = new ArrayList<>();
		while (rs.next()) {
			String commitName = rs.getString(1);
			commitNames.add(commitName);
		}
		rs.close();
		stmt.close();
		
		PreparedStatement ps = conn.prepareStatement("INSERT INTO "
				+ outputTable + " (bug_name,ordering) VALUES (?,?)");
		for (String commitName: commitNames) {
			int end = 0;
			while (end < commitName.length() && commitName.charAt(end) != '_')
				end++;
			String hash = commitName.substring(0, end);
			int order = getTimestamp(hash);
			System.out.println(commitName + ", " + order);
			if (order != -1) {
				ps.setString(1, commitName);
				ps.setInt(2, order);
				ps.executeUpdate();
			}
		}
		ps.close();
		
		
	}
	
	private void processDerby() throws SQLException {
		Connection conn = SqliteManager.getConnection();
		Statement stmt = conn.createStatement();
		
		String outputTable = "af_commit_order_derby";
		stmt.executeUpdate("DROP TABLE IF EXISTS " + outputTable);
		stmt.executeUpdate("CREATE TABLE " + outputTable + " (bug_name TEXT, ordering INTEGER)");
		
		String inputTable = "unique_bug";
		ResultSet rs = stmt.executeQuery("SELECT bug_name FROM " + inputTable);
		List<String> commitNames = new ArrayList<>();
		while (rs.next()) {
			String commitName = rs.getString(1);
			commitNames.add(commitName);
		}
		rs.close();
		stmt.close();
		
		PreparedStatement ps = conn.prepareStatement("INSERT INTO "
				+ outputTable + " (bug_name,ordering) VALUES (?,?)");
		//  Get SVN ID
		for (String commitName: commitNames) {
			int order = getDerbyOrder(commitName);
			System.out.println(commitName + ", " + order);
			ps.setString(1, commitName);
			ps.setInt(2, order);
			ps.executeUpdate();
		}
		ps.close();
		
	}
	
	private int getDerbyOrder(String commitName) {
		int end = 0;
		while (end < commitName.length() && Character.isDigit(commitName.charAt(end)))
			end++;
		String orderString = commitName.substring(0, end);
		return Integer.parseInt(orderString);
	}

	public static void main(String[] args) throws SQLException {
		String[] projects = {"activemq","uima"};
		for (String project: projects) {
			AfCommitOrder order = new AfCommitOrder(project);
			order.exec();
		}
	}
	
	public static void main1(String[] args) throws IOException {
		// This is a test
		String command = "git --git-dir=/Users/Vito/git/aries/.git show -s --format=%ct 0084a90";
		Process p = Runtime.getRuntime().exec(command);
		try {
			p.waitFor();
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
        BufferedReader stdInput = new BufferedReader(new InputStreamReader(
                p.getInputStream()));
        String output = stdInput.readLine();
        int timestamp = Integer.parseInt(output);
        System.out.println(timestamp);
        
	}

}
