package edu.vt.cs.prediction.extend;

import java.io.IOException;
import java.nio.file.DirectoryIteratorException;
import java.nio.file.DirectoryStream;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
import java.sql.Connection;
import java.sql.SQLException;
import java.sql.Statement;

import edu.vt.cs.sql.SqliteManager;

public class CommitNameExtraction {
	
	/**
	 * aries, cassandra, lucece, mahout
	 * @param args
	 * @throws SQLException
	 */
	public static void main(String[] args) throws SQLException {
		String project = "mahout";
		
		String folder = "/Users/Vito/Documents/VT/2017spring/SE/ZhongData/" + project + "/" + project;
		String tableName = "prediction_cm_" + project + "_commits";
		
		
		
		Connection conn = SqliteManager.getConnection();
		Statement stmt = conn.createStatement();
		
		stmt.executeUpdate("DROP TABLE IF EXISTS " + tableName);
		stmt.executeUpdate("CREATE TABLE IF NOT EXISTS " + tableName + " (bug_name TEXT)");
		
		Path folderPath = FileSystems.getDefault().getPath(folder);
		try (DirectoryStream<Path> stream = Files.newDirectoryStream(folderPath)) {
		    for (Path file: stream) {
		    	if (Files.isDirectory(file)) {
		    		String commitName = file.getFileName().toString();
		    		if (!commitName.endsWith("internal")) {
		    			stmt.executeUpdate("INSERT INTO " + tableName + " (bug_name) VALUES (\"" + commitName + "\")");
		    			System.out.println(file.getFileName());
		    		}
		    	}
		    }
		} catch (IOException | DirectoryIteratorException x) {
		    // IOException can never be thrown by the iteration.
		    // In this snippet, it can only be thrown by newDirectoryStream.
		    System.err.println(x);
		}
		
		stmt.close();
		conn.close();
	}
	
	/**
	 * find the bug number in the end of a commit name.
	 * E.g., for 123456_DERBY-7890, it returns 7890.
	 * For 987654_DERBY-32_found, it returns 32.
	 * @param commitName full bug name
	 * @return bug number in the end of bug name
	 */
	public static String parseBugNum(String commitName) {
		int dashPos = commitName.indexOf('-');
		int begin = dashPos + 1;
		int end = begin;
		while(end < commitName.length() && Character.isDigit(commitName.charAt(end)))
			end++;
		return commitName.substring(begin, end);
	}
}
