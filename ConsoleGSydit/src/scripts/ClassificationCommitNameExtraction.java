package scripts;

import java.io.IOException;
import java.nio.file.DirectoryIteratorException;
import java.nio.file.DirectoryStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.SQLException;
import java.sql.Statement;

import edu.vt.cs.sql.SqliteManager;

/**
 * 
 * @author Ye Wang
 * @since 02/28/2018
 *
 */
public class ClassificationCommitNameExtraction {
	
	public static void main(String[] args) throws SQLException {
		String[] projects = {"aries", "cassandra", "derby", "mahout"};
		for (String project: projects) {
			execute(project);
		}
	}

	public static void execute(String project) throws SQLException {
		
		String parentFolder = "/Users/Vito/Documents/VT/2018spring/SE/CommitClassification/data/" + project;
		String commitTable = "classify_commits_" + project;
		
		Connection conn = SqliteManager.getConnection();
		Statement stmt = conn.createStatement();
		
		stmt.executeUpdate("DROP TABLE IF EXISTS " + commitTable);
		stmt.executeUpdate("CREATE TABLE IF NOT EXISTS " + commitTable + " (bug_name TEXT, commit_type TEXT)");
		
		PreparedStatement ps = conn.prepareStatement("INSERT INTO " + commitTable + " (bug_name,commit_type) VALUES (?,?)");
		Path folderPath = Paths.get(parentFolder);
		try (DirectoryStream<Path> stream = Files.newDirectoryStream(folderPath)) {
		    for (Path file: stream) {
		    	if (!Files.isDirectory(file)) 
		    		continue;
	    		String commitName = file.getFileName().toString();
	    		if (commitName.endsWith("unknown") || commitName.endsWith("trivalfix"))
	    			continue;
	    		
	    		String commitType = getCommitType(commitName);
	    		if (commitType.equals("null"))
	    			continue;
	    		ps.setString(1, commitName);
	    		ps.setString(2, commitType);
	    		ps.executeUpdate();
    			System.out.println(commitName + "  " + commitType);
		    }
		} catch (IOException | DirectoryIteratorException x) {
		    // IOException can never be thrown by the iteration.
		    // In this snippet, it can only be thrown by newDirectoryStream.
		    System.err.println(x);
		}
		ps.close();
		stmt.close();
		conn.close();
	}
	
	private static String getCommitType(String commitName) {
		int firstUnderscoreIndex = commitName.indexOf('_');
		int secondUnderscoreIndex = commitName.indexOf('_', firstUnderscoreIndex + 1);
		String commitType = commitName.substring(firstUnderscoreIndex + 1, secondUnderscoreIndex);
		return commitType.replace(" ", "");
	}
}
