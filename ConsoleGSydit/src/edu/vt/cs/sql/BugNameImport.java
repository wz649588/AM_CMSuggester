package edu.vt.cs.sql;

import java.io.IOException;
import java.nio.file.FileSystems;
import java.nio.file.Path;
import java.sql.Connection;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.Scanner;

public class BugNameImport {
	
	/**
	 * Import bug name from file to SQLite database
	 * @param args
	 * @throws IOException 
	 * @throws SQLException 
	 */
	public static void main(String[] args) throws IOException, SQLException {
		String bugNameFile = "/Users/zijianjiang/Documents/NaM/pattern-finder/grapa/bugNames2.txt";
		Path bugNamePath = FileSystems.getDefault().getPath(bugNameFile);
		Scanner bugScanner = new Scanner(bugNamePath);
		
		Connection connection = SqliteManager.getConnection();
		Statement statement = connection.createStatement();
		
		String sql1 = "CREATE TABLE IF NOT EXISTS bug (name TEXT PRIMARY KEY)";
		statement.executeUpdate(sql1);
		
		while (bugScanner.hasNextLine()) {
			String line = bugScanner.nextLine();
			String bugName = line.trim();
			String sql2 = String.format("INSERT INTO bug VALUES (\"%s\")", bugName);
			statement.executeUpdate(sql2);
		}
		
		String sql3 = "DELETE FROM bug WHERE name=\"329187_DERBY-330\"";
		statement.executeUpdate(sql3);
		
		bugScanner.close();
		connection.close();
	}
}
