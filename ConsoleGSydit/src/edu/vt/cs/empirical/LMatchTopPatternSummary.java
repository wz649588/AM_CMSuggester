package edu.vt.cs.empirical;

import java.io.IOException;
import java.nio.file.DirectoryIteratorException;
import java.nio.file.DirectoryStream;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.sql.Connection;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;

import edu.vt.cs.sql.SqliteManager;

public class LMatchTopPatternSummary {
	
	private String project;
	
	private String picFolder;
	
	private static String outputFolder = "/Users/Vito/Documents/VT/2018spring/SE/characterization/patterns/top-pattern";
	
	public LMatchTopPatternSummary(String project) {
		this.project = project;
		picFolder = "/Users/Vito/Documents/VT/2018spring/SE/characterization/patterns/largestPatternPic_" + project;
	}

	public void execute() {
		String matchWithId = "em_largest_match_with_pattern_id_" + project;
		String matchCollapsed = "em_largest_match_collapsed_" + project;
		String sql = String.format(
				"SELECT collapsed_id, count(*) FROM %s LEFT JOIN %s ON %s.pattern_id=%s.pattern_id"
				+ " GROUP BY collapsed_id ORDER BY count(*) DESC",
				matchWithId, matchCollapsed, matchWithId, matchCollapsed);
		Connection conn = SqliteManager.getConnection();
		try {
			Statement stmt = conn.createStatement();
			ResultSet rs = stmt.executeQuery(sql);
			int index = 1;
			while (rs.next() && index <= 5) {
				String id = rs.getString(1);
				int count = rs.getInt(2);
				System.out.println(id + "," + count);
				String extractedFileName = id + ".png";
				Path sourcePath = FileSystems.getDefault().getPath(picFolder, extractedFileName);
				String outputFileName = project + "-" + index + ".png";
				Path targetPath = FileSystems.getDefault().getPath(outputFolder, outputFileName);
				try {
					Files.copy(sourcePath, targetPath);
				} catch (IOException e) {
					e.printStackTrace();
				}
				
				index++;
			}
		} catch (SQLException e) {
			e.printStackTrace();
		}
	}
	
	public static void initFolder(String folder) {
		Path path = Paths.get(folder);
		if (Files.exists(path)) {
			// empty the folder
			try (DirectoryStream<Path> stream = Files.newDirectoryStream(path)) {
			    for (Path file: stream) {
			    	Files.delete(file);
			    }
			} catch (IOException | DirectoryIteratorException x) {
			    x.printStackTrace();
			}
		} else {
			// create the folder
			try {
				Files.createDirectory(path);
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
	}

	public static void main(String[] args) {
		
		initFolder(outputFolder);
		
		String[] projects = {"aries", "cassandra", "derby", "mahout"};
		for (String project: projects) {
			System.out.println(project);
			LMatchTopPatternSummary summary = new LMatchTopPatternSummary(project);
			summary.execute();
		}
	}
}
