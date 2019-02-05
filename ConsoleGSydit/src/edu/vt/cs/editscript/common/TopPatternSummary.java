package edu.vt.cs.editscript.common;

import java.io.IOException;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
import java.sql.Connection;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;

import edu.vt.cs.sql.SqliteManager;

public class TopPatternSummary {
	
	private String project;
	
	private String picFolder;
	
	private String outputFolder = "/Users/zijianjiang/Documents/NaM/top-pattern";
	
	public TopPatternSummary(String project) {
		this.project = project;
		picFolder = "/Users/zijianjiang/Documents/NaM/largestPatternPic_" + project;
	}

	public void execute() {
		
		
		String matchWithId = project + "_largest_match_with_pattern_id";
		String matchCollapsed = project + "_largest_match_collapsed";
		String sql = String.format(
				"SELECT collapsed_id, count(*) FROM %s LEFT JOIN %s ON %s.pattern_id=%s.pattern_id"
				+ " GROUP BY collapsed_id ORDER BY count(*) DESC",
				matchWithId, matchCollapsed, matchWithId, matchCollapsed);
//		System.out.println(sql);
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
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
				
				index++;
			}
		} catch (SQLException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	public static void main(String[] args) {
		String[] projects = {"aries", "cassandra", "derby", "mahout"};
		for (String project: projects) {
			System.out.println(project);
			TopPatternSummary summary = new TopPatternSummary(project);
			summary.execute();
		}
	}
}
