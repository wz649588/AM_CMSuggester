package edu.vt.cs.empirical;

import static java.nio.file.StandardOpenOption.CREATE;
import static java.nio.file.StandardOpenOption.TRUNCATE_EXISTING;

import java.io.IOException;
import java.io.OutputStream;
import java.nio.file.DirectoryIteratorException;
import java.nio.file.DirectoryStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.poi.xssf.usermodel.XSSFRow;
import org.apache.poi.xssf.usermodel.XSSFSheet;
import org.apache.poi.xssf.usermodel.XSSFWorkbook;
import org.jgrapht.Graph;

import com.google.gson.Gson;

import edu.vt.cs.editscript.json.GraphDataJson.GraphEdge;
import edu.vt.cs.editscript.json.GraphDataJson.GraphNode;
import edu.vt.cs.editscript.json.GraphDataWithNodesJson;
import edu.vt.cs.sql.SqliteManager;

/**
 * Find the patterns that exists in all 4 projects
 * @author Ye Wang
 * @since 03/21/2018
 */
public class LMatchUbiquitous {
	
	private String[] projects;
	
	private String[] collapsedTables;
	
	private String ubiTable = "em_largest_match_ubi";
	
	private String picFolder = "/Users/Vito/Documents/VT/2018spring/SE/characterization/patterns/ubiPic";

	public LMatchUbiquitous(String[] projects) {
		this.projects = projects;
		collapsedTables = new String[projects.length];
		for (int i = 0; i < projects.length; i++) {
			String project = projects[i];
			String cTable = "em_largest_match_collapsed_" + project;
			collapsedTables[i] = cTable;
		}
	}
	
	public void execute() throws SQLException, IOException {
		Connection conn = SqliteManager.getConnection();
		Statement stmt = conn.createStatement();
		Map<Graph<GraphNode, GraphEdge>, Map<String, String>> graphMap = new HashMap<>();
		
		Gson gson = new Gson();
		
		for (int i = 0; i < projects.length; i++) {
			String project = projects[i];
			String cTable = collapsedTables[i];
			ResultSet rs = stmt.executeQuery("SELECT shape,collapsed_id,collapsed_shape FROM " + cTable);
			Set<String> addedCids = new HashSet<>();
			while (rs.next()) {
				String shape = rs.getString(1);
				String cid = rs.getString(2);
				String collapsedShape = rs.getString(3);
				if (addedCids.contains(cid))
					continue;
				if (collapsedShape != null)
					shape = collapsedShape;
				GraphDataWithNodesJson graphDataJson = gson.fromJson(shape, GraphDataWithNodesJson.class);
				Graph<GraphNode, GraphEdge> current = graphDataJson.getJgrapht();
				Graph<GraphNode, GraphEdge> existingGraph = null;
				for (Graph<GraphNode, GraphEdge> g: graphMap.keySet()) {
					if (LMatchPatternExtraction.isGraphASubgraphOfGraphB(g, current)
							&& LMatchPatternExtraction.isGraphASubgraphOfGraphB(current, g)) {
						existingGraph = g;
						break;
					}
				}
				if (existingGraph == null) {
					Map<String, String> pSet = new HashMap<>();
					pSet.put(project, cid);
					graphMap.put(current, pSet);
				} else {
					Map<String, String> pSet = graphMap.get(existingGraph);
					pSet.put(project, cid);
				}
			}
			rs.close();
		}
		
		stmt.executeUpdate("DROP TABLE IF EXISTS " + ubiTable);
		String sql = "CREATE TABLE IF NOT EXISTS " + ubiTable + " (shape TEXT";
		for (String project: projects) {
			sql += "," + project + "_id TEXT," + project + "_cnum INTEGER";
		}
		sql += ")";
		stmt.executeUpdate(sql);
		
		String sql2 = "INSERT INTO " + ubiTable + "(shape";
		for (String project: projects) {
			sql2 += "," + project + "_id," + project + "_cnum";
		}
		sql2 += ") VALUES (";
		for (int i = 0; i < 2 * projects.length; i++) {
			sql2 += "?,";
		}
		sql2 += "?)";
		PreparedStatement ps = conn.prepareStatement(sql2);
		for (Graph<GraphNode, GraphEdge> g: graphMap.keySet()) {
			Map<String, String> pMap = graphMap.get(g);
			if (pMap.size() < projects.length)
				continue;
			ps.setString(1, GraphDataWithNodesJson.convertToJsonClass(g).toJson());
			for (int i = 0; i < projects.length; i++) {
				String project = projects[i];
				String cid = pMap.get(project);
				String matchWithId = "em_largest_match_with_pattern_id_" + project;
				String matchCollapsed = "em_largest_match_collapsed_" + project;
				String sql3 = String.format(
						"SELECT count(DISTINCT bug_name) AS cnum "
						+ "FROM %s LEFT JOIN %s ON %s.pattern_id=%s.pattern_id"
						+ " WHERE collapsed_id='%s'",
						matchWithId, matchCollapsed, matchWithId, matchCollapsed, cid);
				ResultSet rs = stmt.executeQuery(sql3);
				rs.next();
				int cnum = rs.getInt(1);
				rs.close();
				ps.setString(2 * i + 2, cid);
				ps.setInt(2 * i + 3, cnum);
			}
			ps.executeUpdate();
		}
		
		// generate pictures
		initFolder(picFolder);
		Path folderPath = Paths.get(picFolder);
		String sql4 = "SELECT " + projects[0] + "_id,";
		for (int i = 0; i < projects.length; i++) {
			String project = projects[i];
			sql4 += project + "_cnum";
			if (i < projects.length - 1)
				sql4 += "+";
		}
		sql4 += " AS tnum FROM " + ubiTable + " ORDER BY tnum DESC"; 
		ResultSet rs = stmt.executeQuery(sql4);
		
		Path srcFolder = Paths.get("/Users/Vito/Documents/VT/2018spring/SE/characterization/patterns/largestPatternPic_" + projects[0]);
		
		int ubiNum = 0;
		while (rs.next()) {
			ubiNum++;
			String fileId = rs.getString(1);
			Path srcFile = srcFolder.resolve(fileId + ".png");
			Path dstFile = folderPath.resolve(ubiNum + ".png");
			try {
				Files.copy(srcFile, dstFile);
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
		
		// build spreadsheet
		XSSFWorkbook workbook1 = new XSSFWorkbook();
		XSSFSheet sheet1 = workbook1.createSheet();
		XSSFRow row1 = sheet1.createRow(0);
		row1.createCell(0).setCellValue("rank");
		for (int i = 0; i < projects.length; i++) {
			row1.createCell(i + 1).setCellValue(projects[i]);
		}
		String sql5 = "SELECT ";
		for (int i = 0; i < projects.length; i++) {
			String project = projects[i];
			sql5 += project + "_cnum";
			if (i < projects.length - 1)
				sql5 += ",";
		}
		sql5 += " FROM " + ubiTable + " ORDER BY ";
		for (int i = 0; i < projects.length; i++) {
			sql5 += projects[i] + "_cnum";
			if (i < projects.length - 1)
				sql5 += "+";
		}
		sql5 += " DESC";
		rs = stmt.executeQuery(sql5);
		int rowNum = 0;
		while (rs.next()) {
			rowNum++;
			row1 = sheet1.createRow(rowNum);
			row1.createCell(0).setCellValue(rowNum);
			for (int i = 1; i <= projects.length; i++) {
				row1.createCell(i).setCellValue(rs.getInt(i));
			}
		}
		
		String parentFolder = "/Users/Vito/Documents/VT/2018spring/SE/characterization/patterns";
		Path ssPath = Paths.get(parentFolder, "ubi.xlsx");
		OutputStream xlsxFile1 = Files.newOutputStream(ssPath, CREATE, TRUNCATE_EXISTING);
		workbook1.write(xlsxFile1);
		xlsxFile1.close();
		workbook1.close();

		
		ps.close();
		stmt.close();
		conn.close();
		
		
		
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
	
	public static void main(String[] args) throws SQLException, IOException {
		String projects[] = {"aries", "cassandra", "derby", "mahout"};
		LMatchUbiquitous finder = new LMatchUbiquitous(projects);
		finder.execute();
		
	}
}
