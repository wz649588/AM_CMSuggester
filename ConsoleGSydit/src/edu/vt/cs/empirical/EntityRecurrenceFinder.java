package edu.vt.cs.empirical;

import static java.nio.file.StandardOpenOption.CREATE;
import static java.nio.file.StandardOpenOption.TRUNCATE_EXISTING;

import java.io.IOException;
import java.io.OutputStream;
import java.lang.reflect.Type;
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
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import org.apache.poi.xssf.usermodel.XSSFRow;
import org.apache.poi.xssf.usermodel.XSSFSheet;
import org.apache.poi.xssf.usermodel.XSSFWorkbook;
import org.jgrapht.Graph;

import com.google.gson.Gson;
import com.google.gson.reflect.TypeToken;

import edu.vt.cs.editscript.json.GraphDataWithNodesJson;
import edu.vt.cs.editscript.json.GraphDataJson.GraphEdge;
import edu.vt.cs.editscript.json.GraphDataJson.GraphNode;
import edu.vt.cs.graph.ReferenceNode;
import edu.vt.cs.sql.SqliteManager;

/**
 * (M1, M2) -> (C1, C2, ...)
 * @author Ye Wang
 * @since 03/13/2018
 *
 */
public class EntityRecurrenceFinder {
	
	private String project;
	
	private String editScriptTable;
	
	private String disaTable;
	
	private String coTable;
	
	private String parentFolder = "/Users/Vito/Documents/VT/2018spring/SE/characterization/co";
	
	
	
	public EntityRecurrenceFinder(String project) {
		this.project = project;
		this.editScriptTable = "edit_script_table_" + project;
		this.disaTable = "disa_" + project;
		this.coTable = "disa_co_" + project;
	}
	
	/**
	 * Disassemble graphs in edit script table into one node per row
	 * @throws SQLException
	 */
	public void disaGraph() throws SQLException {
		Connection conn = SqliteManager.getConnection();
		Statement stmt = conn.createStatement();
		
		stmt.executeUpdate("DROP TABLE IF EXISTS " + disaTable);
		stmt.executeUpdate("CREATE TABLE IF NOT EXISTS " + disaTable
				+ " (bug_name TEXT,entity_sig TEXT,node_type TEXT)");
		
		ResultSet rs = stmt.executeQuery("SELECT count(*) FROM " + editScriptTable);
		rs.next();
		int totalRow = rs.getInt(1);
		rs.close();
		
		Gson gson = new Gson();
		PreparedStatement ps = conn.prepareStatement("INSERT INTO "
				+ disaTable + " (bug_name,entity_sig,node_type) VALUES (?,?,?)");
		for (int offset = 0; offset < totalRow; offset++) {
			rs = stmt.executeQuery("SELECT bug_name, graph_data FROM "
					+ editScriptTable + " LIMIT 1 OFFSET " + offset);
			rs.next();
			String bugName = rs.getString(1);
			String graphDataJson = rs.getString(2);
			GraphDataWithNodesJson graphData = gson.fromJson(graphDataJson, GraphDataWithNodesJson.class);
			Graph<GraphNode, GraphEdge>	graph = graphData.getJgrapht();
			
			ps.setString(1, bugName);
			for (GraphNode n: graph.vertexSet()) {
				String sig = n.getName();
				int type = n.getType();
				String nodeType = ReferenceNode.getTypeString(type);
				ps.setString(2, sig);
				ps.setString(3, nodeType);
				ps.executeUpdate();
				
			}
			
		}
		
		ps.close();
		stmt.close();
		conn.close();
		
	}
	
	/**
	 * Find the entity pair co-occuring in multiple commits.
	 * @throws SQLException
	 */
	public void findCooccur() throws SQLException {
		Connection conn = SqliteManager.getConnection();
		Statement stmt = conn.createStatement();
		
		stmt.executeUpdate("DROP TABLE IF EXISTS " + coTable);
		stmt.executeUpdate("CREATE TABLE " + coTable
				+ " (left_entity TEXT,right_entity TEXT,"
				+ "commit_info TEXT,commit_num INTEGER,is_same_type TEXT,same_type TEXT)");
		
		
		ResultSet rs = stmt.executeQuery("SELECT entity_sig FROM "
				+ "(SELECT entity_sig, count(*) AS num"
				+ " FROM " + disaTable + " GROUP BY entity_sig ORDER BY num DESC)"
				+ " WHERE num > 1");
		
		List<String> entityList = new ArrayList<>();
		while (rs.next()) {
			String entitySig = rs.getString(1);
			entityList.add(entitySig);
		}
		rs.close();
		
		Gson gson = new Gson();
		
		// one to one compare
		PreparedStatement ps = conn.prepareStatement("SELECT bug_name,node_type FROM " + disaTable + " WHERE entity_sig=?");
		PreparedStatement ps2 = conn.prepareStatement("INSERT INTO "
				+ coTable + " (left_entity,right_entity,commit_info,commit_num,is_same_type,same_type) VALUES (?,?,?,?,?,?)");
		for (int i = 0; i < entityList.size() - 1; i++) {
			System.out.println(i + 1 + "/" + entityList.size());
			String leftEntity = entityList.get(i);
			ps.setString(1, leftEntity);
			rs = ps.executeQuery();
			List<String> leftCommits = new ArrayList<>();
			Map<String, String> leftCommitToType = new HashMap<>();
			while (rs.next()) {
				String commit = rs.getString(1);
				String nodeType = rs.getString(2);
				leftCommits.add(commit);
				leftCommitToType.put(commit, nodeType);
			}
			rs.close();
			
			ps2.setString(1, leftEntity);
			
			for (int j = i + 1; j < entityList.size(); j++) {
				String rightEntity = entityList.get(j);
				ps.setString(1, rightEntity);
				rs = ps.executeQuery();
				List<String> rightCommits = new ArrayList<>();
				Map<String, String> rightCommitToType = new HashMap<>();
				while (rs.next()) {
					String commit = rs.getString(1);
					String nodeType = rs.getString(2);
					rightCommits.add(commit);
					rightCommitToType.put(commit, nodeType);
				}
				rs.close();
				
				List<String> commonCommits = leftCommits;
				commonCommits.retainAll(rightCommits);
				
				if (commonCommits.size() < 2)
					continue;
				
				String sameType = null;
				boolean isSameType = true;
				List<Map<String, String>> commitInfoList = new ArrayList<>(); 
				for (String c: commonCommits) {
					Map<String, String> commitInfo = new LinkedHashMap<>();
					String leftType = leftCommitToType.get(c);
					String rightType = rightCommitToType.get(c);
					commitInfo.put("commit", c);
					commitInfo.put("leftType", leftType);
					commitInfo.put("rightType", rightType);
					if (isSameType) {
						if (sameType == null)
							sameType = leftType;
						else if (!sameType.equals(leftType))
							isSameType = false;
						if (!sameType.equals(rightType))
							isSameType = false;
					}
					commitInfoList.add(commitInfo);
				}
				
				ps2.setString(2, rightEntity);
				ps2.setString(3, gson.toJson(commitInfoList));
				ps2.setInt(4, commonCommits.size());
				ps2.setString(5, isSameType ? "y" : "n");
				ps2.setString(6, isSameType ? sameType : null);
				ps2.executeUpdate();
				
				
			}
		}
		
		ps2.close();
		ps.close();
		stmt.close();
		conn.close();
	}
	
	public void saveToFile() throws SQLException, IOException {
		Gson gson = new Gson();
		Connection conn = SqliteManager.getConnection();
		Statement stmt = conn.createStatement();
		
		ResultSet rs = stmt.executeQuery("SELECT left_entity,right_entity,commit_info,commit_num,same_type FROM "
				+ coTable + " WHERE is_same_type='y'");
		
		XSSFWorkbook workbook = new XSSFWorkbook();
		XSSFSheet sheet = workbook.createSheet();
		XSSFRow row = sheet.createRow(0);
		row.createCell(0).setCellValue("left_entity");
		row.createCell(1).setCellValue("right_entity");
		row.createCell(2).setCellValue("commit_info");
		row.createCell(3).setCellValue("commit_num");
		row.createCell(4).setCellValue("node_type");
		int rowNum = 0;
		while (rs.next()) {
			String leftEntity = rs.getString(1);
			String rightEntity = rs.getString(2);
			String commitInfoJson = rs.getString(3);
			int commitNum = rs.getInt(4);
			String nodeType = rs.getString(5);
			
			Type commitInfoType = new TypeToken<List<Map<String, String>>>() {}.getType();
			List<Map<String, String>> commitInfoList = gson.fromJson(commitInfoJson, commitInfoType);
			List<String> commitInfo = new ArrayList<>();
			for (Map<String, String> info: commitInfoList) {
				String commit = info.get("commit");
				commitInfo.add(commit);
			}
			
			rowNum++;
			row = sheet.createRow(rowNum);
			row.createCell(0).setCellValue(leftEntity);
			row.createCell(1).setCellValue(rightEntity);
			row.createCell(2).setCellValue(gson.toJson(commitInfo));
			row.createCell(3).setCellValue(commitNum);
			row.createCell(4).setCellValue(nodeType);
		}
		rs.close();
		
		Path parentPath = Paths.get(parentFolder);
		Path file1Path = parentPath.resolve("co_same_type_" + project + ".xlsx");
		OutputStream xlsxFile1 = Files.newOutputStream(file1Path, CREATE, TRUNCATE_EXISTING);
		workbook.write(xlsxFile1);
		xlsxFile1.close();
		workbook.close();
		
		rs = stmt.executeQuery("SELECT left_entity,right_entity,commit_info,commit_num FROM "
				+ coTable + " WHERE is_same_type='n'");
		workbook = new XSSFWorkbook();
		sheet = workbook.createSheet();
		row = sheet.createRow(0);
		row.createCell(0).setCellValue("left_entity");
		row.createCell(1).setCellValue("right_entity");
		row.createCell(2).setCellValue("commit_info");
		row.createCell(3).setCellValue("commit_num");
		rowNum = 0;
		while (rs.next()) {
			String leftEntity = rs.getString(1);
			String rightEntity = rs.getString(2);
			String commitInfoJson = rs.getString(3);
			int commitNum = rs.getInt(4);
			
			rowNum++;
			row = sheet.createRow(rowNum);
			row.createCell(0).setCellValue(leftEntity);
			row.createCell(1).setCellValue(rightEntity);
			row.createCell(2).setCellValue(commitInfoJson);
			row.createCell(3).setCellValue(commitNum);
		}
		rs.close();
		Path file2Path = parentPath.resolve("co_not_same_type_" + project + ".xlsx");
		OutputStream xlsxFile2 = Files.newOutputStream(file2Path, CREATE, TRUNCATE_EXISTING);
		workbook.write(xlsxFile2);
		xlsxFile2.close();
		workbook.close();
		
		
		stmt.close();
		conn.close();
	}
	
	
	public static void main(String[] args) throws SQLException, IOException {
		String[] projects = {"aries", "cassandra", "derby", "mahout"};
		for (String project: projects) {
			System.out.println(project);
			EntityRecurrenceFinder finder = new EntityRecurrenceFinder(project);
//			finder.disaGraph();
//			finder.findCooccur();
			finder.saveToFile();
		}
		
	}

}
