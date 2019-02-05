package edu.vt.cs.empirical;

import java.io.IOException;
import java.io.OutputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;

import static java.nio.file.StandardOpenOption.*;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.Arrays;
import java.util.List;

import org.apache.poi.xssf.usermodel.XSSFRow;
import org.apache.poi.xssf.usermodel.XSSFSheet;
import org.apache.poi.xssf.usermodel.XSSFWorkbook;
import org.jgrapht.Graph;

import com.google.gson.Gson;

import edu.vt.cs.editscript.json.GraphDataWithNodesJson;
import edu.vt.cs.editscript.json.GraphDataJson.GraphEdge;
import edu.vt.cs.editscript.json.GraphDataJson.GraphNode;
import edu.vt.cs.graph.ReferenceNode;
import edu.vt.cs.sql.SqliteManager;

/**
 * After the TSE paper got rejected, I have to redo the empirical study part.
 * I rerun the program to get the change dependency graphs, and now I use this
 * class to extract statistics from the graphs.
 * @author Ye Wang
 * @since 03/10/2018
 *
 */
public class GraphStatExtraction {
	
	private String graphTable;
	
	private String resultTable;
	
	public GraphStatExtraction(String graphTable, String resultTable) {
		this.graphTable = graphTable;
		this.resultTable = resultTable;
	}
	
	public void execute() throws SQLException {
		// set up result table in database
		Connection conn = SqliteManager.getConnection();
		Statement stmt = conn.createStatement();
		
		// am, dm, ... mean entities' numbers in each commit.
		// graph_nums should be a JSON array, the first number is the number of
		// graphs whose node number is one, the second number is the number of
		// graphs whose node number is two, etc.
		stmt.executeUpdate("DROP TABLE IF EXISTS " + resultTable);
		stmt.executeUpdate("CREATE TABLE " + resultTable
				+ " (bug_name TEXT,graph_num INTEGER,"
				+ "am INTEGER,dm INTEGER,cm INTEGER,"
				+ "af INTEGER,df INTEGER,cf INTEGER,"
				+ "ac INTEGER,dc INTEGER,total_num INTEGER)");
		
		
		// get data from graph table
		ResultSet rs = stmt.executeQuery("SELECT count(*) FROM " + graphTable);
		rs.next();
		int totalRow = rs.getInt(1);
		rs.close();
		
		Gson gson = new Gson();
		
		PreparedStatement ps = conn.prepareStatement("INSERT INTO " + resultTable
				+ " (bug_name,graph_num,am,dm,cm,af,df,cf,ac,dc,total_num) "
				+ "VALUES (?,?,?,?,?,?,?,?,?,?,?)");
		
		for (int offset = 0; offset < totalRow; offset++) {
			rs = stmt.executeQuery("SELECT bug_name,graph_num,graph_data FROM " + graphTable + " LIMIT 1 OFFSET " + offset);
			rs.next();
			String bugName = rs.getString(1);
			int graphNum = rs.getInt(2);
			String graphData = rs.getString(3);
			rs.close();
			
			GraphDataWithNodesJson graphDataWithNodesJson = gson.fromJson(graphData, GraphDataWithNodesJson.class);
			Graph<GraphNode, GraphEdge> graph = graphDataWithNodesJson.getJgrapht();
			int am = 0;
			int dm = 0;
			int cm = 0;
			int af = 0;
			int df = 0;
			int cf = 0;
			int ac = 0;
			int dc = 0;
			int totalNum = 0;
			for (GraphNode node: graph.vertexSet()) {
				int nodeType = node.getType();
				switch (nodeType) {
				case ReferenceNode.AM:
					am++;
					break;
				case ReferenceNode.DM:
					dm++;
					break;
				case ReferenceNode.CM:
					cm++;
					break;
				case ReferenceNode.AF:
					af++;
					break;
				case ReferenceNode.DF:
					df++;
					break;
				case ReferenceNode.CF:
					df++;
					break;
				case ReferenceNode.AC:
					ac++;
					break;
				case ReferenceNode.DC:
					dc++;
					break;
				}
				totalNum++;
			}
			
			ps.setString(1, bugName);
			ps.setInt(2, graphNum);
			ps.setInt(3, am);
			ps.setInt(4, dm);
			ps.setInt(5, cm);
			ps.setInt(6, af);
			ps.setInt(7, df);
			ps.setInt(8, cf);
			ps.setInt(9, ac);
			ps.setInt(10, dc);
			ps.setInt(11, totalNum);
			ps.executeUpdate();
		}
		
		
		ps.close();
		stmt.close();
		conn.close();
	}
	
	public void createViews(List<String> viewList) throws SQLException {
		Connection conn = SqliteManager.getConnection();
		Statement stmt = conn.createStatement();
		
		// view 1
		String resultView1 = viewList.get(0);
		stmt.executeUpdate("DROP VIEW IF EXISTS " + resultView1);
		stmt.executeUpdate("CREATE VIEW " + resultView1
				+ " AS SELECT "
				+ "sum(am) AS am, sum(dm) AS dm, sum(cm) AS cm,"
				+ "sum(af) AS af, sum(df) AS df, sum(cf) AS cf,"
				+ "sum(ac) AS ac, sum(dc) AS dc FROM " + resultTable);
		
		// view 2
		String resultView2 = viewList.get(1);
		stmt.executeUpdate("DROP VIEW IF EXISTS " + resultView2);
		String subquery = "SELECT bug_name, sum(total_num) AS node_num FROM "
				+ resultTable + " GROUP BY bug_name";
		stmt.executeUpdate("CREATE VIEW " + resultView2
				+ " AS SELECT node_num, count(*) AS commit_num FROM (" + subquery
				+ ") GROUP BY node_num ORDER BY node_num ASC");
		
		
		// View 3
		String resultView3 = viewList.get(2);
		stmt.executeUpdate("DROP VIEW IF EXISTS " + resultView3);
		String subquery3 = "SELECT bug_name, count(*) AS cdg_num FROM "
				+ resultTable + " WHERE total_num>1 GROUP BY bug_name";
		stmt.executeUpdate("CREATE VIEW " + resultView3
				+ " AS SELECT cdg_num, count(*) AS commit_num FROM (" + subquery3
				+ ") GROUP BY cdg_num ORDER BY cdg_num ASC");
		
		stmt.close();
		conn.close();
	}
	
	private static long percent(int part, int total) {
		return Math.round(((double) part) / total * 100);
	}

	public static void main(String[] args) throws SQLException, IOException {
		String[] projects = {"aries", "cassandra", "derby", "mahout"};
		for (String project: projects) {
			String graphTable = "edit_script_table_" + project;
			String resultTable = "empirical_graph_stat_" + project;
			String resultView1 = "empirical_view1_" + project;
			String resultView2 = "empirical_view2_" + project;
			String resultView3 = "empirical_view3_" + project;
			List<String> resultViews = Arrays.asList(resultView1, resultView2, resultView3);
			GraphStatExtraction extraction = new GraphStatExtraction(graphTable, resultTable);
//			extraction.execute();
			extraction.createViews(resultViews);
		}
		
		// merge result
		String parentFolder = "/Users/Vito/Documents/VT/2018spring/SE/characterization/csv";
		
		Connection conn = SqliteManager.getConnection();
		Statement stmt = conn.createStatement();
		
		// xlsx table 1
		XSSFWorkbook workbook1 = new XSSFWorkbook();
		XSSFSheet sheet1 = workbook1.createSheet();
		XSSFRow row1 = sheet1.createRow(0);
		row1.createCell(0).setCellValue("project");
		row1.createCell(1).setCellValue("class");
		row1.createCell(2).setCellValue("method");
		row1.createCell(3).setCellValue("field");
		// xlsx table 2
		XSSFWorkbook workbook2 = new XSSFWorkbook();
		XSSFSheet sheet2 = workbook2.createSheet();
		XSSFRow row2 = sheet2.createRow(0);
		row2.createCell(0).setCellValue("project");
		row2.createCell(1).setCellValue("am");
		row2.createCell(2).setCellValue("dm");
		row2.createCell(3).setCellValue("cm");
		row2.createCell(4).setCellValue("af");
		row2.createCell(5).setCellValue("df");
		row2.createCell(6).setCellValue("cf");
		row2.createCell(7).setCellValue("ac");
		row2.createCell(8).setCellValue("dc");
		
		// data table 1 and 2
		StringBuilder table1Data = new StringBuilder();
		table1Data.append("project,class,method,field\n");
		StringBuilder table2Data = new StringBuilder();
		table2Data.append("project,am,dm,cm,af,df,cf,ac,dc\n");
		for (int i = 0; i < projects.length; i++) {
			String project = projects[i];
			String resultView1 = "empirical_view1_" + project;
			
			ResultSet rs = stmt.executeQuery("SELECT am,dm,cm,af,df,cf,ac,dc FROM " + resultView1);
			rs.next();
			int am = rs.getInt(1);
			int dm = rs.getInt(2);
			int cm = rs.getInt(3);
			int af = rs.getInt(4);
			int df = rs.getInt(5);
			int cf = rs.getInt(6);
			int ac = rs.getInt(7);
			int dc = rs.getInt(8);
			rs.close();
			
			int total = am + dm + cm + af + df + cf + ac + dc;
			
			table1Data.append(project).append(",");
			table1Data.append(percent(ac + dc, total)).append(",");
			table1Data.append(percent(am + dm + cm, total)).append(",");
			table1Data.append(percent(af + df + cf, total)).append("\n");
			
			int rowNum = i + 1;
			row1 = sheet1.createRow(rowNum);
			row1.createCell(0).setCellValue(project);
			row1.createCell(1).setCellValue(percent(ac + dc, total));
			row1.createCell(2).setCellValue(percent(am + dm + cm, total));
			row1.createCell(3).setCellValue(percent(af + df + cf, total));
			
			
			table2Data.append(project).append(",");
			table2Data.append(percent(am, total)).append(",").append(percent(dm, total)).append(",");
			table2Data.append(percent(cm, total)).append(",");
			table2Data.append(percent(af, total)).append(",").append(percent(df, total)).append(",");
			table2Data.append(percent(cf, total)).append(",");
			table2Data.append(percent(ac, total)).append(",").append(percent(dc, total)).append("\n");
			
			row2 = sheet2.createRow(rowNum);
			row2.createCell(0).setCellValue(project);
			row2.createCell(1).setCellValue(percent(am, total));
			row2.createCell(2).setCellValue(percent(dm, total));
			row2.createCell(3).setCellValue(percent(cm, total));
			row2.createCell(4).setCellValue(percent(af, total));
			row2.createCell(5).setCellValue(percent(df, total));
			row2.createCell(6).setCellValue(percent(cf, total));
			row2.createCell(7).setCellValue(percent(ac, total));
			row2.createCell(8).setCellValue(percent(dc, total));
			
		}
		Path parentPath = Paths.get(parentFolder);
		Path table1Path = parentPath.resolve("empirical_table1.csv");
//		Files.write(table1Path, table1Data.toString().getBytes(), CREATE, TRUNCATE_EXISTING);
		
		Path table2Path = parentPath.resolve("empirical_table2.csv");
//		Files.write(table2Path, table2Data.toString().getBytes(), CREATE, TRUNCATE_EXISTING);
		
		Path xlsxPath1 = parentPath.resolve("empirical_table1.xlsx");
		OutputStream xlsxFile1 = Files.newOutputStream(xlsxPath1, CREATE, TRUNCATE_EXISTING);
		workbook1.write(xlsxFile1);
		xlsxFile1.close();
		workbook1.close();
		
		Path xlsxPath2 = parentPath.resolve("empirical_table2.xlsx");
		OutputStream xlsxFile2 = Files.newOutputStream(xlsxPath2, CREATE, TRUNCATE_EXISTING);
		workbook2.write(xlsxFile2);
		xlsxFile2.close();
		workbook2.close();
		
		
		for (String project: projects) {
			
			// xlsx table 3
			XSSFWorkbook workbook3 = new XSSFWorkbook();
			XSSFSheet sheet3 = workbook3.createSheet();
			XSSFRow row3 = sheet3.createRow(0);
			row3.createCell(0).setCellValue("node_num");
			row3.createCell(1).setCellValue("commit_num");
			
			StringBuilder table3Data = new StringBuilder();
			table3Data.append("node_num,commit_num\n");
			String resultView2 = "empirical_view2_" + project;
			ResultSet rs = stmt.executeQuery("SELECT node_num,commit_num FROM " + resultView2);
			int rowNum = 0;
			while (rs.next()) {
				int nodeNum = rs.getInt(1);
				int commitNum = rs.getInt(2);
				table3Data.append(nodeNum).append(",").append(commitNum).append("\n");
				
				rowNum++;
				row3 = sheet3.createRow(rowNum);
				row3.createCell(0).setCellValue(nodeNum);
				row3.createCell(1).setCellValue(commitNum);
				
			}
			rs.close();
			Path table3Path = parentPath.resolve("empirical_table3_" + project + ".csv");;
//			Files.write(table3Path, table3Data.toString().getBytes(), CREATE, TRUNCATE_EXISTING);
			
			Path xlsxPath3 = parentPath.resolve("empirical_table3_" + project + ".xlsx");
			OutputStream xlsxFile3 = Files.newOutputStream(xlsxPath3, CREATE, TRUNCATE_EXISTING);
			workbook3.write(xlsxFile3);
			xlsxFile3.close();
			workbook3.close();
		}
		
		for (String project: projects) {
			
			// xlsx table 3
			XSSFWorkbook workbook4 = new XSSFWorkbook();
			XSSFSheet sheet4 = workbook4.createSheet();
			XSSFRow row4 = sheet4.createRow(0);
			row4.createCell(0).setCellValue("cdg_num");
			row4.createCell(1).setCellValue("commit_num");
			
			StringBuilder table4Data = new StringBuilder();
			table4Data.append("cdg_num,commit_num\n");
			String resultView3 = "empirical_view3_" + project;
			ResultSet rs = stmt.executeQuery("SELECT cdg_num,commit_num FROM " + resultView3);
			int rowNum = 0;
			while (rs.next()) {
				int cdgNum = rs.getInt(1);
				int commitNum = rs.getInt(2);
				table4Data.append(cdgNum).append(",").append(commitNum).append("\n");
				
				rowNum++;
				row4 = sheet4.createRow(rowNum);
				row4.createCell(0).setCellValue(cdgNum);
				row4.createCell(1).setCellValue(commitNum);
			}
			rs.close();
			Path table4Path = parentPath.resolve("empirical_table4_" + project + ".csv");
//			Files.write(table4Path, table4Data.toString().getBytes(), CREATE, TRUNCATE_EXISTING);
			
			Path xlsxPath4 = parentPath.resolve("empirical_table4_" + project + ".xlsx");
			OutputStream xlsxFile4 = Files.newOutputStream(xlsxPath4, CREATE, TRUNCATE_EXISTING);
			workbook4.write(xlsxFile4);
			xlsxFile4.close();
			workbook4.close();
		}
		
	}
}
