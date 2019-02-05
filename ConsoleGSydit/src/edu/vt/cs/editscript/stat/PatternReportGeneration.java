package edu.vt.cs.editscript.stat;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.lang.reflect.Type;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import com.google.gson.Gson;
import com.google.gson.reflect.TypeToken;
import com.ibm.wala.util.WalaException;
import com.ibm.wala.viz.DotUtil;

import edu.vt.cs.editscript.common.LongestCommonSubseq;
import edu.vt.cs.editscript.json.ScriptEdge;
import edu.vt.cs.editscript.json.ScriptNode;
import edu.vt.cs.editscript.json.EditScriptJson.EditOperationJson;
import edu.vt.cs.graph.ReferenceEdge;
import edu.vt.cs.graph.ReferenceNode;
import edu.vt.cs.sql.SqliteManager;

/**
 * With the unique patterns in script_stat_grouped_pattern and classified data
 * in script_stat_data_with_pattern, we can generate a report. The report data
 * will be stored in script_stat_report
 * 
 * @author Ye Wang
 * @since 04/16/2017
 *
 */
public class PatternReportGeneration {
	
	private static String patternPicDir = "/Users/Vito/Documents/VT/2016fall/SE/patternDataPic";
	
	private static String dotExe = "/usr/local/bin/dot";
	
	private static boolean executeFromScratch = true;
	
	public static void main(String[] args) throws SQLException {
		generatePatternPictures();
		generateReportTable();
	}
	
	private static void generateReportTable() throws SQLException {
		Connection conn = SqliteManager.getConnection();
		Statement stmt = conn.createStatement();
		
		if (executeFromScratch)
			stmt.executeUpdate("DROP TABLE IF EXISTS script_stat_report");
		
		stmt.executeUpdate("CREATE TABLE IF NOT EXISTS script_stat_report (pattern_id INTEGER, bn1 TEXT, gn1 INTEGER, bn2 TEXT, gn2 INTEGER, mapping_num INTEGER, common_script TEXT)");
		
		ResultSet rs = stmt.executeQuery("SELECT MAX(pattern_id) FROM script_stat_grouped_pattern");
		rs.next();
		int maxPatternId = rs.getInt(1);
		rs.close();
		
		Gson gson = new Gson();
		Type nodeMapType = new TypeToken<Map<ScriptNode, ScriptNode>>(){}.getType();
		Type patternNodeMapType = new TypeToken<Map<String, ScriptNode>>(){}.getType();
		
		PreparedStatement ps = conn.prepareStatement("INSERT INTO script_stat_report (pattern_id, bn1, gn1, bn2, gn2, mapping_num, common_script) VALUES (?,?,?,?,?,?,?)");
		
		for (int patternId = 1; patternId < maxPatternId; patternId++) {
			ps.setInt(1, patternId);
			rs = stmt.executeQuery("SELECT bn1,gn1,bn2,gn2,mapping_num,node_map,pattern_node_map FROM script_stat_data_with_pattern WHERE pattern_id=" + patternId);
			while (rs.next()) {
				String bn1 = rs.getString(1);
				int gn1 = rs.getInt(2);
				String bn2 = rs.getString(3);
				int gn2 = rs.getInt(4);
				int mappingNum = rs.getInt(5);
				String nodeMapJson = rs.getString(6);
				String patternNodeMapJson = rs.getString(7);
				
				Map<ScriptNode, ScriptNode> nodeMap = gson.fromJson(nodeMapJson, nodeMapType);
				Map<String, ScriptNode> patternNodeMap = gson.fromJson(patternNodeMapJson, patternNodeMapType);
				
				List<JsonReportData> reportDataList = new ArrayList<>();
				for (String shapeNode: patternNodeMap.keySet()) {
					JsonReportData reportData = new JsonReportData();
					ScriptNode leftNode = patternNodeMap.get(shapeNode);
					ScriptNode rightNode = nodeMap.get(leftNode);
					List<JsonReportEdit> commonScript = new ArrayList<>();
					List<EditOperationJson> leftScript = leftNode.getScript();
					List<EditOperationJson> rightScript = rightNode.getScript();
					
					reportData.shapeNode = shapeNode;
					reportData.left = leftNode.getName();
					reportData.right = rightNode.getName();
					
					if (leftScript != null && !leftScript.isEmpty() && rightScript != null && !rightScript.isEmpty()) {
						LongestCommonSubseq<EditOperationJson> lcs = new LongestCommonSubseq<>(leftScript, rightScript);
						List<EditOperationJson> lcsScript = lcs.getResultList();
						for (EditOperationJson e: lcsScript) {
							JsonReportEdit edit = new JsonReportEdit();
							edit.type = e.getType();
							edit.label = e.getLabel();
							commonScript.add(edit);
						}
						reportData.commonScript = commonScript;
					} else {
						reportData.commonScript = null;
					}
					reportDataList.add(reportData);
				}
				
				ps.setString(2, bn1);
				ps.setInt(3, gn1);
				ps.setString(4, bn2);
				ps.setInt(5, gn2);
				ps.setInt(6, mappingNum);
				ps.setString(7, gson.toJson(reportDataList));
				ps.executeUpdate();
				
				
			}
		}
		
		ps.close();
		
		stmt.close();
		conn.close();
	}
	
	private static void generatePatternPictures() throws SQLException {
		
		Path picDirPath = FileSystems.getDefault().getPath(patternPicDir);
		try {
			Files.createDirectories(picDirPath);
		} catch (IOException e) {
			e.printStackTrace();
		}
		
		Connection conn = SqliteManager.getConnection();
		Statement stmt = conn.createStatement();
		
		Gson gson = new Gson();
		Type scriptEdgeListType = new TypeToken<List<ScriptEdge>>(){}.getType();
		
		ResultSet rs = stmt.executeQuery("SELECT pattern_id, shape FROM script_stat_grouped_pattern");
		while (rs.next()) {
			int patternId = rs.getInt(1);
			String shapeJson = rs.getString(2);
			List<ScriptEdge> shape = gson.fromJson(shapeJson, scriptEdgeListType);
			String dot = synthesizeDot(shape);
			writePicFile(patternId, dot);
		}
		
		
		stmt.close();
		conn.close();
	}
	
	private static void writePicFile(int index, String dot) {
		File f = null;
	    try {
	    	f = File.createTempFile("dot_data", null);
			FileWriter fw = new FileWriter(f);
			fw.write(dot);
			fw.close();
		} catch (Exception e) {
			e.printStackTrace();
	    }
	    
	    String picFile = patternPicDir + "/" + index + ".png";
	    String[] cmds = {dotExe, "-Tpng", "-Gdpi=300", "-o", picFile, "-v", f.getAbsolutePath()};
	    try {
			Process p = Runtime.getRuntime().exec(cmds);
			try {
				p.waitFor();
			} catch (InterruptedException e) {
				e.printStackTrace();
			}
		} catch (IOException e) {
			e.printStackTrace();
		}
	    
	    f.delete();
	}
	
	private static String synthesizeDot(List<ScriptEdge> edges) {
		int fontSize = 16;
		String fontColor = "black";
		String fontName = "Arial";
		StringBuilder result = new StringBuilder("digraph \"DirectedRelationGraph\" {\n");
		result.append("graph [concentrate = true];");
	    
	    String fontsizeStr = "fontsize=" + fontSize;
	    String fontcolorStr = (fontColor != null) ? ",fontcolor="+fontColor : "";
	    String fontnameStr = (fontName != null) ? ",fontname="+fontName : "";
	         
	    result.append("center=true;");
	    result.append(fontsizeStr);
	    result.append(";node [ color=blue,shape=\"box\"");
	    result.append(fontsizeStr);
	    result.append(fontcolorStr);
	    result.append(fontnameStr);
	    result.append("];edge [ color=black,");
	    result.append(fontsizeStr);
	    result.append(fontcolorStr);
	    result.append(fontnameStr);
	    result.append("]; \n");
	    
//	    for (ReferenceNode vertex: g.vertexSet()) {
//	    	 result.append("   ");
//	    	 result.append("\"");
//	    	 result.append(resolveNodeType(vertex.type) + " " + vertex.toString());//label contains simple representation of each node
//	    	 result.append("\"");
//	    	 result.append(" [ ]\n");
//	    }
	
		for (ScriptEdge edge: edges) {
			result.append(" ");
    		result.append("\"" + edge.getSrc().getName() + "\"");
	        result.append(" -> ");
	        result.append("\"" + edge.getDst().getName() + "\"");
	        result.append(" [");
	        if (edge.getType() == ReferenceEdge.FIELD_ACCESS) {
	        	result.append("color=red");
	        } else if (edge.getType() == ReferenceEdge.METHOD_INVOKE){ // edgeType is CONTROL_FLOW
	        	result.append("color=blue");
	        } else { // METHOD_OVERRIDE
	        	result.append("color=yellow");
	        }
	        result.append("]\n");
		}
	    
	    result.append("\n}");
		return result.toString();
	}
}

class JsonReportData {
	public String shapeNode;
	public String left;
	public String right;
	public List<JsonReportEdit> commonScript;
}

class JsonReportEdit {
	public String type;
	public String label;
}
