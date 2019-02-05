package edu.vt.cs.editscript.common;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.sql.Connection;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.jgrapht.Graph;

import com.google.gson.Gson;

import edu.vt.cs.editscript.json.GraphDataJson;
import edu.vt.cs.editscript.json.ScriptEdge;
import edu.vt.cs.editscript.json.GraphDataJson.GraphEdge;
import edu.vt.cs.editscript.json.GraphDataJson.GraphNode;
import edu.vt.cs.graph.ReferenceEdge;
import edu.vt.cs.sql.SqliteManager;

/**
 * This class generates the pictures for 
 * @author Ye Wang
 *
 */
public class LargestMatchPicGeneration {
	
	private static String patternPicDir = "/Users/zijianjiang/Documents/NaM/largestPatternPic";
	
	private static String dotExe = "/usr/local/bin/dot";

	public static void main(String[] args) throws SQLException {
		/*
		 * 1. Extract shape from largest_match_pattern
		 * 2. Convert each to shape to a picture and store it. 
		 */
		Connection conn = SqliteManager.getConnection();
		Statement stmt = conn.createStatement();
		
		// aries, cassandra, derby, mahout
		String project = "aries";
		String patternTable = project + "_largest_match_pattern";
		
		Gson gson = new Gson();
		ResultSet rs = stmt.executeQuery("SELECT pattern_id, shape FROM " + patternTable);
		while (rs.next()) {
			int patternId = rs.getInt(1);
			String jsonShape = rs.getString(2);
			GraphDataJson shape = gson.fromJson(jsonShape, GraphDataJson.class);
			List<GraphEdge> edges = shape.getEdges();
			
			
			// convert the shape to a picture
			generatePicture(Integer.toString(patternId), edges);
			
		}
		
		String collapsedTable = project + "_largest_match_collapsed";
		rs = stmt.executeQuery("SELECT collapsed_id, collapsed_shape FROM "
				+ collapsedTable + " WHERE collapsed_shape IS NOT NULL");
		Set<String> uniqueIdSet = new HashSet<>();
		while (rs.next()) {
			String collapsedId = rs.getString(1);
			String collapsedShape = rs.getString(2);
			if (uniqueIdSet.contains(collapsedId))
				continue;
			GraphDataJson shape = gson.fromJson(collapsedShape, GraphDataJson.class);
			List<GraphEdge> edges = shape.getEdges();
			generatePicture(collapsedId, edges);
		}
		
		stmt.close();
		conn.close();
	}
	
	private static void generatePicture(String patternId, List<GraphEdge> edges) {
		String dot = synthesizeDot(edges);
//		System.out.println(dot);
		
		writePicFile(patternId, dot);
//		System.exit(0);
	}
	
	private static String synthesizeDot(List<GraphEdge> edges) {
		int fontSize = 24;
		String fontColor = "black";
		String fontName = "Arial";
		StringBuilder result = new StringBuilder("digraph \"DirectedRelationGraph\" {\n");
		result.append("graph [concentrate = true];");
	    
	    String fontsizeStr = "fontsize=" + fontSize;
	    String fontcolorStr = (fontColor != null) ? ",fontcolor="+fontColor : "";
	    String fontnameStr = (fontName != null) ? ",fontname="+fontName : "";
	         
	    result.append("center=true;");
	    result.append(fontsizeStr);
	    result.append(";node [ color=black,shape=\"box\"");
	    result.append(fontsizeStr);
	    result.append(fontcolorStr);
	    result.append(fontnameStr);
	    result.append("];edge [ color=black,");
	    result.append(fontsizeStr);
	    result.append(fontcolorStr);
	    result.append(fontnameStr);
	    result.append("]; \n");
	
		for (GraphEdge edge: edges) {
			result.append(" ");
    		result.append("\"" + edge.getSrc().getName() + "\"");
	        result.append(" -> ");
	        result.append("\"" + edge.getDst().getName() + "\"");
	        result.append(" [");
	        if (edge.getType() == ReferenceEdge.FIELD_ACCESS) {
	        	result.append("color=black,penwidth=2,arrowsize=0.7,label=\" f\",fontsize=28");
	        } else if (edge.getType() == ReferenceEdge.METHOD_INVOKE){
	        	result.append("color=black,penwidth=2,arrowsize=0.7,label=\" m\",fontsize=28");
	        } else { // METHOD_OVERRIDE
	        	result.append("color=black,style=dashed,penwidth=2,arrowsize=0.7");
	        }
	        result.append("]\n");
		}
	    
	    result.append("\n}");
		return result.toString();
	}
	
	private static void writePicFile(String index, String dot) {
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
}
