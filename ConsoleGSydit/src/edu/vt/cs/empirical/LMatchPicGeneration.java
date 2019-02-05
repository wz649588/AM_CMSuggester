package edu.vt.cs.empirical;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.DirectoryIteratorException;
import java.nio.file.DirectoryStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.sql.Connection;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import com.google.gson.Gson;

import edu.vt.cs.editscript.json.GraphDataJson;
import edu.vt.cs.editscript.json.GraphDataJson.GraphEdge;
import edu.vt.cs.graph.ReferenceEdge;
import edu.vt.cs.sql.SqliteManager;

public class LMatchPicGeneration {
	
	private String project;
	
	private String patternPicDir;
	
	private static final String dotExe = "/usr/local/bin/dot";
	
	public LMatchPicGeneration(String project) {
		this.project = project;
		this.patternPicDir = "/Users/zijianjiang/Documents/NaM/characterization/patterns/largestPatternPic_" + project;
		
	}
	
	private static void initFolder(String folder) {
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
	
	public void execute() throws SQLException {
		
		initFolder(patternPicDir);
		
		/*
		 * 1. Extract shape from largest_match_pattern
		 * 2. Convert each to shape to a picture and store it. 
		 */
		Connection conn = SqliteManager.getConnection();
		Statement stmt = conn.createStatement();
		
		String patternTable =  "em_largest_match_pattern_" + project;
		
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
		
		String collapsedTable = "em_largest_match_collapsed_" + project;
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

	public static void main(String[] args) throws SQLException {
		String[] projects = {"aries", "cassandra", "derby", "mahout"};
		for (String project: projects) {
			LMatchPicGeneration picGeneration = new LMatchPicGeneration(project);
			picGeneration.execute();
		}
	}
	
	private void generatePicture(String patternId, List<GraphEdge> edges) {
		String dot = synthesizeDot(edges);
		writePicFile(patternId, dot);
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
	        } else if (edge.getType() == ReferenceEdge.METHOD_OVERRIDE){ // METHOD_OVERRIDE
	        	result.append("color=black,style=dashed,penwidth=2,arrowsize=0.7");
	        } else { // CLASS_CONTAIN
	        	result.append("color=black,penwidth=2,arrowsize=0.7,label=\" c\",fontsize=28");
	        }
	        result.append("]\n");
		}
	    
	    result.append("\n}");
		return result.toString();
	}
	
	private void writePicFile(String index, String dot) {
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
