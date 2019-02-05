package edu.vt.cs.extraction;

import java.io.File;
import java.io.FileWriter;
import java.nio.file.FileSystems;
import java.nio.file.Path;
import java.util.List;

import org.jgrapht.Graph;

import com.ibm.wala.util.WalaException;
import com.ibm.wala.viz.DotUtil;

import edu.uci.ics.jung.graph.DirectedSparseGraph;
import edu.vt.cs.graph.ReferenceEdge;
import edu.vt.cs.graph.ReferenceNode;

/**
 * Draw PDF of JGraphT graphs with Dot
 * @author Ye Wang
 * @since 10/24/2016
 */
public class PatternDotUtil {
	
	// the location of Dot
	private final static String dotExe = "/usr/local/bin/dot";
	
	public static void main(String[] args) {
		String jungGraphLoc = "/Users/Vito/Documents/VT/2016fall/SE/grapa_results_inuse/derby/189721_DERBY-334_found/impact_2.xml";
		Path jungGraphPath = FileSystems.getDefault().getPath(jungGraphLoc);
		DirectedSparseGraph<ReferenceNode, ReferenceEdge> jungGraph = PatternExtractor.readXMLFile(jungGraphPath);
		Graph<ReferenceNode, ReferenceEdge> graph = PatternExtractor.convertJungToJGraphT(jungGraph);
		// String dotFile = "/Users/Vito/Documents/VT/2016fall/SE/temp/temp.df";
		String outputFile = "/Users/Vito/Documents/VT/2016fall/SE/temp/1234.pdf";
		dotify(graph, outputFile);
	}
	
	/**
	 * Output a PDF file for a JGraphT graph
	 * @param graph JGraphT graph
	 * @param outputFile Location of output PDF file
	 */
	public static void dotify(Graph<ReferenceNode, ReferenceEdge> graph, 
			String outputFile) {
		StringBuilder dotStringBuilder = dotOutput(graph);		
		
		// retrieve the filename parameter to this component, a String	 
		File f = null;
	    try {
			// Create a temporary file for Dot format data
	    	f = File.createTempFile("dot_data", null);
	    	// f = new File("/Users/Vito/Documents/VT/2016fall/SE/temp/temp.df");
			FileWriter fw = new FileWriter(f);
			fw.write(dotStringBuilder.toString());
			fw.close();
		} catch (Exception e) {
			e.printStackTrace();
	    }
	    
	    if (dotExe != null) {
	    	try {
				DotUtil.spawnDot(dotExe, outputFile, f);
			} catch (WalaException e) {
				e.printStackTrace();
			}
	    }
	    
	    // Delete the temporary file for Dot format data
	    f.delete();
	}
	
	public static String resolveNodeType(int t) {
		String type;
		switch (t) {
			case 0:
				type = "UNKNOWN";
				break;
			case 1:
				type = "CM";
				break;
			case 2:
				type = "AM";
				break;
			case 3:
				type = "DM";
				break;
			case 4:
				type = "AF";
				break;
			case 5:
				type = "DF";
				break;
			default:
				type = "NONE";
		}
		return type;
	}
	
	/**
	 * resolve the control/data dependency type of ReferenceEdge
	 * @param dep the int value of dependency type
	 * @return
	 */
	public static String resolveDepType(int dep) {
		String type = "";
		if ((dep & ReferenceEdge.CALLEE_CONTROL_DEP_OTHER) == ReferenceEdge.CALLEE_CONTROL_DEP_OTHER)
			type += "t<-C-;";
		if ((dep & ReferenceEdge.CALLEE_DATA_DEP_OTHER) == ReferenceEdge.CALLEE_DATA_DEP_OTHER)
			type += "t<-D-;";
		if ((dep & ReferenceEdge.OTHER_CONTROL_DEP_CALLEE) == ReferenceEdge.OTHER_CONTROL_DEP_CALLEE)
			type += "t-C->;";
		if ((dep & ReferenceEdge.OTHER_DATA_DEP_CALLEE) == ReferenceEdge.OTHER_DATA_DEP_CALLEE)
			type += "t-D->;";
		return type;
	}
	
	/**
	 * generate the file that Dot needs
	 * @param g JGraphT graph
	 * @return StringBuffer of Dot format
	 */
	public static StringBuilder dotOutput(Graph<ReferenceNode, ReferenceEdge> g) {
		int fontSize = 6;
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
	    
	    for (ReferenceNode vertex: g.vertexSet()) {
	    	 result.append("   ");
	    	 result.append("\"");
	    	 result.append(resolveNodeType(vertex.type) + " " + vertex.toString());//label contains simple representation of each node
	    	 result.append("\"");
	    	 result.append(" [ ]\n");
	    }
	
		for (ReferenceEdge edge: g.edgeSet()) {
			result.append(" ");
    		result.append("\"" + resolveNodeType(g.getEdgeSource(edge).type) + " " + g.getEdgeSource(edge).toString() + "\"");
	        result.append(" -> ");
	        result.append("\"" + resolveNodeType(g.getEdgeTarget(edge).type) + " " + g.getEdgeTarget(edge).toString() + "\"");
	        result.append(" [");
	        if (edge.type == ReferenceEdge.FIELD_ACCESS) {
	        	result.append("color=red");
	        } else if (edge.type == ReferenceEdge.METHOD_INVOKE){ // edgeType is CONTROL_FLOW
	        	result.append("color=blue");
	        } else { // METHOD_OVERRIDE
	        	result.append("color=yellow");
	        }
	        String dep = resolveDepType(edge.dep);
	        if (!dep.equals(""))
	        	result.append(",label=\"" + dep + "\"");
	        result.append("]\n");
		}
	    
	    result.append("\n}");
		return result;
	}
	
//	public static StringBuilder dotOutput(List<Graph<ReferenceNode, ReferenceEdge> > graphs) {
//		StringBuilder result = new StringBuilder();
//		for (Graph<ReferenceNode, ReferenceEdge> graph: graphs) {
//			result.append(dotOutput(graph));
//		}
//		return result;
//	}
}
