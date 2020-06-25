package edu.vt.cs.graph;

import java.io.File;
import java.io.FileWriter;
import java.util.Iterator;

import partial.code.grapa.delta.graph.data.AbstractNode;
import partial.code.grapa.delta.graph.data.Edge;

import com.ibm.wala.util.WalaException;
import com.ibm.wala.viz.DotUtil;

import edu.uci.ics.jung.graph.DirectedSparseGraph;

public class ChangeGraphDotUtil {
	public static void dotify(DirectedSparseGraph<ReferenceNode, ReferenceEdge> g, 
			String dotFile, String outputFile, String dotExe) {
		StringBuffer dotStringBuffer = dotOutput(g);
		
		// retrieve the filename parameter to this component, a String	 
		File f = null;
	    try {
	    	 if (dotFile == null) {
	   	      	throw new WalaException("internal error: null filename parameter");
	   	      }
		      f = new File(dotFile);
		      FileWriter fw = new FileWriter(f);
		      fw.write(dotStringBuffer.toString());
		      fw.close();
		} catch (Exception e) {
		      e.printStackTrace();
	    }
	    
	    if (dotExe != null) {
	    	try {
				DotUtil.spawnDot(dotExe, outputFile, f);
			} catch (WalaException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
	    }
	}
	
	public static StringBuffer dotOutput(DirectedSparseGraph<ReferenceNode, ReferenceEdge> g) {
		int fontSize = 6;
		String fontColor = "black";
		String fontName = "Arial";
		StringBuffer result = new StringBuffer("digraph \"DirectedRelationGraph\" {\n");
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
	    
	    for (Iterator<ReferenceNode> it = g.getVertices().iterator(); it.hasNext();) {
	    	 result.append("   ");
	    	 result.append("\"");
	    	 result.append(it.next().toString());//label contains simple representation of each node
	    	 result.append("\"");
	    	 result.append(" [ ]\n");
	    }
	    
	    for(ReferenceNode an : g.getVertices()) {
	    	for (ReferenceNode an2 : g.getSuccessors(an)) {	    		
	    		result.append(" ");
	    		result.append("\"" + an.toString() + "\"");
    	        result.append(" -> ");
    	        result.append("\"" + an2.toString() + "\"");
    	        ReferenceEdge e = g.findEdge(an, an2);
    	        if (e.type == ReferenceEdge.FIELD_ACCESS) {
    	        	result.append(" [color=red]\n");
    	        } else { // edgeType is CONTROL_FLOW
    	        	result.append(" [color=blue]\n");    	        	
    	        }    	      
	    	}
	    }
	    
	    result.append("\n}");
		return result;
	}
}
