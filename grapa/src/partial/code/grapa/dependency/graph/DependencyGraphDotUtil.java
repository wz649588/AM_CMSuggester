package partial.code.grapa.dependency.graph;

import java.io.BufferedInputStream;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Iterator;
























import com.ibm.wala.examples.drivers.PDFTypeHierarchy;
import com.ibm.wala.ipa.slicer.HeapStatement;
import com.ibm.wala.ipa.slicer.NormalStatement;
import com.ibm.wala.ipa.slicer.ParamCallee;
import com.ibm.wala.ipa.slicer.ParamCaller;
import com.ibm.wala.ipa.slicer.SDG;
import com.ibm.wala.ipa.slicer.Slicer.ControlDependenceOptions;
import com.ibm.wala.ipa.slicer.Slicer.DataDependenceOptions;
import com.ibm.wala.ipa.slicer.Statement;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.util.WalaException;
import com.ibm.wala.util.collections.Iterator2Collection;
import com.ibm.wala.util.debug.Assertions;
import com.ibm.wala.util.graph.Graph;
import com.ibm.wala.viz.DotUtil;
import com.ibm.wala.viz.NodeDecorator;

import edu.uci.ics.jung.graph.DirectedSparseGraph;

/**
 * utilities for interfacing with DOT
 */
public class DependencyGraphDotUtil extends DotUtil {

  public static void dotify(
			DirectedSparseGraph<StatementNode, StatementEdge> graph, NodeDecorator decorator,
			String dotFile, String outputFile, String dotExe) throws WalaException {
	// TODO Auto-generated method stub
	if (graph == null) {
      throw new IllegalArgumentException("g is null");
    }
	
    File f = DependencyGraphDotUtil.writeDotFile(graph, decorator, dotFile);
    if (dotExe != null) {
      spawnDot(dotExe, outputFile, f);
    }
  }

	private static File writeDotFile(
			DirectedSparseGraph<StatementNode, StatementEdge> graph, NodeDecorator labels, String dotfile) throws WalaException {
		// TODO Auto-generated method stub
		 if (graph == null) {
		      throw new IllegalArgumentException("g is null");
		    }
		    StringBuffer dotStringBuffer = dotOutput(graph, labels);
		  
		    // retrieve the filename parameter to this component, a String
		    if (dotfile == null) {
		      throw new WalaException("internal error: null filename parameter");
		    }
		    try {
		      File f = new File(dotfile);
		      FileWriter fw = new FileWriter(f);
		      fw.write(dotStringBuffer.toString());
		      fw.close();
		      return f;

		    } catch (Exception e) {
		      throw new WalaException("Error writing dot file " + dotfile);
		    }
	}

	private static StringBuffer dotOutput(
			DirectedSparseGraph<StatementNode, StatementEdge> graph,
			NodeDecorator labels) throws WalaException {
		// TODO Auto-generated method stub
		StringBuffer result = new StringBuffer("digraph \"DirectedSDG\" {\n");

		  
		result.append("graph [concentrate = true];");
		   
		    
	    String rankdir = getRankDir();
	    if (rankdir != null) {
	      result.append("rankdir=" + rankdir + ";");
	    }
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

		
	    result.append("  subgraph cluster0{\n");
	    outputNodes(labels, result, graph.getVertices(), StatementNode.LEFT);
		    
    	for (StatementNode fn:graph.getVertices()) {
    	      for (StatementNode tn:graph.getSuccessors(fn)) {
    	    	if(fn.side == StatementNode.LEFT&&tn.side == StatementNode.LEFT){  
	    	        result.append(" ");
	    	        result.append(getPort(fn, labels));
	    	        result.append(" -> ");
	    	        result.append(getPort(tn, labels));
	    	        StatementEdge edge = graph.findEdge(fn,tn);
	    	        if(edge.type==StatementEdge.DATA_FLOW){
	    	        	result.append(" [color=red]\n");
	    	        }else if(edge.type==StatementEdge.CONTROL_FLOW){
	    	        	result.append(" [color=blue]\n");
	    	        }else if(edge.type==StatementEdge.CHANGE){
	    	        	result.append(" [color=green]\n");
	    	        }else{
	    	        	result.append(" \n");
	    	        }
    	    	}
    	      }
    	 }
		 result.append("  \n}\n");
		 
		 result.append("  subgraph cluster1{\n");
		 outputNodes(labels, result, graph.getVertices(), StatementNode.RIGHT);
		 for (StatementNode fn:graph.getVertices()) {
	   	      for (StatementNode tn:graph.getSuccessors(fn)) {
		   	    	if(fn.side == StatementNode.RIGHT&&tn.side == StatementNode.RIGHT){  
			    	        result.append(" ");
			    	        result.append(getPort(fn, labels));
			    	        result.append(" -> ");
			    	        result.append(getPort(tn, labels));
			    	        StatementEdge edge = graph.findEdge(fn,tn);
			    	        if(edge.type==StatementEdge.DATA_FLOW){
			    	        	result.append(" [color=red]\n");
			    	        }else if(edge.type==StatementEdge.CONTROL_FLOW){
			    	        	result.append(" [color=blue]\n");
			    	        }else if(edge.type==StatementEdge.CHANGE){
			    	        	result.append(" [color=green]\n");
			    	        }else{
			    	        	result.append(" \n");
			    	        }
		   	    	}
	   	      }
	   	 }
		 result.append("  \n}\n");
		 for (StatementNode fn:graph.getVertices()) {
	   	      for (StatementNode tn:graph.getSuccessors(fn)) {
		   	    	if(fn.side == StatementNode.LEFT&&tn.side == StatementNode.RIGHT){  
			    	        result.append(" ");
			    	        result.append(getPort(fn, labels));
			    	        result.append(" -> ");
			    	        result.append(getPort(tn, labels));
			    	        StatementEdge edge = graph.findEdge(fn,tn);
			    	        if(edge.type==StatementEdge.DATA_FLOW){
			    	        	result.append(" [color=red]\n");
			    	        }else if(edge.type==StatementEdge.CONTROL_FLOW){
			    	        	result.append(" [color=blue]\n");
			    	        }else if(edge.type==StatementEdge.CHANGE){
			    	        	result.append(" [color=green]\n");
			    	        }else{
			    	        	result.append(" \n");
			    	        }
		   	    	}
	   	      }
	   	 }
		 result.append("\n}");
		 return result;
	}
	

	private static void outputNodes(NodeDecorator<StatementNode> labels, StringBuffer result, Collection dotNodes, int side) throws WalaException {
	    for (Iterator<StatementNode> it = dotNodes.iterator(); it.hasNext();) {
	      outputNode(labels, result, it.next(), side);
	    }
    }

	private static void outputNode(NodeDecorator<StatementNode> labels, StringBuffer result, StatementNode n, int side) throws WalaException {
	    if(n.side == side){
			result.append("   ");
		    result.append("\"");
		    result.append(getLabel(n, labels));
		    result.append("\"");
		    result.append(decorateNode(n, labels));
	    }
	}

  
  private static Object decorateNode(StatementNode n,
			NodeDecorator<StatementNode> labels) {
		// TODO Auto-generated method stub
	  StringBuffer result = new StringBuffer();
	  if(n.side == StatementNode.LEFT){
		  result.append(" [ ]\n");
	  }else{
		  result.append(" [color=red]\n");
	  }
	  return result.toString();
  }


  private static  String getLabel(StatementNode n, NodeDecorator d) throws WalaException {
    String result = null;
    if (d == null) {
      result = n.toString();
    } else {
      result = d.getLabel(n);
      result = result == null ? n.toString() : result;
    }
    if (result.length() >= MAX_LABEL_LENGTH) {
      result = result.substring(0, MAX_LABEL_LENGTH - 3) + "...";
    }
    return result;
  }

  private static  String getPort(StatementNode n, NodeDecorator d) throws WalaException {
    return "\"" + getLabel(n, d) + "\"";

  }  

}
