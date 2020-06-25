package partial.code.grapa.tool;

import java.io.BufferedInputStream;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Iterator;






















import partial.code.grapa.dependency.graph.SDGwithPredicate;
import partial.code.grapa.dependency.graph.StatementEdge;
import partial.code.grapa.dependency.graph.StatementNode;

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
import com.ibm.wala.viz.NodeDecorator;

import edu.uci.ics.jung.graph.DirectedSparseGraph;

/**
 * utilities for interfacing with DOT
 */
public class SdgDotUtil {

  /**
   * possible output formats for dot
   * 
   */
  public static enum DotOutputType {
    PS, SVG, PDF, EPS
  }

  private static DotOutputType outputType = DotOutputType.PDF;
  
  private static int fontSize = 6;
  private static String fontColor = "black";
  private static String fontName = "Arial";

  public static void setOutputType(DotOutputType outType) {
    outputType = outType;
  }

  public static DotOutputType getOutputType() {
    return outputType;
  }

  private static String outputTypeCmdLineParam() {
    switch (outputType) {
    case PS:
      return "-Tps";
    case EPS:
      return "-Teps";
    case SVG:
      return "-Tsvg";
    case PDF:
      return "-Tpdf";
    default:
      Assertions.UNREACHABLE();
      return null;
    }
  }

  /**
   * Some versions of dot appear to croak on long labels. Reduce this if so.
   */
  private final static int MAX_LABEL_LENGTH = Integer.MAX_VALUE;


  /**
   * @param  the type of a graph node
   */
  public static  void dotify(SDGwithPredicate graph, NodeDecorator labels, String dotFile, String outputFile, String dotExe)
    throws WalaException {
    dotify(graph, labels, null, dotFile, outputFile, dotExe);
  }

  /**
   * @param  the type of a graph node
   */
  public static  void dotify(SDGwithPredicate graph, NodeDecorator labels, String title, String dotFile, String outputFile, String dotExe)
      throws WalaException {
    if (graph == null) {
      throw new IllegalArgumentException("g is null");
    }
    File f = SdgDotUtil.writeDotFile(graph, labels, title, dotFile);
    if (dotExe != null) {
      spawnDot(dotExe, outputFile, f);
    }
  }

  public static void dotify(
			DirectedSparseGraph<StatementNode, StatementEdge> graph, NodeDecorator decorator,
			String dotFile, String outputFile, String dotExe) throws WalaException {
	// TODO Auto-generated method stub
	if (graph == null) {
      throw new IllegalArgumentException("g is null");
    }
	
    File f = SdgDotUtil.writeDotFile(graph, decorator, dotFile);
    if (dotExe != null) {
      spawnDot(dotExe, outputFile, f);
    }
  }
  
 

public static void spawnDot(String dotExe, String outputFile, File dotFile) throws WalaException {
    if (dotFile == null) {
      throw new IllegalArgumentException("dotFile is null");
    }
    String[] cmdarray = { dotExe, outputTypeCmdLineParam(), "-o", outputFile, "-v", dotFile.getAbsolutePath() };
    System.out.println("spawning process " + Arrays.toString(cmdarray));
    BufferedInputStream output = null;
    BufferedInputStream error = null;
    try {
      Process p = Runtime.getRuntime().exec(cmdarray);
      output = new BufferedInputStream(p.getInputStream());
      error = new BufferedInputStream(p.getErrorStream());
      boolean repeat = true;
      while (repeat) {
        try {
          Thread.sleep(500);
        } catch (InterruptedException e1) {
          e1.printStackTrace();
          // just ignore and continue
        }
        if (output.available() > 0) {
          byte[] data = new byte[output.available()];
          int nRead = output.read(data);
          System.err.println("read " + nRead + " bytes from output stream");
        }
        if (error.available() > 0) {
          byte[] data = new byte[error.available()];
          int nRead = error.read(data);
          System.err.println("read " + nRead + " bytes from error stream");
        }
        try {
          p.exitValue();
          // if we get here, the process has terminated
          repeat = false;
          System.out.println("process terminated with exit code " + p.exitValue());
        } catch (IllegalThreadStateException e) {
          // this means the process has not yet terminated.
          repeat = true;
        }
      }
    } catch (IOException e) {
      e.printStackTrace();
      throw new WalaException("IOException in " + SdgDotUtil.class);
    } finally {
      if (output != null) {
        try {
          output.close();
        } catch (IOException e) {
          e.printStackTrace();
        }
      }
      if (error != null) {
        try {
          error.close();
        } catch (IOException e) {
          e.printStackTrace();
        }
      }
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
	


public static  File writeDotFile(SDGwithPredicate graph, NodeDecorator labels, String title, String dotfile) throws WalaException {

    if (graph == null) {
      throw new IllegalArgumentException("g is null");
    }
    StringBuffer dotStringBuffer = dotOutput(graph, labels, title);
  
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

		
		    outputNodes(labels, result, graph.getVertices());

		    
		    boolean bDiff = true;
		    
	    	for (StatementNode fn:graph.getVertices()) {
//	    		  Statement fs = fn.statement;
	    	      for (StatementNode tn:graph.getSuccessors(fn)) {
//	    	    	Statement ts = tn.statement;
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
			
		    result.append("\n}");
		    return result;
	}
	
	
	
  /**
   * @return StringBuffer holding dot output representing G
   * @throws WalaException
   */
  private static  StringBuffer dotOutput(SDGwithPredicate graph, NodeDecorator labels, String title) throws WalaException {
    StringBuffer result = new StringBuffer("digraph \"DirectedSDG\" {\n");

    if (title != null) {
      result.append("graph [label = \""+title+"\", labelloc=t, concentrate = true];");
    } else {
      result.append("graph [concentrate = true];");
    }
    
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

    Collection dotNodes = computeDotNodes(graph);

    outputNodes(labels, result, dotNodes);

    
    boolean bDiff = true;
    if(bDiff){
    	//dataflow
    	graph.reConstruct(DataDependenceOptions.FULL, ControlDependenceOptions.NONE);
    	for (Iterator<Statement> it = graph.iterator(); it.hasNext();) {
    		  Statement n = it.next();
    	      for (Iterator<Statement> it2 = graph.getSuccNodes(n); it2.hasNext();) {
    	    	Statement s = it2.next();
    	        result.append(" ");
    	        result.append(getPort(n, labels));
    	        result.append(" -> ");
    	        result.append(getPort(s, labels));
    	        result.append(" [color=red]\n");
    	      }
    	 }
		
		//controlflow
    	graph.reConstruct(DataDependenceOptions.NONE, ControlDependenceOptions.FULL);
    	for (Iterator<Statement> it = graph.iterator(); it.hasNext();) {
    		  Statement n = it.next();
    	      for (Iterator<Statement> it2 = graph.getSuccNodes(n); it2.hasNext();) {
    	    	Statement s = it2.next();
    	        result.append(" ");
    	        result.append(getPort(n, labels));
    	        result.append(" -> ");
    	        result.append(getPort(s, labels));
    	        result.append(" \n");
    	      }
    	}
    }else{
    	for (Iterator<Statement> it = graph.iterator(); it.hasNext();) {
  		  Statement n = it.next();
  	      for (Iterator<Statement> it2 = graph.getSuccNodes(n); it2.hasNext();) {
  	    	Statement s = it2.next();
  	        result.append(" ");
  	        result.append(getPort(n, labels));
  	        result.append(" -> ");
  	        result.append(getPort(s, labels));
  	        result.append(" \n");
  	      }
  	    }
    }
    result.append("\n}");
    return result;
  }

 

private static  void outputNodes(NodeDecorator<StatementNode> labels, StringBuffer result, Collection dotNodes) throws WalaException {
    for (Iterator<StatementNode> it = dotNodes.iterator(); it.hasNext();) {
      outputNode(labels, result, it.next());
    }
  }

  private static  void outputNode(NodeDecorator<StatementNode> labels, StringBuffer result, StatementNode n) throws WalaException {
    result.append("   ");
    result.append("\"");
    result.append(getLabel(n, labels));
    result.append("\"");
    result.append(decorateNode(n, labels));
  }

  
/**
   * Compute the nodes to visualize
   */
  private static  Collection computeDotNodes(Graph<Statement> lfg) throws WalaException {
    return Iterator2Collection.toSet(lfg.iterator());
  }

  private static String getRankDir() throws WalaException {
    return null;
  }

  /**
   * @param n node to decorate
   * @param d decorating master
   */
  private static  String decorateNode(Statement n, NodeDecorator d) throws WalaException {
    StringBuffer result = new StringBuffer();
    result.append(" [ ]\n");
    return result.toString();
  }
  
  private static Object decorateNode(StatementNode n,
			NodeDecorator<StatementNode> labels) {
		// TODO Auto-generated method stub
	  StringBuffer result = new StringBuffer();
	  result.append(" [ ]\n");
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

  private static Object getPort(Statement n, NodeDecorator d) throws WalaException {
	// TODO Auto-generated method stub
	  return "\"" + getLabel(n, d) + "\"";
  }

  private static String getLabel(Statement n, NodeDecorator d) throws WalaException {
	// TODO Auto-generated method stub
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

  public static int getFontSize() {
    return fontSize;
  }

  public static void setFontSize(int fontSize) {
    SdgDotUtil.fontSize = fontSize;
  }


}
