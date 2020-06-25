package partial.code.grapa.tool;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Hashtable;
import java.util.Iterator;

import partial.code.grapa.delta.graph.data.AbstractNode;
import partial.code.grapa.delta.graph.data.Connector;
import partial.code.grapa.delta.graph.data.Edge;
import partial.code.grapa.delta.graph.data.GetInst;
import partial.code.grapa.delta.graph.data.MethodInvoc;
import partial.code.grapa.delta.graph.data.NewInst;
import partial.code.grapa.delta.graph.data.PutInst;
import partial.code.grapa.dependency.graph.DeltaGraphDecorator;
import partial.code.grapa.dependency.graph.DependencyGraphDotUtil;
import partial.code.grapa.dependency.graph.DfgNodeDecorator;
import partial.code.grapa.dependency.graph.SDGwithPredicate;
import partial.code.grapa.dependency.graph.StatementEdge;
import partial.code.grapa.dependency.graph.StatementNode;

import com.ibm.wala.cast.ir.ssa.AstAssertInstruction;
import com.ibm.wala.cast.java.ssa.AstJavaInvokeInstruction;
import com.ibm.wala.examples.drivers.PDFTypeHierarchy;
import com.ibm.wala.ipa.slicer.NormalStatement;
import com.ibm.wala.ipa.slicer.Statement;
import com.ibm.wala.ipa.slicer.Slicer.ControlDependenceOptions;
import com.ibm.wala.ipa.slicer.Slicer.DataDependenceOptions;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.SSAArrayStoreInstruction;
import com.ibm.wala.ssa.SSABinaryOpInstruction;
import com.ibm.wala.ssa.SSACheckCastInstruction;
import com.ibm.wala.ssa.SSAConditionalBranchInstruction;
import com.ibm.wala.ssa.SSAGetInstruction;
import com.ibm.wala.ssa.SSAGotoInstruction;
import com.ibm.wala.ssa.SSAInstanceofInstruction;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSANewInstruction;
import com.ibm.wala.ssa.SSAPutInstruction;
import com.ibm.wala.ssa.SSAUnaryOpInstruction;
import com.ibm.wala.types.TypeReference;
import com.ibm.wala.util.WalaException;
import com.thoughtworks.xstream.XStream;
import com.thoughtworks.xstream.io.xml.StaxDriver;

import edu.uci.ics.jung.graph.DirectedSparseGraph;

public class GraphUtil {
	public static String dotExe = "e:/Program Files (x86)/Graphviz2.38/bin/dot.exe";	
	
	public static DirectedSparseGraph<StatementNode, StatementEdge> translateToJungGraph(
			SDGwithPredicate flowGraph) {
		// TODO Auto-generated method stub
		if(flowGraph == null){
			return null;
		}
		DirectedSparseGraph<StatementNode, StatementEdge> graph = new DirectedSparseGraph<StatementNode, StatementEdge>(); 
		Hashtable<Statement, StatementNode> table = new Hashtable<Statement, StatementNode>();
		Iterator<Statement> it = flowGraph.iterator();
		while(it.hasNext()){
			Statement statement = it.next();
			StatementNode node = new StatementNode(statement);
			table.put(statement, node);
			graph.addVertex(node);
		}
		
		flowGraph.reConstruct(DataDependenceOptions.NO_BASE_NO_EXCEPTIONS, ControlDependenceOptions.NONE);
		it = flowGraph.iterator();
		while(it.hasNext()){
			Statement s1 = it.next();
		
			Iterator<Statement> nodes = flowGraph.getSuccNodes(s1);
			while(nodes.hasNext()){
				Statement s2 = nodes.next();
				StatementNode from = table.get(s1);
				StatementNode to = table.get(s2);
				graph.addEdge(new StatementEdge(from, to, StatementEdge.DATA_FLOW), from, to);
			}
		}
		
		flowGraph.reConstruct(DataDependenceOptions.NONE, ControlDependenceOptions.FULL);
		it = flowGraph.iterator();
		while(it.hasNext()){
			Statement s1 = it.next();
			Iterator<Statement> nodes = flowGraph.getSuccNodes(s1);
			while(nodes.hasNext()){
				Statement s2 = nodes.next();
				StatementNode from = table.get(s1);
				StatementNode to = table.get(s2);
				StatementEdge edge = graph.findEdge(from, to);
				if(edge==null){
					graph.addEdge(new StatementEdge(from, to, StatementEdge.CONTROL_FLOW), from, to);
				}
			}
		}
		return graph;
	}
	
	public static void writeGraphXMLFile(
			DirectedSparseGraph<StatementNode, StatementEdge> graph,
			IR ir, String filename) {
		// TODO Auto-generated method stub
		String xmlFile = filename + ".xml";
		xmlFile = xmlFile.replaceAll("<", "");
		xmlFile = xmlFile.replaceAll(">", "");
		DirectedSparseGraph<AbstractNode, Edge> g = translateGraphToXMLGraph(graph, ir);
		XStream xstream = new XStream(new StaxDriver());
		 try{
			 File file = new File(xmlFile);
			 FileWriter writer=new FileWriter(file);
			 String content = xstream.toXML(g);
			 writer.write(content);
			 writer.close();
		 } catch (IOException e){
			 e.printStackTrace();
		 }
	}
	
	public static DirectedSparseGraph<AbstractNode, Edge> translateGraphToXMLGraph(
			DirectedSparseGraph<StatementNode, StatementEdge> graph, IR ir) {
		// TODO Auto-generated method stub
		DirectedSparseGraph<AbstractNode, Edge> g = new DirectedSparseGraph<AbstractNode, Edge>(); 
		Hashtable<StatementNode, AbstractNode> table = new Hashtable<StatementNode, AbstractNode>();
		for(StatementNode sn:graph.getVertices()){
			if(sn.statement instanceof NormalStatement){
				NormalStatement ns = (NormalStatement)sn.statement;
				SSAInstruction ins = ns.getInstruction();
				if(ins instanceof AstJavaInvokeInstruction){
					  AstJavaInvokeInstruction aji = (AstJavaInvokeInstruction)ins;
					  MethodInvoc method = new MethodInvoc(aji, sn.side);
					  table.put(sn, method);
					  g.addVertex(method);
				  }else if (ins instanceof SSANewInstruction){
					  SSANewInstruction nis = (SSANewInstruction)ins;
					  NewInst method = new NewInst(nis, sn.side);
					  table.put(sn, method);
					  g.addVertex(method);
				  }else if(ins instanceof SSAPutInstruction){
					  SSAPutInstruction pis = (SSAPutInstruction)ins;
					  PutInst put = new PutInst(pis, ir, sn.side);
					  table.put(sn, put);
					  g.addVertex(put);					
				  }else if(ins instanceof SSAGetInstruction){
					  SSAGetInstruction gis = (SSAGetInstruction)ins;
					  GetInst put = new GetInst(gis, ir, sn.side);
					  table.put(sn, put);
					  g.addVertex(put);
				  }else if(ins instanceof SSABinaryOpInstruction){
					  SSABinaryOpInstruction ois = (SSABinaryOpInstruction)ins;
					  String line = "binaryop(" + ois.getOperator() + ") ";
					  Connector connector = new Connector("SSABinaryOpInstruction", line, sn.side);
					  table.put(sn, connector);
					  g.addVertex(connector);
				  }else if(ins instanceof SSAArrayStoreInstruction){
					  Connector connector = new Connector("SSAArrayStoreInstruction", "arraystore", sn.side);
					  table.put(sn, connector);
					  g.addVertex(connector);
				  }else if(ins instanceof SSAUnaryOpInstruction){
					  SSAUnaryOpInstruction uoi = (SSAUnaryOpInstruction)ins;
					  String line = uoi.getOpcode().toString();
					  Connector connector = new Connector("SSAUnaryOpInstruction", line, sn.side);
					  table.put(sn, connector);
					  g.addVertex(connector);
				  }else if(ins instanceof SSAGotoInstruction){
					  String line = ins.toString();
					  Connector connector = new Connector("SSAGotoInstruction", line, sn.side);
					  table.put(sn, connector);
					  g.addVertex(connector);
				  }else if(ins instanceof AstAssertInstruction){
					  String line = "assert"; 
					  Connector connector = new Connector("AstAssertInstruction", line, sn.side);
					  table.put(sn, connector);
					  g.addVertex(connector);
				  }else if(ins instanceof SSAConditionalBranchInstruction){
					  SSAConditionalBranchInstruction cbi = (SSAConditionalBranchInstruction)ins;
					  String line = cbi.toString(ir.getSymbolTable());
					  Connector connector = new Connector("SSAConditionalBranchInstruction", line, sn.side);
					  table.put(sn, connector);
					  g.addVertex(connector);
				  }else if(ins instanceof SSAInstanceofInstruction){
					  SSAInstanceofInstruction iis = (SSAInstanceofInstruction)ins;
					  String line = "instanceof " + iis.getCheckedType();
					  Connector connector = new Connector("SSAInstanceofInstruction", line, sn.side);
					  table.put(sn, connector);
					  g.addVertex(connector);
				  }else if(ins instanceof SSACheckCastInstruction){
					  SSACheckCastInstruction cci = (SSACheckCastInstruction)ins;
					  String line = "checkcast";
				      for (TypeReference t : cci.getDeclaredResultTypes()) {
				          line = line + " " + t;
				      }
				      Connector connector = new Connector("SSACheckCastInstruction", line, sn.side);
					  table.put(sn, connector);
					  g.addVertex(connector);
				  }else{
					  Connector connector = new Connector(sn.statement.getClass().getName(), sn.statement.toString(), sn.side);
					  table.put(sn, connector);
					  g.addVertex(connector);
				  }
			}else{
				Connector connector = new Connector(sn.statement.getClass().getName(), sn.statement.toString(), sn.side);
				table.put(sn, connector);
				g.addVertex(connector);
			}
		}

		for(StatementEdge edge:graph.getEdges()){
			AbstractNode from = table.get(edge.from);
			AbstractNode to = table.get(edge.to);
			Edge e = new Edge(from, to, edge.type);
			g.addEdge(e, from, to);
		}
		return g;
	}
	
	public static void writePdfSDGraph(
			DirectedSparseGraph<StatementNode, StatementEdge> graph,IR ir, 
			String filename) {
		// TODO Auto-generated method stub
		String psFile = filename + ".pdf";
		psFile = psFile.replaceAll("<", "");
		psFile = psFile.replaceAll(">", "");

		DfgNodeDecorator decorator = new DfgNodeDecorator(ir);
		try {
			SdgDotUtil.dotify(graph, decorator, PDFTypeHierarchy.DOT_FILE, psFile , dotExe );
		} catch (WalaException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	
	public static void writePdfDeltaGraph(
			DirectedSparseGraph<StatementNode, StatementEdge> graph, IR lir,
			IR rir, String filename) {
		String psFile =  filename + ".pdf";
		psFile = psFile.replaceAll("<", "");
		psFile = psFile.replaceAll(">", "");
		
		DeltaGraphDecorator decorator = new DeltaGraphDecorator(lir,rir);
		try {
			DependencyGraphDotUtil.dotify(graph, decorator, PDFTypeHierarchy.DOT_FILE, psFile , dotExe);
		} catch (WalaException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	
	public static void writeDeltaGraphXMLFile(
			DirectedSparseGraph<StatementNode, StatementEdge> graph,
			IR lir,
			IR rir,
			String filename) {
		String xmlFile = filename + ".xml";
		xmlFile = xmlFile.replaceAll("<", "");
		xmlFile = xmlFile.replaceAll(">", "");
		DirectedSparseGraph<AbstractNode, Edge> g = translateDeltaGraphToXMLGraph(graph, lir, rir);
		XStream xstream = new XStream(new StaxDriver());
		 try{
			 File file = new File(xmlFile);
			 FileWriter writer=new FileWriter(file);
			 String content = xstream.toXML(g);
			 writer.write(content);
			 writer.close();
		 } catch (IOException e){
			 e.printStackTrace();
		 }
	}
	
	public static DirectedSparseGraph<AbstractNode, Edge> translateDeltaGraphToXMLGraph(
			DirectedSparseGraph<StatementNode, StatementEdge> graph, IR lir, IR rir) {
		// TODO Auto-generated method stub
		
		DirectedSparseGraph<AbstractNode, Edge> g = new DirectedSparseGraph<AbstractNode, Edge>(); 
		Hashtable<StatementNode, AbstractNode> table = new Hashtable<StatementNode, AbstractNode>();
		for(StatementNode sn:graph.getVertices()){
			if(sn.statement instanceof NormalStatement){
				NormalStatement ns = (NormalStatement)sn.statement;
				SSAInstruction ins = ns.getInstruction();
				if(ins instanceof AstJavaInvokeInstruction){
					  AstJavaInvokeInstruction aji = (AstJavaInvokeInstruction)ins;
					  MethodInvoc method = new MethodInvoc(aji, sn.side);
					  table.put(sn, method);
					  g.addVertex(method);
				  }else if (ins instanceof SSANewInstruction){
					  SSANewInstruction nis = (SSANewInstruction)ins;
					  NewInst method = new NewInst(nis, sn.side);
					  table.put(sn, method);
					  g.addVertex(method);
				  }else if(ins instanceof SSAPutInstruction){
					  SSAPutInstruction pis = (SSAPutInstruction)ins;
					  IR ir = null;
					  if(sn.side == StatementNode.LEFT){
					  	  ir = lir;
					  }else{
						  ir = rir;
					  }
					  PutInst put = new PutInst(pis, ir, sn.side);
					  table.put(sn, put);
					  g.addVertex(put);
					
				  }else if(ins instanceof SSAGetInstruction){
					  SSAGetInstruction gis = (SSAGetInstruction)ins;
					  IR ir = null;
					  if(sn.side == StatementNode.LEFT){
					  	  ir = lir;
					  }else{
						  ir = rir;
					  }
					  GetInst put = new GetInst(gis, ir, sn.side);
					  table.put(sn, put);
					  g.addVertex(put);
				  }else if(ins instanceof SSABinaryOpInstruction){
					  SSABinaryOpInstruction ois = (SSABinaryOpInstruction)ins;
					  String line = "binaryop(" + ois.getOperator() + ") ";
					  Connector connector = new Connector("SSABinaryOpInstruction", line, sn.side);
					  table.put(sn, connector);
					  g.addVertex(connector);
				  }else if(ins instanceof SSAArrayStoreInstruction){
					  Connector connector = new Connector("SSAArrayStoreInstruction", "arraystore", sn.side);
					  table.put(sn, connector);
					  g.addVertex(connector);
				  }else if(ins instanceof SSAUnaryOpInstruction){
					  SSAUnaryOpInstruction uoi = (SSAUnaryOpInstruction)ins;
					  String line = uoi.getOpcode().toString();
					  Connector connector = new Connector("SSAUnaryOpInstruction", line, sn.side);
					  table.put(sn, connector);
					  g.addVertex(connector);
				  }else if(ins instanceof SSAGotoInstruction){
					  String line = ins.toString();
					  Connector connector = new Connector("SSAGotoInstruction", line, sn.side);
					  table.put(sn, connector);
					  g.addVertex(connector);
				  }else if(ins instanceof AstAssertInstruction){
					  String line = "assert"; 
					  Connector connector = new Connector("AstAssertInstruction", line, sn.side);
					  table.put(sn, connector);
					  g.addVertex(connector);
				  }else if(ins instanceof SSAConditionalBranchInstruction){
					  SSAConditionalBranchInstruction cbi = (SSAConditionalBranchInstruction)ins;
					  IR ir = null;
					  if(sn.side == StatementNode.LEFT){
					  	  ir = lir;
					  }else{
						  ir = rir;
					  }
					  String line = cbi.toString(ir.getSymbolTable());
					  Connector connector = new Connector("SSAConditionalBranchInstruction", line, sn.side);
					  table.put(sn, connector);
					  g.addVertex(connector);
				  }else if(ins instanceof SSAInstanceofInstruction){
					  SSAInstanceofInstruction iis = (SSAInstanceofInstruction)ins;
					  String line = "instanceof " + iis.getCheckedType();
					  Connector connector = new Connector("SSAInstanceofInstruction", line, sn.side);
					  table.put(sn, connector);
					  g.addVertex(connector);
				  }else if(ins instanceof SSACheckCastInstruction){
					  SSACheckCastInstruction cci = (SSACheckCastInstruction)ins;
					  String line = "checkcast";
				      for (TypeReference t : cci.getDeclaredResultTypes()) {
				          line = line + " " + t;
				      }
				      Connector connector = new Connector("SSACheckCastInstruction", line, sn.side);
					  table.put(sn, connector);
					  g.addVertex(connector);
				  }else{
					  Connector connector = new Connector(sn.statement.getClass().getName(), sn.statement.toString(), sn.side);
					  table.put(sn, connector);
					  g.addVertex(connector);
				  }
			}else{
				Connector connector = new Connector(sn.statement.getClass().getName(), sn.statement.toString(), sn.side);
				table.put(sn, connector);
				g.addVertex(connector);
			}
		}

		for(StatementEdge edge:graph.getEdges()){
			AbstractNode from = table.get(edge.from);
			AbstractNode to = table.get(edge.to);
			Edge e = new Edge(from, to, edge.type);
			g.addEdge(e, from, to);
		}
		return g;
	}

}
