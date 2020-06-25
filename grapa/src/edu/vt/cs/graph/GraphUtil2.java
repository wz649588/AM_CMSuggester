package edu.vt.cs.graph;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Properties;
import java.util.Set;

import org.eclipse.jdt.core.SourceRange;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.CompilationUnit;

import com.ibm.wala.cast.ipa.callgraph.AstCallGraph;
import com.ibm.wala.cast.ir.ssa.AstAssertInstruction;
import com.ibm.wala.cast.java.loader.JavaSourceLoaderImpl.ConcreteJavaMethod;
import com.ibm.wala.cast.java.ssa.AstJavaInvokeInstruction;
import com.ibm.wala.classLoader.IMethod;
import com.ibm.wala.classLoader.JavaLanguage.JavaInstructionFactory;
import com.ibm.wala.examples.drivers.PDFTypeHierarchy;
import com.ibm.wala.examples.properties.WalaExamplesProperties;
import com.ibm.wala.ipa.slicer.GetCaughtExceptionStatement;
import com.ibm.wala.ipa.slicer.PhiStatement;
import com.ibm.wala.ipa.slicer.SDG;
import com.ibm.wala.ipa.slicer.Slicer.ControlDependenceOptions;
import com.ibm.wala.ipa.slicer.Slicer.DataDependenceOptions;
import com.ibm.wala.ipa.slicer.Statement;
import com.ibm.wala.ipa.slicer.StatementWithInstructionIndex;
import com.ibm.wala.properties.WalaProperties;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.SSAArrayStoreInstruction;
import com.ibm.wala.ssa.SSABinaryOpInstruction;
import com.ibm.wala.ssa.SSACheckCastInstruction;
import com.ibm.wala.ssa.SSAConditionalBranchInstruction;
import com.ibm.wala.ssa.SSAFieldAccessInstruction;
import com.ibm.wala.ssa.SSAGetInstruction;
import com.ibm.wala.ssa.SSAGotoInstruction;
import com.ibm.wala.ssa.SSAInstanceofInstruction;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSANewInstruction;
import com.ibm.wala.ssa.SSAPhiInstruction;
import com.ibm.wala.ssa.SSAPutInstruction;
import com.ibm.wala.ssa.SSAUnaryOpInstruction;
import com.ibm.wala.types.TypeReference;
import com.ibm.wala.util.WalaException;
import com.ibm.wala.util.graph.Graph;
import com.ibm.wala.viz.DotUtil;
import com.thoughtworks.xstream.XStream;
import com.thoughtworks.xstream.io.xml.StaxDriver;

import partial.code.grapa.delta.graph.data.AbstractNode;
import partial.code.grapa.delta.graph.data.Connector;
import partial.code.grapa.delta.graph.data.Edge;
import partial.code.grapa.delta.graph.data.GetInst;
import partial.code.grapa.delta.graph.data.MethodInvoc;
import partial.code.grapa.delta.graph.data.NewInst;
import partial.code.grapa.delta.graph.data.PutInst;
import partial.code.grapa.dependency.graph.SDGwithPredicate;
import partial.code.grapa.dependency.graph.StatementEdge;
import partial.code.grapa.dependency.graph.StatementNode;
import partial.code.grapa.mapping.ClientMethod;
import edu.uci.ics.jung.graph.DirectedSparseGraph;

public class GraphUtil2 {
	
	static HashMap<ClassRangeKey, StatementNode> astMap = null;
	static HashMap<StatementNode, List<ASTNode>> snToAsts = null;
	
	public static String dotExe = "/usr/local/bin/dot";
	
	//added by nameng, to establish mapping between the internal statements and AST statements
	public static DirectedSparseGraph<StatementNode, StatementEdge> translateToJungGraph(
			SDG flowGraph, ClientMethod mClient,
			SourceMapper cache,
			int side) {
		CompilationUnit defaultCu = (CompilationUnit)mClient.ast;
//		if (!mClient.methodName.contains("processCommand"))
//			return null;
//		if (flowGraph == null) 
//			return null;
		LineMapper defaultMapper = cache.getLineMapper(defaultCu);
		String defaultClassName = mClient.key;
		
		DirectedSparseGraph<StatementNode, StatementEdge> graph = new DirectedSparseGraph<StatementNode, StatementEdge>();
		Hashtable<Statement, StatementNode> table = new Hashtable<Statement, StatementNode>();
		astMap = new HashMap<ClassRangeKey, StatementNode>();
		snToAsts = new HashMap<StatementNode, List<ASTNode>>();
				
		Iterator<Statement> it = flowGraph.iterator();
		int index = -1;
		StatementNode sn = null;
		List<ASTNode> coveredStatements = null;
		String className = defaultClassName;
		CompilationUnit cu = null;
		LineMapper mapper = null;		
		ClassRangeKey key = null;
		while(it.hasNext()) {
			Statement statement = it.next();
			IMethod m = statement.getNode().getMethod();
			if (!(m instanceof ConcreteJavaMethod)) {
				continue;
			}
			
			ConcreteJavaMethod method = (ConcreteJavaMethod)statement.getNode().getMethod();	
			className = method.getDeclaringClass().getName().toString();						
			
			if (className.equals(defaultClassName)) {
				cu = defaultCu;
				mapper = defaultMapper;
			} else {
				cu = cache.getCu(className);
				mapper = cache.getLineMapper(cu);
			}							
			int src_line_number = 0;				
			// this includes ExceptionalReturnCaller, NormalReturnCaller, NormalStatement, and ParamCaller
			if (statement instanceof StatementWithInstructionIndex) {
				StatementWithInstructionIndex s = (StatementWithInstructionIndex)statement;				
				index = s.getInstructionIndex();										
			} else if (statement instanceof GetCaughtExceptionStatement) {
				GetCaughtExceptionStatement s = (GetCaughtExceptionStatement)statement;
				index = s.getInstruction().iindex;					
			} else if (statement instanceof PhiStatement) { //PhiStatement does not correspond to any ASTNode			
				sn = new StatementNode(statement);
				graph.addVertex(sn);
				sn.addStatement(statement);
				table.put(statement, sn);
				continue;
			} else {//this includes METHOD_ENTRY/EXIT, PARAM_CALLEE, NORMAL_RET_CALLEE
				continue;
			}			
			src_line_number = method.getLineNumber(index);									
			coveredStatements = mapper.findNodes(src_line_number);		
			if (coveredStatements == null) {
				coveredStatements = new ArrayList<ASTNode>();
				coveredStatements.add(mapper.findEnclosingMethod(src_line_number));
			}
			
			key = getKey(cu, coveredStatements, className);
			if (astMap.containsKey(key)) {
				sn = astMap.get(key);					
			} else {
				sn = new StatementNode(statement);
				sn.side = side;
				sn.nodes = coveredStatements;
				astMap.put(key, sn);
				snToAsts.put(sn, coveredStatements);
				graph.addVertex(sn);		
			}
			sn.addStatement(statement);
			table.put(statement, sn);	
		} 
		
		flowGraph.reConstruct(DataDependenceOptions.NONE, ControlDependenceOptions.FULL);		
		it = flowGraph.iterator();
		while (it.hasNext()) {
			Statement s1 = it.next();		
			Iterator<Statement> nodes = flowGraph.getSuccNodes(s1);			
			while(nodes.hasNext()){
				Statement s2 = nodes.next();
				StatementNode from = table.get(s1);
				StatementNode to = table.get(s2);
				if (from == null || to == null || from.equals(to)) {
					continue;
				}				
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
				if (from == null || to == null || from.equals(to)) {
					continue;
				}								
				graph.addEdge(new StatementEdge(from, to, StatementEdge.CONTROL_FLOW), from, to);
			}
		}
		return graph;
	}
	
	//Given a line number and a statement, try to find the corresponding AST
	public static ASTNode findNode(ASTNode cu, int src_line_number, Statement statement) {
		StatementNodeFinder finder = new StatementNodeFinder(cu, src_line_number, statement);
		return finder.getCoveredNode();
	}
	
	private static ClassRangeKey getKey(CompilationUnit cu, List<ASTNode> coveredStatements, 
			String typeName) {
		int minStart = Integer.MAX_VALUE;
		int maxEnd = Integer.MIN_VALUE;		
		for (ASTNode n : coveredStatements) {
			int tmpStart = n.getStartPosition();
			int tmpEnd = tmpStart + n.getLength();
			if (tmpStart < minStart) {
				minStart = tmpStart;
			}
			if (tmpEnd > maxEnd) {
				maxEnd = tmpEnd;
			}
		}		
		return new ClassRangeKey(typeName, 
				cu.getLineNumber(minStart), cu.getLineNumber(maxEnd - 1));
	}
	
	public static boolean withinScope(int src_line_number, int startLine, int endLine) {
		return src_line_number <= endLine && src_line_number >= startLine;
	}	
	
	public static void writeSDGraph(
			DirectedSparseGraph<AbstractNode, Edge> g,
			String filename) {
		String xmlFile = filename + ".xml";
		xmlFile = xmlFile.replaceAll("<", "");
		xmlFile = xmlFile.replaceAll(">", "");
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
		 
		String psFile =  filename + ".pdf";
		psFile = psFile.replaceAll("<", "");
		psFile = psFile.replaceAll(">", "");		
		
		GraphDotUtil.dotify(g, PDFTypeHierarchy.DOT_FILE, psFile, dotExe);
	}
	
	
	public static DirectedSparseGraph<AbstractNode, Edge> translateGraphToASTGraph(
			DirectedSparseGraph<StatementNode, StatementEdge> graph, IR ir) {
		// TODO Auto-generated method stub
		DirectedSparseGraph<AbstractNode, Edge> g = new DirectedSparseGraph<AbstractNode, Edge>(); 
		Hashtable<StatementNode, AbstractNode> table = new Hashtable<StatementNode, AbstractNode>();
		AbstractNode an = null;
		
		List<ASTNode> stmts = null;
		
		for(StatementNode sn:graph.getVertices()){
			stmts = snToAsts.get(sn);
			if (stmts == null) { //phi statement
				an = new PhiStatementNode(sn);				
			} else if (stmts.size() == 1) {
				an = new SingleStatementNode(stmts.get(0), sn.side);
			} else { //stmts.size() > 1
				an = new MultiStatementNode(stmts, sn.side);
			}
			g.addVertex(an);
			table.put(sn, an);
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
