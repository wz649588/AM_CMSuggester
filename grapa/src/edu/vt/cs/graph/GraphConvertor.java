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
import java.util.Set;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.CompilationUnit;

import com.ibm.wala.cast.java.loader.JavaSourceLoaderImpl.ConcreteJavaMethod;
import com.ibm.wala.classLoader.IMethod;
import com.ibm.wala.examples.drivers.PDFTypeHierarchy;
import com.ibm.wala.ipa.slicer.GetCaughtExceptionStatement;
import com.ibm.wala.ipa.slicer.PhiStatement;
import com.ibm.wala.ipa.slicer.SDG;
import com.ibm.wala.ipa.slicer.Statement;
import com.ibm.wala.ipa.slicer.StatementWithInstructionIndex;
import com.ibm.wala.ipa.slicer.Slicer.ControlDependenceOptions;
import com.ibm.wala.ipa.slicer.Slicer.DataDependenceOptions;
import com.ibm.wala.ssa.IR;
import com.thoughtworks.xstream.XStream;
import com.thoughtworks.xstream.io.xml.StaxDriver;

import edu.uci.ics.jung.graph.DirectedSparseGraph;
import partial.code.grapa.delta.graph.data.AbstractNode;
import partial.code.grapa.delta.graph.data.Edge;
import partial.code.grapa.dependency.graph.StatementEdge;
import partial.code.grapa.dependency.graph.StatementNode;
import partial.code.grapa.mapping.ClientMethod;
//will be deprecated
//added by nameng: Modified from GraphUtil2 to instantiate the functionality (public static=>public)
public class GraphConvertor {

	HashMap<ClassRangeKey, StatementNode> astMap = null;
	HashMap<StatementNode, List<ASTNode>> snToAsts = null;
	HashMap<Integer, StatementNode> lineToSn = null;
	private DirectedSparseGraph<StatementNode, StatementEdge> graph;
	private String className = null;
	private ConcreteJavaMethod method = null;
	private Map<Integer, List<Integer>> lineToIndexes = null;
	private Map<Integer, Integer> indexToLine = null;
	private LineMapper lineMapper = null;
	
	public DirectedSparseGraph<StatementNode, StatementEdge> translateToJungGraph(
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
		lineToIndexes = new HashMap<Integer, List<Integer>>();
		indexToLine = new HashMap<Integer, Integer>();
		lineToSn = new HashMap<Integer, StatementNode>();
		
		graph = new DirectedSparseGraph<StatementNode, StatementEdge>();
		Hashtable<Statement, StatementNode> table = new Hashtable<Statement, StatementNode>();
		astMap = new HashMap<ClassRangeKey, StatementNode>();
		snToAsts = new HashMap<StatementNode, List<ASTNode>>();
				
		Iterator<Statement> it = flowGraph.iterator();
		int index = -1;
		StatementNode sn = null;
		List<ASTNode> coveredStatements = null;
		className = defaultClassName;
		CompilationUnit cu = null;
	
		ClassRangeKey key = null;
		while(it.hasNext()) {
			Statement statement = it.next();
			IMethod m = statement.getNode().getMethod();
			if (!(m instanceof ConcreteJavaMethod)) {
				continue;
			}
			
			method = (ConcreteJavaMethod)statement.getNode().getMethod();	
			className = method.getDeclaringClass().getName().toString();						
			
			if (className.equals(defaultClassName)) {
				cu = defaultCu;
				lineMapper = defaultMapper;
			} else {
				cu = cache.getCu(className);
				lineMapper = cache.getLineMapper(cu);
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
			List<Integer> indexes = lineToIndexes.get(src_line_number);
			if (indexes == null) {
				indexes = new ArrayList<Integer>();
				lineToIndexes.put(src_line_number, indexes);
			}
			if (!indexes.contains(index))
				indexes.add(index);
			if (!indexToLine.containsKey(index)) {
				indexToLine.put(index, src_line_number);
			}
			
			coveredStatements = lineMapper.findNodes(src_line_number);		
			if (coveredStatements == null) {
				coveredStatements = new ArrayList<ASTNode>();
				coveredStatements.add(lineMapper.findEnclosingMethod(src_line_number));
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
			lineToSn.put(src_line_number, sn);
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
	
	public List<Integer> getInstIndexes(int src_line_number) {
		return lineToIndexes.get(src_line_number);
	}
	
	public List<Integer> getSrcLines(int start, int end) {
		List<Integer> result = new ArrayList<Integer>();
		for (int i = start; i <= end; i++) {
			if (indexToLine.containsKey(i)) {
				result.add(indexToLine.get(i));
			}
		}
		return result;		
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
	
	public DirectedSparseGraph<AbstractNode, Edge> translateGraphToASTGraph(
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
