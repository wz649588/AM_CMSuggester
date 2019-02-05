package edu.vt.cs.changes.api;

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
import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.slicer.GetCaughtExceptionStatement;
import com.ibm.wala.ipa.slicer.PDG;
import com.ibm.wala.ipa.slicer.PhiStatement;
import com.ibm.wala.ipa.slicer.SDG;
import com.ibm.wala.ipa.slicer.Statement;
import com.ibm.wala.ipa.slicer.StatementWithInstructionIndex;
import com.ibm.wala.ipa.slicer.Slicer.ControlDependenceOptions;
import com.ibm.wala.ipa.slicer.Slicer.DataDependenceOptions;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.ISSABasicBlock;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SymbolTable;
import com.ibm.wala.ssa.Value;
import com.thoughtworks.xstream.XStream;
import com.thoughtworks.xstream.io.xml.StaxDriver;

import edu.uci.ics.jung.graph.DirectedSparseGraph;
import edu.vt.cs.diffparser.util.SourceCodeRange;
import edu.vt.cs.graph.ClassRangeKey;
import edu.vt.cs.graph.LineMapper;
import edu.vt.cs.graph.SourceMapper;
import partial.code.grapa.delta.graph.data.AbstractNode;
import partial.code.grapa.delta.graph.data.Edge;
import partial.code.grapa.dependency.graph.StatementEdge;
import partial.code.grapa.dependency.graph.StatementNode;
import partial.code.grapa.mapping.ClientMethod;

//added by nameng: Modified from GraphConvertor to instantiate the functionality (public static=>public)
public class GraphConvertor2 {
	SDG g = null;
	IR ir = null;	
	ClientMethod mClient = null;
	LineMapper lineMapper = null;
	CompilationUnit cu = null;
	private Map<Integer, List<Integer>> lineToIndexes = null;
	private ConcreteJavaMethod method = null;
	private String className = null;
	private Map<Integer, Integer> indexToLine = null;
	private ValueConvertor vc = null;
	Map<Integer, DefUseFact> summary = null;
	
	public void init(IR ir, SDG g, ClientMethod mClient, LineMapper lineMapper, CompilationUnit cu) {
		this.ir = ir;
		this.g = g;
		Set<CGNode> cgNodes = g.getCallGraph().getNodes(mClient.mRef);
		if (cgNodes.size() > 1 || cgNodes.size() == 0) {
			System.err.println("Need more process");
		}
		CGNode cgNode = cgNodes.iterator().next();
		PDG pdg = g.getPDG(cgNode);
		this.mClient = mClient;
		this.cu = cu;
		this.lineMapper = lineMapper;
		
		int index = -1;
		List<ASTNode> coveredStatements = null;
	
		lineToIndexes = new HashMap<Integer, List<Integer>>();
		indexToLine = new HashMap<Integer, Integer>();
		method = null;
		className = null;
		summary = new HashMap<Integer, DefUseFact>();

		vc = new ValueConvertor(ir);
	
		Statement statement = null;
		Iterator<Statement> it = pdg.iterator();
		statement = it.next();
		method = (ConcreteJavaMethod)statement.getNode().getMethod();
		className = method.getDeclaringClass().getName().toString();	
		
		SSAInstruction inst = null;
		it = pdg.iterator();
		while(it.hasNext()) {
			statement = it.next();			
			int src_line_number = 0;				
			// this includes ExceptionalReturnCaller, NormalReturnCaller, NormalStatement, and ParamCaller
			if (statement instanceof StatementWithInstructionIndex) {
				StatementWithInstructionIndex s = (StatementWithInstructionIndex)statement;				
				index = s.getInstructionIndex();
				inst = s.getInstruction();				
			} else if (statement instanceof GetCaughtExceptionStatement) {
				GetCaughtExceptionStatement s = (GetCaughtExceptionStatement)statement;
				index = s.getInstruction().iindex;
				inst = s.getInstruction();
			} else {//this includes METHOD_ENTRY/EXIT, PARAM_CALLEE, NORMAL_RET_CALLEE, PhiStatement
				continue;
			}	
			String defStr = null;
			
			vc.convert(index, inst.getDef());
			List<String> useStrs = new ArrayList<String>();				
			for (int i = 0; i < inst.getNumberOfUses(); i++) {
				useStrs.add(vc.convert(index, inst.getUse(i)));
			}
			summary.put(index, new DefUseFact(defStr, useStrs));
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
		} 
		
//		g.reConstruct(DataDependenceOptions.NONE, ControlDependenceOptions.FULL);		
//		it = g.iterator();
//		while (it.hasNext()) {
//			Statement s1 = it.next();		
//			Iterator<Statement> nodes = g.getSuccNodes(s1);			
//			while(nodes.hasNext()){
//				
//			}
//		}
		
//		g.reConstruct(DataDependenceOptions.NONE, ControlDependenceOptions.FULL);
//		it = g.iterator();
//		while(it.hasNext()){
//			Statement s1 = it.next();
//			Iterator<Statement> nodes = g.getSuccNodes(s1);
//			while(nodes.hasNext()){
//				Statement s2 = nodes.next();
//				
//			}
//		}
	}
	
	public List<Integer> getInstIndexes(int line) {
		return lineToIndexes.get(line);
	}
	
	public Subgraph getSubgraph(List<ISSABasicBlock> blocks) {
		int fIndex = -1, lIndex = -1;
		Subgraph sg = new Subgraph();
//		DefUseFact f = null;
//		SNode defSn = null;
//		SNode useSn = null;
//		for (ISSABasicBlock b : blocks) {
//			fIndex = b.getFirstInstructionIndex();
//			lIndex = b.getLastInstructionIndex();
//			for (int i = fIndex; i <= lIndex; i++) {
//				f = summary.get(i);
//				defSn = new SNode(f.def);
//				if (!sg.containsVertex(defSn)) {
//					sg.addVertex(defSn);
//				}			
//				for (int j = 0; j < f.uses.size(); j++) {
//					useSn = new SNode(f.uses.get(j));
//					if (!sg.containsVertex(useSn)) {
//						sg.addVertex(useSn);
//						sg.addEdge(new SEdge(i, j), useSn, defSn);						
//					}
//				}				
//			}			
//		}
		return sg;
	}
	
	public class DefUseFact {
	    String def;
	    List<String> uses;
	    public DefUseFact(String def, List<String> uses) {
	    	this.def = def;
	    	this.uses = uses;
	    }
	}
}

   
