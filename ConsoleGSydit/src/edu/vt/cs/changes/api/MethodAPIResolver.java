package edu.vt.cs.changes.api;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.MethodDeclaration;

import com.ibm.wala.cast.java.ipa.callgraph.AstJavaZeroXCFABuilder;
import com.ibm.wala.cast.java.loader.JavaSourceLoaderImpl.ConcreteJavaMethod;
import com.ibm.wala.classLoader.IMethod;
import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.slicer.GetCaughtExceptionStatement;
import com.ibm.wala.ipa.slicer.NormalStatement;
import com.ibm.wala.ipa.slicer.PDG;
import com.ibm.wala.ipa.slicer.PhiStatement;
import com.ibm.wala.ipa.slicer.SDG;
import com.ibm.wala.ipa.slicer.Statement;
import com.ibm.wala.ipa.slicer.StatementWithInstructionIndex;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.ISSABasicBlock;
import com.ibm.wala.ssa.SSACFG.BasicBlock;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.types.MethodReference;

import ch.uzh.ifi.seal.changedistiller.model.entities.SourceCodeChange;
import ch.uzh.ifi.seal.changedistiller.model.entities.SourceCodeEntity;
import ch.uzh.ifi.seal.changedistiller.model.entities.Update;
import edu.uci.ics.jung.graph.DirectedSparseGraph;
import edu.vt.cs.append.FineChangesInMethod;
import edu.vt.cs.changes.ChangeFact;
import edu.vt.cs.changes.ChangeMethodData;
import edu.vt.cs.diffparser.util.SourceCodeRange;
import edu.vt.cs.graph.SourceMapper;
import partial.code.grapa.dependency.graph.DataFlowAnalysisEngine;
import partial.code.grapa.dependency.graph.StatementEdge;
import partial.code.grapa.dependency.graph.StatementNode;
import partial.code.grapa.mapping.ClientMethod;

public class MethodAPIResolver extends APIResolver {
	
	private Map<ClientMethod, SDG> oldSDGs = null;
	private Map<ClientMethod, SDG> newSDGs = null;
	
	private SourceMapper oldSourceMapper = null;
	private SourceMapper newSourceMapper = null;
	
	public MethodAPIResolver(DataFlowAnalysisEngine leftEngine, DataFlowAnalysisEngine rightEngine) {
		super(leftEngine, rightEngine);
		this.oldSDGs = new HashMap<ClientMethod, SDG>();
		this.newSDGs = new HashMap<ClientMethod, SDG>();
		this.oldSourceMapper = new SourceMapper();
		this.newSourceMapper = new SourceMapper();
	}
	
	public void resolve(Map<IMethodBinding, Set<ChangeFact>> missings) {
		IMethodBinding mb = null;
		Set<ChangeFact> value = null;
		Set<SourceCodeRange> ranges = null;
		GraphConvertor2 oc = new GraphConvertor2();
		GraphConvertor2 nc = new GraphConvertor2();
		SourceMapper oldMapper = new SourceMapper();
		SourceMapper newMapper = new SourceMapper();
		SubgraphComparator comparator = new SubgraphComparator();
		for (Entry<IMethodBinding, Set<ChangeFact>> entry : missings.entrySet()) {
			mb = entry.getKey();
			value = entry.getValue();
			for (ChangeFact cf : value) {
			   List<ChangeMethodData> data = cf.changedMethodData;
			   for (ChangeMethodData d : data) {				  				  
				   if (d.oldBindingMap.containsKey(mb)) {
					   ClientMethod oldMethod = d.oldMethod;
					   CompilationUnit oldCu = (CompilationUnit)oldMethod.ast;
					   if (!oldMethod.toString().contains("insert"))
						   continue;
					   SDG lfg = findOrCreateOldSDG(oldMethod);			
					   oldMapper.add(oldMethod.ast);
					   oc.init(leftEngine.getCurrentIR(), lfg,
							   oldMethod,
							   oldMapper.getLineMapper(oldCu), oldCu);   
					   
					   ClientMethod newMethod = d.newMethod;
					   CompilationUnit newCu = (CompilationUnit)newMethod.ast;
					   
					   SourceCodeEntity mEntity = cf.getEntity(SourceCodeRange.convert(oldMethod.methodbody));
					   FineChangesInMethod allChanges = (FineChangesInMethod)(cf.getChange(mEntity));
					   ranges = d.oldBindingMap.get(mb);
					   Subgraph s1 = null, s2 = null;
					   for (SourceCodeRange r : ranges) {							  
						   s1 = getSubgraph(oldCu, r, oc);
						   SourceCodeChange c = allChanges.getChange(r.converToSourceRange());
						   if (c instanceof Update) {
							   Update u = (Update)c;
							   SourceCodeRange newR = SourceCodeRange.convert(u.getNewEntity());
							   s2 = getSubgraph(newCu, newR, nc);
							   comparator.compare(s1, s2);
						   }
					   }
				   }				 
			   }
			}
		}		
	}
	
	private Subgraph getSubgraph(CompilationUnit cu, SourceCodeRange r, GraphConvertor2 c) {
		//1. convert source code range to line range
		LineRange lineRange = LineRange.get(cu, r);
		//2. convert line range to instructions
		Set<Integer> indexes = new HashSet<Integer>();
		for (int i = lineRange.startLine; i <= lineRange.endLine; i++) {
			indexes.addAll(c.getInstIndexes(i));	   
		}				
		//3. get all blocks enclosing the instructions
		List<ISSABasicBlock> blocks = getBlocks(indexes, c);
		//4. create subgraph with the blocks
		Subgraph s = c.getSubgraph(blocks);
		s.mark(indexes);
		return s;
	}
	
	private SDG findOrCreateOldSDG(ClientMethod m) {
		SDG g = oldSDGs.get(m);
		if (g == null) {
			g = leftEngine.buildSystemDependencyGraph2(m);
			oldSDGs.put(m, g);
		}
		return g;
	}
	
	private SDG findOrCreateNewSDG(ClientMethod m) {
		SDG g = newSDGs.get(m);
		if (g == null) {
			g = rightEngine.buildSystemDependencyGraph2(m);
			newSDGs.put(m, g);
		}
		return g;
	}

	private List<ISSABasicBlock> getBlocks(Set<Integer> indexes, GraphConvertor2 c) {
		IR ir = leftEngine.getCurrentIR();
		SSAInstruction[] insts = ir.getInstructions();
		ISSABasicBlock bb = null;		
		List<ISSABasicBlock> result = new ArrayList<ISSABasicBlock>();
		for (Integer i : indexes) {
			bb = ir.getBasicBlockForInstruction(insts[i]);
			result.add(bb);
 		} 			
		return result;
	}
	
	private List<Integer> getLines(CompilationUnit cu, SourceCodeRange r) {
		List<Integer> lines = new ArrayList<Integer>();
		int startLine = cu.getLineNumber(r.startPosition);
		int endLine = cu.getLineNumber(r.startPosition + r.length - 1);
		for (int i = startLine; i <= endLine; i++) {
			lines.add(i);
		}
		return lines;
	}
}
