package edu.vt.cs.changes;

import static java.nio.file.StandardOpenOption.*;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.lang.reflect.Field;
import java.nio.charset.Charset;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.PriorityQueue;
import java.util.Set;
import java.util.TreeMap;

import org.eclipse.core.resources.IFile;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.CompilationUnit;

import partial.code.grapa.commit.CommitComparator;
import partial.code.grapa.commit.DependenceGraph;
import partial.code.grapa.dependency.graph.DataFlowAnalysisEngine;
import partial.code.grapa.mapping.ClientMethod;
import ch.uzh.ifi.seal.changedistiller.treedifferencing.NodePair;
import ch.uzh.ifi.seal.changedistiller.treedifferencing.TreeEditOperation;

import com.google.gson.Gson;
import com.google.gson.reflect.TypeToken;
import com.ibm.wala.cast.java.loader.JavaSourceLoaderImpl.ConcreteJavaMethod;
import com.ibm.wala.cast.java.ssa.AstJavaInvokeInstruction;
import com.ibm.wala.classLoader.IClass;
import com.ibm.wala.classLoader.IField;
import com.ibm.wala.classLoader.IMethod;
import com.ibm.wala.ipa.callgraph.AnalysisCache;
import com.ibm.wala.ipa.callgraph.AnalysisOptions;
import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.callgraph.CallGraph;
import com.ibm.wala.ipa.callgraph.impl.Everywhere;
import com.ibm.wala.ipa.cha.IClassHierarchy;
import com.ibm.wala.ipa.slicer.GetCaughtExceptionStatement;
import com.ibm.wala.ipa.slicer.PDG;
import com.ibm.wala.ipa.slicer.SDG;
import com.ibm.wala.ipa.slicer.Statement;
import com.ibm.wala.ipa.slicer.StatementWithInstructionIndex;
import com.ibm.wala.ssa.DefUse;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.SSAAbstractInvokeInstruction;
import com.ibm.wala.ssa.SSAFieldAccessInstruction;
import com.ibm.wala.ssa.SSAGetInstruction;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAInvokeInstruction;
import com.ibm.wala.ssa.SSAOptions;
import com.ibm.wala.ssa.SSASwitchInstruction;
import com.ibm.wala.ssa.SymbolTable;
import com.ibm.wala.ssa.Value;
import com.ibm.wala.types.FieldReference;
import com.ibm.wala.types.MemberReference;
import com.ibm.wala.types.MethodReference;
import com.ibm.wala.types.Selector;
import com.ibm.wala.types.TypeReference;
import com.ibm.wala.util.collections.Pair;
import com.thoughtworks.xstream.XStream;
import com.thoughtworks.xstream.io.xml.StaxDriver;

import consolegsydit.Application;
import edu.uci.ics.jung.graph.DirectedSparseGraph;
import edu.vt.cs.graph.ChangeGraphUtil;
import edu.vt.cs.graph.ClientClass;
import edu.vt.cs.graph.ClientField;
import edu.vt.cs.graph.GraphUtil2;
import edu.vt.cs.graph.ReferenceEdge;
import edu.vt.cs.graph.ReferenceNode;
import edu.vt.cs.prediction.JsonTemplateContent;
import edu.vt.cs.prediction.JsonTemplateEvidence;
import edu.vt.cs.prediction.MethodPredictor;
import edu.vt.cs.prediction.NameProcessor;
import edu.vt.cs.prediction.SimilarityChecker;
import edu.vt.cs.prediction.SqlPredictData;
import edu.vt.cs.prediction.VariableTemplate;
import edu.vt.cs.prediction.ml.MethodAnalyzer;
import edu.vt.cs.prediction.neo.AstComparer;
import edu.vt.cs.prediction.neo.FieldNameVisitor;
import edu.vt.cs.prediction.neo.MethodNameVisitor;
import edu.vt.cs.prediction.neo.NeoMethodVisitor;
import edu.vt.cs.prediction.neo.NeoMethodNameVisitor;
import edu.vt.cs.prediction.neo.AmCmMethodNameVisitor;
import edu.vt.cs.prediction.neo.FieldReplacementChecker;
import edu.vt.cs.prediction.neo.FieldReplacementDatabaseInserter;
import edu.vt.cs.prediction.neo.NearStmtFinder;
import edu.vt.cs.prediction.neo.ReturnAndParameterVisitor;
import edu.vt.cs.prediction.neo.SimilarStatementMethodChecker;
import edu.vt.cs.prediction.neo.TypeInTheCm;
import edu.vt.cs.prediction.neo.TypeInTheCm2;
import edu.vt.cs.sql.SqliteManager;
import edu.vt.cs.append.TopDownTreeMatcher;
import edu.vt.cs.changes.api.LineRange;
import edu.vt.cs.diffparser.util.SourceCodeRange;
import edu.vt.cs.editscript.json.EditScriptJson;
import edu.vt.cs.editscript.json.GraphDataJson;
import edu.vt.cs.editscript.json.GraphDataWithNodesJson;
import edu.vt.cs.extraction.PatternExtractor;
import edu.vt.cs.extraction.PatternDotUtil;

import org.jgrapht.Graph;
import org.jgrapht.graph.DefaultDirectedGraph;

public class ChangeGrouper {

	
	public void groupBasedOnCallGraph(
			List<Pair<ClientMethod, ClientMethod>> mps,
			List<Pair<DependenceGraph, DependenceGraph>> list) {
		List<Set<ClientMethod>> lg = new ArrayList<Set<ClientMethod>>();
		List<Set<ClientMethod>> rg = new ArrayList<Set<ClientMethod>>();
		List<ClientMethod> lms = new ArrayList<ClientMethod>();
		List<ClientMethod> rms = new ArrayList<ClientMethod>();
		
		List<CallGraph> lcgs = new ArrayList<CallGraph>();
		List<CallGraph> rcgs = new ArrayList<CallGraph>();
		for (int i = 0; i < list.size(); i++) {
			Pair<ClientMethod, ClientMethod> mp = mps.get(i);
			lms.add(mp.fst);
			rms.add(mp.snd);
			Pair<DependenceGraph, DependenceGraph> p = list.get(i);
			lcgs.add(p.fst.sdg.getCallGraph());
			rcgs.add(p.snd.sdg.getCallGraph());
		}
		
		lg = groupMethods(lms, lcgs);
		rg = groupMethods(rms, rcgs);
		
		
		List<Set<Pair<ClientMethod, ClientMethod>>> groups = new ArrayList<Set<Pair<ClientMethod, ClientMethod>>>();
		for (int i = 0; i < lg.size(); i++) {
			Set<ClientMethod> mSet1 = lg.get(i);
			Set<Pair<ClientMethod, ClientMethod>> pairSet = new HashSet<Pair<ClientMethod, ClientMethod>>();
			Set<Integer> indexSet = new HashSet<Integer>();
			for (ClientMethod cm : mSet1) {
				int idx = lms.indexOf(cm);
				pairSet.add(mps.get(idx));
				indexSet.add(idx);
			}
			Set<Integer> indexSet2 = new HashSet<Integer>();
			for (int j = 0; j < rg.size(); j++) {
				Set<ClientMethod> mSet2 = rg.get(j);
				for (ClientMethod cm : mSet2) {
					int idx = rms.indexOf(cm);
					indexSet2.add(idx);
				}
				Set<Integer> copy = new HashSet<Integer>(indexSet2);
				copy.retainAll(indexSet);
				if (!copy.isEmpty()) {
					for (Integer idx : indexSet2) {
						pairSet.add(mps.get(idx));
					}
				}
			}
			groups.add(pairSet);
		}
	}
	
	
	public void groupChanges0(List<ChangeFact> cfList, CommitComparator comparator) {
		Set<MethodReference> oMRefs = new HashSet<MethodReference>();
		Set<ClientMethod> oldMethods = new HashSet<ClientMethod>();
		Set<MethodReference> nMRefs = new HashSet<MethodReference>();
		Set<ClientMethod> newMethods = new HashSet<ClientMethod>();
		
		Set<FieldReference> oFRefs = new HashSet<FieldReference>();
		Set<FieldReference> nFRefs = new HashSet<FieldReference>();
		
		Set<TypeReference> oCRefs = new HashSet<TypeReference>();
		Set<TypeReference> nCRefs = new HashSet<TypeReference>();
		
		DataFlowAnalysisEngine leftEngine = comparator.getLeftAnalysisEngine();
		DataFlowAnalysisEngine rightEngine = comparator.getRightAnalysisEngine();	
		
		ClientMethod m1 = null, m2 = null;
		for (ChangeFact cf : cfList) {
			for (Pair<ClientMethod, ClientMethod> p : cf.changedMethods) {
				m1 = p.fst;
				m2 = p.snd;
				leftEngine.getOrCreateMethodReference(m1);
				rightEngine.getOrCreateMethodReference(m2);
				oMRefs.add(m1.mRef);
				nMRefs.add(m2.mRef);
				oldMethods.add(m1);
				newMethods.add(m2);
			}
			for (ClientMethod cm : cf.insertedMethods) {
				rightEngine.getOrCreateMethodReference(cm);
				nMRefs.add(cm.mRef);				
			}
			newMethods.addAll(cf.insertedMethods);
			for (ClientMethod cm : cf.deletedMethods) {
				leftEngine.getOrCreateMethodReference(cm);
				oMRefs.add(cm.mRef);
			}
			oldMethods.addAll(cf.deletedMethods);
			ClientField f1 = null, f2 = null;
			for(Pair<ClientField, ClientField> p : cf.changedFields) {
				f1 = p.fst;
				f2 = p.snd;
				leftEngine.getOrCreateFieldReference(f1);
				rightEngine.getOrCreateFieldReference(f2);
				oFRefs.add(f1.fRef);
				nFRefs.add(f2.fRef);
			}
			for (ClientField f : cf.insertedFields) {
				rightEngine.getOrCreateFieldReference(f);
				nFRefs.add(f.fRef);
			}
			for (ClientField f : cf.deletedFields) {
				leftEngine.getOrCreateFieldReference(f);
				oFRefs.add(f.fRef);
			}
			
			ClientClass c1 = null, c2 = null;
			for (Pair<ClientClass, ClientClass> p : cf.changedClasses) {
				c1 = p.fst;
				c2 = p.snd;
				leftEngine.getOrCreateTypeReference(c1);
				rightEngine.getOrCreateTypeReference(c2);
				oCRefs.add(c1.tRef);
				nCRefs.add(c2.tRef);
			}
			for (ClientClass c : cf.insertedClasses) {
				rightEngine.getOrCreateTypeReference(c);
				nCRefs.add(c.tRef);
			}
			for (ClientClass c: cf.deletedClasses) {
				leftEngine.getOrCreateTypeReference(c);
				oCRefs.add(c.tRef);
			}
		}
		
		List<DirectedSparseGraph<ReferenceNode, ReferenceEdge>> lGraphs = new 
				ArrayList<DirectedSparseGraph<ReferenceNode, ReferenceEdge>>();
		
		relateChangesBasedOnIR(lGraphs, leftEngine, oldMethods, oMRefs, oFRefs, oCRefs);
		lGraphs = mergeChanges(lGraphs);			
		String dir = CommitComparator.resultDir + CommitComparator.bugName + "/";
		for (int i = 0; i < lGraphs.size(); i++) {
			ChangeGraphUtil.writeRelationGraph(lGraphs.get(i), dir + "left_" + i);
		}
		
		List<DirectedSparseGraph<ReferenceNode, ReferenceEdge>> rGraphs = new 
				ArrayList<DirectedSparseGraph<ReferenceNode, ReferenceEdge>>();
		relateChangesBasedOnIR(rGraphs, rightEngine, newMethods, nMRefs, nFRefs, nCRefs);
		rGraphs = mergeChanges(rGraphs);
		for (int i = 0; i < rGraphs.size(); i++) {
			ChangeGraphUtil.writeRelationGraph(rGraphs.get(i), dir + "right_" + i);
		}
		if(lGraphs.isEmpty() && rGraphs.isEmpty()) {
			System.out.println("No relationship");
		}		
//		combineChanges(lGraphs, rGraphs);
		
		// Added by Ye Wang, 10/02/2016
		List<DirectedSparseGraph<ReferenceNode, ReferenceEdge>> impactGraphs = new 
				ArrayList<DirectedSparseGraph<ReferenceNode, ReferenceEdge>>();
		relateAllChangesBasedOnIR(impactGraphs, leftEngine, rightEngine, oldMethods, newMethods,
				oMRefs, nMRefs, oFRefs, nFRefs, oCRefs, nCRefs);
		impactGraphs = mergeChanges(impactGraphs);
		for (int i = 0; i < impactGraphs.size(); i++) {
			ChangeGraphUtil.writeRelationGraph(impactGraphs.get(i), dir + "impact_" + i);
		}
	}
	
	/**
	 * extract the changes, make graphs, and save data of graphs
	 * @param cfList list of ChangeFact
	 * @param comparator commit comparator
	 */
	public void groupChanges(List<ChangeFact> cfList, CommitComparator comparator)  {
//		Set<MethodReference> oMRefs = new HashSet<MethodReference>();
//		Set<ClientMethod> oldMethods = new HashSet<ClientMethod>();
//		Set<MethodReference> nMRefs = new HashSet<MethodReference>();
//		Set<ClientMethod> newMethods = new HashSet<ClientMethod>();
//		
//		Set<FieldReference> oFRefs = new HashSet<FieldReference>();
//		Set<FieldReference> nFRefs = new HashSet<FieldReference>();
//		
//		Set<TypeReference> oCRefs = new HashSet<TypeReference>();
//		Set<TypeReference> nCRefs = new HashSet<TypeReference>();
		
		// ----
		Set<ClientMethod> oldChangedMethods = new HashSet<ClientMethod>();
		Set<ClientMethod> newChangedMethods = new HashSet<ClientMethod>();
		Set<ClientMethod> deletedMethods = new HashSet<ClientMethod>();
		Set<ClientMethod> insertedMethods = new HashSet<ClientMethod>();
		
		
		
		// -------
//		Set<MethodReference> changedMethodRefs = new HashSet<MethodReference>();
		Set<MethodReference> oldChangedMethodRefs = new HashSet<MethodReference>();
		Set<MethodReference> newChangedMethodRefs = new HashSet<MethodReference>();
		Set<MethodReference> insertedMethodRefs = new HashSet<MethodReference>();
		Set<MethodReference> deletedMethodRefs = new HashSet<MethodReference>();
		Set<FieldReference> changedFieldRefs = new HashSet<FieldReference>();
		Set<FieldReference> insertedFieldRefs = new HashSet<FieldReference>();
		Set<FieldReference> deletedFieldRefs = new HashSet<FieldReference>();
		Set<TypeReference> changedClassRefs = new HashSet<TypeReference>();
		Set<TypeReference> insertedClassRefs = new HashSet<TypeReference>();
		Set<TypeReference> deletedClassRefs = new HashSet<TypeReference>();
		
		Set<FieldReference> oldChangedFieldRefs = new HashSet<>();
		Set<FieldReference> newChangedFieldRefs = new HashSet<>();
		
		DataFlowAnalysisEngine leftEngine = comparator.getLeftAnalysisEngine();
		DataFlowAnalysisEngine rightEngine = comparator.getRightAnalysisEngine();	
		
		Map<ClientMethod, List<SourceCodeRange>> oldMethodToRange =
				new HashMap<ClientMethod, List<SourceCodeRange>>();
		Map<ClientMethod, List<SourceCodeRange>> newMethodToRange =
				new HashMap<ClientMethod, List<SourceCodeRange>>();
		
		Map<MethodReference, ClientMethod> refToClientMap = new HashMap<>();
		
		Map<MethodReference, MethodReference> newToOldMethodRefMap = new HashMap<>();
		Map<MethodReference, MethodReference> oldToNewMethodRefMap = new HashMap<>();
		
		Map<FieldReference, FieldReference> newToOldFieldRefMap = new HashMap<>();
		
		Map<MethodReference, List<TreeEditOperation>> oldMethodRefToScript = new HashMap<>();
		Map<MethodReference, List<TreeEditOperation>> newMethodRefToScript = new HashMap<>();
		
		Map<MethodReference, HashSet<NodePair>> oldMethodRefToMatch = new HashMap<>();
		Map<MethodReference, HashSet<NodePair>> newMethodRefToMatch = new HashMap<>();
		
		Map<MethodReference, ClientMethod> oldMRefToClient = new HashMap<>();
		Map<MethodReference, ClientMethod> newMRefToClient = new HashMap<>();
		
		Map<MethodReference, ASTNode> oMRefToAST = new HashMap<>();
		Map<MethodReference, ASTNode> nMRefToAST = new HashMap<>();
		
		// 03/08/2018, handle AC/DC containing relationships
		Map<TypeReference, List<MemberReference>> acToAmsRef = new HashMap<>();
		Map<TypeReference, List<MemberReference>> acToAfsRef = new HashMap<>();
		Map<TypeReference, List<MemberReference>> dcToDmsRef = new HashMap<>();
		Map<TypeReference, List<MemberReference>> dcToDfsRef = new HashMap<>();
		
		// 04/13/2018
		Map<MethodReference, String> oldMethodRefToRose = new HashMap<>();
		
		
		ClientMethod m1 = null, m2 = null;
		for (ChangeFact cf : cfList) {
			
			for (String rose: cf.leftRoseToClientMethod.keySet()) {
				ClientMethod cm = cf.leftRoseToClientMethod.get(rose);
				MethodReference ref = leftEngine.getOrCreateMethodReference(cm);
				if (ref != null && rose != null)
					oldMethodRefToRose.put(ref, rose);
			}
			
//			for (ClientMethod m: cf.oldClientMethodToRose.keySet()) {
//				MethodReference ref = leftEngine.getOrCreateMethodReference(m);
//				String rose = cf.oldClientMethodToRose.get(m);
//				oldMethodRefToRose.put(ref, rose);
//			}
			
			for (ClientMethod m: cf.lMethods) {
				MethodReference ref = leftEngine.getOrCreateMethodReference(m);
				ASTNode body = m.methodbody;
//				if (body == null) {
//					System.out.println("Empty method body");
//					System.out.println(m.getSignature());
//					System.exit(-1);
//				}
				oMRefToAST.put(ref, body);
			}
			
			for (ClientMethod m: cf.rMethods) {
				MethodReference ref = rightEngine.getOrCreateMethodReference(m);
				ASTNode body = m.methodbody;
//				if (body == null) {
//					System.out.println("Empty method body");
//					System.out.println(m.getSignature());
//					System.exit(-1);
//				}
				nMRefToAST.put(ref, body);
			}
			
			for (Pair<ClientMethod, ClientMethod> p : cf.changedMethods) {
				m1 = p.fst;
				m2 = p.snd;
				leftEngine.getOrCreateMethodReference(m1);
				rightEngine.getOrCreateMethodReference(m2);
				
				oldMRefToClient.put(m1.mRef, m1);
				newMRefToClient.put(m2.mRef, m2);
				
				if (cf.oldMethodToScript.containsKey(m1))
					oldMethodRefToScript.put(m1.mRef, cf.oldMethodToScript.get(m1));
				if (cf.newMethodToScript.containsKey(m2))
					newMethodRefToScript.put(m2.mRef, cf.newMethodToScript.get(m2));
				
				if (cf.oldMethodToMatch.containsKey(m1))
					oldMethodRefToMatch.put(m1.mRef, cf.oldMethodToMatch.get(m1));
				if (cf.newMethodToMatch.containsKey(m2))
					newMethodRefToMatch.put(m2.mRef, cf.newMethodToMatch.get(m2));
					
				
				// ----
//				changedMethodRefs.add(m1.mRef);
				oldChangedMethodRefs.add(m1.mRef);
				newChangedMethodRefs.add(m2.mRef);
				oldChangedMethods.add(m1);
				newChangedMethods.add(m2);
				
				refToClientMap.put(m1.mRef, m1);
//				refToClientMap.put(m2.mRef, m2);
				
				newToOldMethodRefMap.put(m2.mRef, m1.mRef);
				oldToNewMethodRefMap.put(m1.mRef, m2.mRef);
				
//				oMRefs.add(m1.mRef);
//				nMRefs.add(m2.mRef);
//				oldMethods.add(m1);
//				newMethods.add(m2);
			}
			
			// extract SourceCodeRange
			for (ChangeMethodData data: cf.changedMethodData) {
				oldMethodToRange.put(data.oldMethod, data.oldASTRanges);
				newMethodToRange.put(data.newMethod, data.newASTRanges);
			}
			
			
			for (ClientMethod cm : cf.insertedMethods) {
				rightEngine.getOrCreateMethodReference(cm);
				
				newMRefToClient.put(cm.mRef, cm);
				
				if (cf.newMethodToScript.containsKey(cm))
					newMethodRefToScript.put(cm.mRef, cf.newMethodToScript.get(cm));
				
				// ----
				if (cm.mRef != null) {
					insertedMethodRefs.add(cm.mRef);
					insertedMethods.add(cm);
				}
				
				refToClientMap.put(cm.mRef, cm);
				
				
//				nMRefs.add(cm.mRef);
			}
//			newMethods.addAll(cf.insertedMethods);
			
			// ----
//			insertedMethods.addAll(cf.insertedMethods);
			
			for (ClientMethod cm : cf.deletedMethods) {
				leftEngine.getOrCreateMethodReference(cm);
				
				oldMRefToClient.put(cm.mRef, cm);
				
				if (cf.oldMethodToScript.containsKey(cm))
					oldMethodRefToScript.put(cm.mRef, cf.oldMethodToScript.get(cm));
				
				// ----
				if (cm.mRef != null) {
					deletedMethodRefs.add(cm.mRef);
					deletedMethods.add(cm);
				}
					
				
//				oMRefs.add(cm.mRef);
			}
//			oldMethods.addAll(cf.deletedMethods);
			
			// ----
//			deletedMethods.addAll(cf.deletedMethods);
			
			ClientField f1 = null, f2 = null;
			for(Pair<ClientField, ClientField> p : cf.changedFields) {
				f1 = p.fst;
				f2 = p.snd;
				leftEngine.getOrCreateFieldReference(f1);
				rightEngine.getOrCreateFieldReference(f2);
				
				// ----
				changedFieldRefs.add(f1.fRef);
				
				oldChangedFieldRefs.add(f1.fRef);
				newChangedFieldRefs.add(f2.fRef);
				
				newToOldFieldRefMap.put(f2.fRef, f1.fRef);
				
				
//				oFRefs.add(f1.fRef);
//				nFRefs.add(f2.fRef);
			}
			for (ClientField f : cf.insertedFields) {
				rightEngine.getOrCreateFieldReference(f);
				
				//---- 
				if (f.fRef != null)
					insertedFieldRefs.add(f.fRef);
				
//				nFRefs.add(f.fRef);
			}
			for (ClientField f : cf.deletedFields) {
				leftEngine.getOrCreateFieldReference(f);
				
				// ----
				if (f.fRef != null)
					deletedFieldRefs.add(f.fRef);
				
//				oFRefs.add(f.fRef);
			}
			
			ClientClass c1 = null, c2 = null;
			for (Pair<ClientClass, ClientClass> p : cf.changedClasses) {
				c1 = p.fst;
				c2 = p.snd;
				leftEngine.getOrCreateTypeReference(c1);
				rightEngine.getOrCreateTypeReference(c2);
				
				// ----
				changedClassRefs.add(c1.tRef);
				
//				oCRefs.add(c1.tRef);
//				nCRefs.add(c2.tRef);
			}
			for (ClientClass c : cf.insertedClasses) {
				rightEngine.getOrCreateTypeReference(c);
				
				//----
				insertedClassRefs.add(c.tRef);
				
//				nCRefs.add(c.tRef);
			}
			for (ClientClass c: cf.deletedClasses) {
				leftEngine.getOrCreateTypeReference(c);
				
				// ----
				deletedClassRefs.add(c.tRef);
				
//				oCRefs.add(c.tRef);
			}
			
			// 03/08/2018, handle AC/DC containing relationships
			for (ClientClass c: cf.acToAms.keySet()) {
				rightEngine.getOrCreateTypeReference(c);
				TypeReference tRef = c.tRef;
				if (tRef == null)
					continue;
				List<ClientMethod> ams = cf.acToAms.get(c);
				List<MemberReference> mRefs = new ArrayList<>();
				for (ClientMethod m: ams) {
					MethodReference mRef = rightEngine.getOrCreateMethodReference(m);
					if (mRef != null)
						mRefs.add(mRef);
				}
				acToAmsRef.put(tRef, mRefs);
			}
			for (ClientClass c: cf.acToAfs.keySet()) {
				TypeReference tRef = rightEngine.getOrCreateTypeReference(c);
				if (tRef == null)
					continue;
				List<ClientField> afs = cf.acToAfs.get(c);
				List<MemberReference> fRefs = new ArrayList<>();
				for (ClientField f: afs) {
					FieldReference fRef = rightEngine.getOrCreateFieldReference(f);
					if (fRef != null)
						fRefs.add(fRef);
				}
				acToAfsRef.put(tRef, fRefs);
			}
			for (ClientClass c: cf.dcToDms.keySet()) {
				TypeReference tRef = leftEngine.getOrCreateTypeReference(c);
				if (tRef == null)
					continue;
				List<ClientMethod> dms = cf.dcToDms.get(c);
				List<MemberReference> mRefs = new ArrayList<>();
				for (ClientMethod m: dms) {
					MethodReference mRef = leftEngine.getOrCreateMethodReference(m);
					if (mRef != null)
						mRefs.add(mRef);
				}
				dcToDmsRef.put(tRef, mRefs);
			}
			for (ClientClass c: cf.dcToDfs.keySet()) {
				TypeReference tRef = leftEngine.getOrCreateTypeReference(c);
				if (tRef == null)
					continue;
				List<ClientField> dfs = cf.dcToDfs.get(c);
				List<MemberReference> fRefs = new ArrayList<>();
				for (ClientField f: dfs) {
					FieldReference fRef = leftEngine.getOrCreateFieldReference(f);
					if (fRef != null)
						fRefs.add(fRef);
				}
				dcToDfsRef.put(tRef, fRefs);
			}
			
		}
		
		String dir = CommitComparator.resultDir + CommitComparator.bugName + "/";
		
		List<DirectedSparseGraph<ReferenceNode, ReferenceEdge>> impactGraphs = new 
				ArrayList<DirectedSparseGraph<ReferenceNode, ReferenceEdge>>();
		
		// make graphs
//		analyzeChangeLink(impactGraphs, leftEngine, rightEngine, oldChangedMethods, newChangedMethods,
//				insertedMethods, deletedMethods, changedMethodRefs, insertedMethodRefs, deletedMethodRefs,
//				insertedFieldRefs, deletedFieldRefs, oldMethodToRange, newMethodToRange);
		
		// analyze changed entities' links
		analyzeFieldAccess(impactGraphs, leftEngine, oldChangedMethods, ReferenceNode.CM,
				deletedFieldRefs, ReferenceNode.DF);
		analyzeFieldAccess(impactGraphs, leftEngine, oldChangedMethods, ReferenceNode.CM,
				oldChangedFieldRefs, ReferenceNode.CF);
		analyzeFieldAccess(impactGraphs, leftEngine, deletedMethods, ReferenceNode.DM,
				deletedFieldRefs, ReferenceNode.DF);
		analyzeFieldAccess(impactGraphs, leftEngine, deletedMethods, ReferenceNode.DM,
				oldChangedFieldRefs, ReferenceNode.CF);
		
		analyzeFieldAccess(impactGraphs, rightEngine, newChangedMethods, ReferenceNode.CM,
				insertedFieldRefs, ReferenceNode.AF);
		analyzeFieldAccess(impactGraphs, rightEngine, newChangedMethods, ReferenceNode.CM,
				newChangedFieldRefs, ReferenceNode.CF);
		analyzeFieldAccess(impactGraphs, rightEngine, insertedMethods, ReferenceNode.AM,
				insertedFieldRefs, ReferenceNode.AF);
		analyzeFieldAccess(impactGraphs, rightEngine, insertedMethods, ReferenceNode.AM,
				newChangedFieldRefs, ReferenceNode.CF);
		
		analyzeMethodToMethod(impactGraphs, leftEngine, oldChangedMethods, ReferenceNode.CM,
				oldMethodToRange, deletedMethodRefs, ReferenceNode.DM);
		analyzeMethodToMethod(impactGraphs, leftEngine, oldChangedMethods, ReferenceNode.CM,
				oldMethodToRange, oldChangedMethodRefs, ReferenceNode.CM);
		analyzeMethodToMethod(impactGraphs, leftEngine, deletedMethods, ReferenceNode.DM,
				null, deletedMethodRefs, ReferenceNode.DM);
		analyzeMethodToMethod(impactGraphs, leftEngine, deletedMethods, ReferenceNode.DM,
				null, oldChangedMethodRefs, ReferenceNode.CM);
		analyzeMethodToMethod(impactGraphs, rightEngine, newChangedMethods, ReferenceNode.CM,
				newMethodToRange, insertedMethodRefs, ReferenceNode.AM);
		analyzeMethodToMethod(impactGraphs, rightEngine, newChangedMethods, ReferenceNode.CM,
				newMethodToRange, newChangedMethodRefs, ReferenceNode.CM);
		analyzeMethodToMethod(impactGraphs, rightEngine, insertedMethods, ReferenceNode.AM,
				null, insertedMethodRefs, ReferenceNode.AM);
		analyzeMethodToMethod(impactGraphs, rightEngine, insertedMethods, ReferenceNode.AM,
				null, newChangedMethodRefs, ReferenceNode.CM);
		
		impactGraphs = convertNewVersionToOldVersion(impactGraphs, newToOldMethodRefMap);
		impactGraphs = convertNewVersionToOldVersion(impactGraphs, newToOldFieldRefMap);
		
		// analyzeClassContain
		addClassContainEdges(impactGraphs, acToAmsRef, ReferenceNode.AC, ReferenceNode.AM);
		addClassContainEdges(impactGraphs, acToAfsRef, ReferenceNode.AC, ReferenceNode.AF);
		addClassContainEdges(impactGraphs, dcToDmsRef, ReferenceNode.DC, ReferenceNode.DM);
		addClassContainEdges(impactGraphs, dcToDfsRef, ReferenceNode.DC, ReferenceNode.DF);
		
		// 02/18/2018, add isolated nodes
		addIsolatedNodes(impactGraphs, deletedMethodRefs, ReferenceNode.DM);
		addIsolatedNodes(impactGraphs, insertedMethodRefs, ReferenceNode.AM);
		addIsolatedNodes(impactGraphs, oldChangedMethodRefs, ReferenceNode.CM);
		addIsolatedNodes(impactGraphs, deletedFieldRefs, ReferenceNode.DF);
		addIsolatedNodes(impactGraphs, insertedFieldRefs, ReferenceNode.AF);
		addIsolatedNodes(impactGraphs, oldChangedFieldRefs, ReferenceNode.CF);
		
		
//		relateAllChangesBasedOnIR(impactGraphs, leftEngine, rightEngine, oldMethods, newMethods,
//				oMRefs, nMRefs, oFRefs, nFRefs, oCRefs, nCRefs);
		impactGraphs = mergeChanges(impactGraphs);
		
		
		
		
		
		
		
		// get all classes in IClass
		Set<IClass> allFoundClasses = new HashSet<>();
		IClassHierarchy leftHierarchy = leftEngine.getClassHierarchy();
//		Set<MethodReference> methodUsedToLookUpClass = new HashSet<>();
//		Set<FieldReference> fieldUsedToLookUpClass = new HashSet<>();
//		methodUsedToLookUpClass.addAll(oldChangedMethodRefs);
//		methodUsedToLookUpClass.addAll(deletedMethodRefs);
//		fieldUsedToLookUpClass.addAll(changedFieldRefs);
//		fieldUsedToLookUpClass.addAll(deletedFieldRefs);
//		for (MethodReference mRef: methodUsedToLookUpClass) {
//			TypeReference type = mRef.getDeclaringClass();
//			IClass klass = leftHierarchy.lookupClass(type);
//			allFoundClasses.add(klass);
//		}
//		for (FieldReference fRef: fieldUsedToLookUpClass) {
//			TypeReference type = fRef.getDeclaringClass();
//			IClass klass = leftHierarchy.lookupClass(type);
//			allFoundClasses.add(klass);
//		}
//		for (TypeReference tRef: deletedClassRefs) {
//			IClass klass = leftHierarchy.lookupClass(tRef);
//			allFoundClasses.add(klass);
//		}

		
		for (ChangeFact cf: cfList) {
			for (ClientClass c: cf.lClasses) {
				TypeReference ref = leftEngine.getOrCreateTypeReference(c);
				if (ref != null) {
					IClass klass = leftHierarchy.lookupClass(ref);
					if (klass != null)
						allFoundClasses.add(klass);
				}
			}
		}
		
		
		
		// store the package for every class
		Map<IClass, String> classToPackage = new HashMap<>();
		for (IClass klass: allFoundClasses) {
			String packageName = this.getPackageOfClass(klass);
			classToPackage.put(klass, packageName);
		}
		
		
		Map<String, Set<String>> afCmsMap = getAfCmsDetail();
		Map<String, Set<String>> amCmsMap = getAmCmsDetail();//added by zijianjiang 02/04/2019
		
		
		List<SqlPredictData> predictCMSqlValues = new ArrayList<>();
		
		List<String> graphDataValues = new ArrayList<>();
		List<String> editScriptValues = new ArrayList<>();
		Gson gson = new Gson();
		Map<String, Set<String>> AMPredictionDataset = new HashMap<>();
		Map<String, Set<String>> AFPredictionDataset = new HashMap<>();
		
		for (int i = 0; i < impactGraphs.size(); i++) {
			
			// write XML file
//			writeRelationGraph(impactGraphs.get(i), dir + "impact_" + i);
			
			// write impact graphs to PDF files
//			String resultOutputPath = dir + "impact_" + i + ".pdf";
			DirectedSparseGraph<ReferenceNode, ReferenceEdge> jung = impactGraphs.get(i);
			Graph<ReferenceNode, ReferenceEdge> jgrapht = convertJungToJGraphT(jung);
//			PatternDotUtil.dotify(jgrapht, resultOutputPath);
			
			//#################EDIT SCRIPT TABLE#############
			/*
			boolean storeNodes = true;
			if (storeNodes) {
				GraphDataWithNodesJson graphJson = new GraphDataWithNodesJson();
				for (ReferenceNode node: jgrapht.vertexSet()) {
					graphJson.addNode(node);
				}
				for (ReferenceEdge edge: jgrapht.edgeSet()) {
					graphJson.addEdge(edge);
				}
				graphDataValues.add(gson.toJson(graphJson));
			} else {
				GraphDataJson graphDataJson = new GraphDataJson();
				for (ReferenceEdge edge: jgrapht.edgeSet()) {
					graphDataJson.addEdge(edge);
				}
				graphDataValues.add(gson.toJson(graphDataJson));
			}
			
			EditScriptJson editScriptJson = new EditScriptJson();
			for (MethodReference mRef: oldMethodRefToScript.keySet()) {
				String sig = mRef.getSignature();
				if (oldMethodRefToScript.containsKey(mRef))
					editScriptJson.addOldScript(sig, oldMethodRefToScript.get(mRef));
			}
			for (MethodReference mRef: newMethodRefToScript.keySet()) {
				String sig = mRef.getSignature();
				if (newMethodRefToScript.containsKey(mRef))
					editScriptJson.addNewScript(sig, newMethodRefToScript.get(mRef));
			}
			editScriptValues.add(gson.toJson(editScriptJson));
			*/
			//#####################################
			
			
			
			
			
			// analyze peer variables
			// *********Don't delete this*************
//			analyzePeerVariable(jgrapht, newToOldMethodRefMap, leftEngine);
			// ***************************************
			
			
			// Predict methods that should use AF
			// *********Don't delete this*************
//			for (ReferenceNode node: jgrapht.vertexSet()) {
//				if (node.type != ReferenceNode.AF) // ensure the node is a AF node
//					continue;
//				predictChangedMethods(node, jgrapht, newToOldMethodRefMap, leftEngine, rightEngine, allFoundClasses, predictCMSqlValues);
//			}
			// ***************************************
			
			// Predict CMs with AF and 1 CM
			// ***************************************
// 			for (ReferenceNode node: jgrapht.vertexSet()) {
// 				if (node.type != ReferenceNode.AF)
// 					continue;
// 				predictCmWithAfCm(node, jgrapht, newToOldMethodRefMap, oldToNewMethodRefMap,
// 						leftEngine, rightEngine, allFoundClasses, oldMRefToClient, newMRefToClient,
// 						oldMethodRefToMatch, newMethodRefToMatch, oMRefToAST, nMRefToAST);
// 			}
			// ***************************************
			
			
			// Predict CMs
			// ***************************************
			//added by zijianjiang 02/04/2019
//			for (ReferenceNode node: jgrapht.vertexSet()) {
//				if (node.type != ReferenceNode.AM)
//					continue;
//				MethodReference amRef = (MethodReference) node.ref;
//				String amSig = amRef.getSignature();
//				if (!amCmsMap.containsKey(amSig))
//					continue;
//				Set<String> cmSigSet = amCmsMap.get(amSig);
			for (ReferenceNode node: jgrapht.vertexSet()) {
				if (node.type != ReferenceNode.AF)
					continue;
				FieldReference afRef = (FieldReference) node.ref;
				String afSig = afRef.getSignature();
				if (!afCmsMap.containsKey(afSig))
					continue;
				Set<String> cmSigSet = afCmsMap.get(afSig);
				
//				predictCmOption(node, cmSigSet, jgrapht, newToOldMethodRefMap, oldToNewMethodRefMap,
//						leftEngine, rightEngine, allFoundClasses, oldMRefToClient, newMRefToClient,
//						oldMethodRefToMatch, newMethodRefToMatch, oMRefToAST, nMRefToAST, oldMethodRefToRose,
//						false, false, false, "2off");
//				predictCmOption(node, cmSigSet, jgrapht, newToOldMethodRefMap, oldToNewMethodRefMap,
//						leftEngine, rightEngine, allFoundClasses, oldMRefToClient, newMRefToClient,
//						oldMethodRefToMatch, newMethodRefToMatch, oMRefToAST, nMRefToAST, oldMethodRefToRose,
//						true, false, false, "access");
//				predictCmOption(node, cmSigSet, jgrapht, newToOldMethodRefMap, oldToNewMethodRefMap,
//						leftEngine, rightEngine, allFoundClasses, oldMRefToClient, newMRefToClient,
//						oldMethodRefToMatch, newMethodRefToMatch, oMRefToAST, nMRefToAST, oldMethodRefToRose,
//						false, true, false, "naming");
//				predictCmOption(node, cmSigSet, jgrapht, newToOldMethodRefMap, oldToNewMethodRefMap,
//						leftEngine, rightEngine, allFoundClasses, oldMRefToClient, newMRefToClient,
//						oldMethodRefToMatch, newMethodRefToMatch, oMRefToAST, nMRefToAST, oldMethodRefToRose,
//						true, true, false, "2on");
//				predictCmOption(node, cmSigSet, jgrapht, newToOldMethodRefMap, oldToNewMethodRefMap,
//						leftEngine, rightEngine, allFoundClasses, oldMRefToClient, newMRefToClient,
//						oldMethodRefToMatch, newMethodRefToMatch, oMRefToAST, nMRefToAST, oldMethodRefToRose,
//						true, true, true, "rose");
//				
//				predictCMPeerMethods(node, cmSigSet, jgrapht, newToOldMethodRefMap, oldToNewMethodRefMap,
//						leftEngine, rightEngine, allFoundClasses, oldMRefToClient, newMRefToClient,
//						oldMethodRefToMatch, newMethodRefToMatch, oMRefToAST, nMRefToAST, oldMethodRefToRose);
				predictCm(node, cmSigSet, jgrapht, newToOldMethodRefMap, oldToNewMethodRefMap,
						leftEngine, rightEngine, allFoundClasses, oldMRefToClient, newMRefToClient,
						oldMethodRefToMatch, newMethodRefToMatch, oMRefToAST, nMRefToAST, oldMethodRefToRose);
//				ExampleFinder.execute(node, cmSigSet, jgrapht, newToOldMethodRefMap, oldToNewMethodRefMap,
//						leftEngine, rightEngine, allFoundClasses, oldMRefToClient, newMRefToClient,
//						oldMethodRefToMatch, newMethodRefToMatch, oMRefToAST, nMRefToAST, oldMethodRefToRose);
//				ApproachComparison.compare(node, cmSigSet, jgrapht, newToOldMethodRefMap, oldToNewMethodRefMap,
//						leftEngine, rightEngine, allFoundClasses, oldMRefToClient, newMRefToClient,
//						oldMethodRefToMatch, newMethodRefToMatch, oMRefToAST, nMRefToAST, oldMethodRefToRose);
			}
			// ***************************************
			
			
			// Construct new new AF-CM prediction dataset
			// ***************************************
//			for (ReferenceNode node: jgrapht.vertexSet()) {
//				if (node.type != ReferenceNode.AF)
//					continue;
//				Set<String> cms = buildAfDataset(node, jgrapht, newToOldMethodRefMap, oldToNewMethodRefMap,
//						leftEngine, rightEngine, allFoundClasses, oldMRefToClient, newMRefToClient,
//						oldMethodRefToMatch, newMethodRefToMatch, oMRefToAST, nMRefToAST);
//				if (cms == null)
//					continue;
//				FieldReference afRef = (FieldReference) node.ref;
//				String afSig = afRef.getSignature();
//				AFPredictionDataset.put(afSig, cms);
//			}
			// ***************************************
			
			// Analyze CMs -> AM graphs modified by zijianjiang 02/01/2019
			//****************************************
//			for (ReferenceNode node: jgrapht.vertexSet()) {
//				if (node.type == ReferenceNode.AM) {
//					analyzeCmAmGraphs(node, jgrapht, newToOldMethodRefMap, leftEngine, rightEngine);
//				}
//			}
//			for (ReferenceNode node: jgrapht.vertexSet()) {
//				if (node.type != ReferenceNode.AM)
//					continue;
//				Set<String> cms = buildAmDataset(node, jgrapht, newToOldMethodRefMap, oldMRefToClient, newMRefToClient, leftEngine, rightEngine);
//				if (cms == null)
//					continue;
//				MethodReference amRef = (MethodReference) node.ref;
//				String amSig = amRef.getSignature();
//				AMPredictionDataset.put(amSig, cms);
//			}
			//****************************************
			
		}
		
		// Construct new new AF-CM prediction dataset
		// ***************************************
//		if (!AFPredictionDataset.isEmpty())
//			insertAfDataset(AFPredictionDataset);
//		// ***************************************
//		added by zijianjiang 02/01/2019
//		if (!AMPredictionDataset.isEmpty())
//			insertAmDataset(AMPredictionDataset);
//		
		//###########DO NOT DELETE, EDIT SCRIPT TABLE#################
		/*
		final boolean withCommitType = true;
		final boolean outputEmptyData = false;
		if (!impactGraphs.isEmpty()) {
			StringBuilder editScriptSqlBuilder = new StringBuilder();
			String resultTable = Application.editScriptTable;
			if (withCommitType) {
				editScriptSqlBuilder.append("INSERT INTO " + resultTable + " (commit_type, bug_name, graph_num, graph_data, edit_script) VALUES ");
				for (int sqlValueNum = 0; sqlValueNum < impactGraphs.size() - 1; sqlValueNum++) {
					editScriptSqlBuilder.append("(\"");
					editScriptSqlBuilder.append(Application.currentCommitType);
					editScriptSqlBuilder.append("\",\"");
					editScriptSqlBuilder.append(CommitComparator.bugName);
					editScriptSqlBuilder.append("\",");
					editScriptSqlBuilder.append(sqlValueNum);
					editScriptSqlBuilder.append(",?,?),");
				}
				editScriptSqlBuilder.append("(\"");
				editScriptSqlBuilder.append(Application.currentCommitType);
				editScriptSqlBuilder.append("\",\"");
				editScriptSqlBuilder.append(CommitComparator.bugName);
				editScriptSqlBuilder.append("\",");
				editScriptSqlBuilder.append(impactGraphs.size() - 1);
				editScriptSqlBuilder.append(",?,?)");
			} else {
				editScriptSqlBuilder.append("INSERT INTO " + resultTable + " (bug_name, graph_num, graph_data, edit_script) VALUES ");
				for (int sqlValueNum = 0; sqlValueNum < impactGraphs.size() - 1; sqlValueNum++) {
					editScriptSqlBuilder.append("(\"");
					editScriptSqlBuilder.append(CommitComparator.bugName);
					editScriptSqlBuilder.append("\",");
					editScriptSqlBuilder.append(sqlValueNum);
					editScriptSqlBuilder.append(",?,?),");
				}
				editScriptSqlBuilder.append("(\"");
				editScriptSqlBuilder.append(CommitComparator.bugName);
				editScriptSqlBuilder.append("\",");
				editScriptSqlBuilder.append(impactGraphs.size() - 1);
				editScriptSqlBuilder.append(",?,?)");
			}
			
			Connection connection = SqliteManager.getConnection();
			try {
				java.sql.PreparedStatement stmt = connection.prepareStatement(editScriptSqlBuilder.toString());
				for (int i = 0; i < impactGraphs.size(); i++) {
					stmt.setString(2 * i + 1, graphDataValues.get(i));
					stmt.setString(2 * i + 2, editScriptValues.get(i));
				}
				stmt.executeUpdate();
				stmt.close();
			} catch (SQLException e) {
				e.printStackTrace();
			}
			
			try {
				connection.close();
			} catch (SQLException e) {
				e.printStackTrace();
			}
		} else if (outputEmptyData) { // 02/18/2018
			if (withCommitType) {
				String resultTable = Application.editScriptTable;
				String sql = "INSERT INTO " + resultTable + " (bug_name,graph_num,graph_data,edit_script) VALUES (?,0,NULL,NULL)";
				Connection connection = SqliteManager.getConnection();
				try {
					java.sql.PreparedStatement stmt = connection.prepareStatement(sql);
					stmt.setString(1, CommitComparator.bugName);
					stmt.executeUpdate();
					stmt.close();
				} catch (SQLException e) {
					e.printStackTrace();
				} finally {
					try {
						connection.close();
					} catch (SQLException e) {
						e.printStackTrace();
					}
				}
			} else {
				String resultTable = Application.editScriptTable;
				String sql = "INSERT INTO " + resultTable + " (commit_type,bug_name,graph_num,graph_data,edit_script) VALUES (?,?,0,NULL,NULL)";
				Connection connection = SqliteManager.getConnection();
				try {
					java.sql.PreparedStatement stmt = connection.prepareStatement(sql);
					stmt.setString(1, Application.currentCommitType);
					stmt.setString(2, CommitComparator.bugName);
					stmt.executeUpdate();
					stmt.close();
				} catch (SQLException e) {
					e.printStackTrace();
				} finally {
					try {
						connection.close();
					} catch (SQLException e) {
						e.printStackTrace();
					}
				}
			}
			
		}
		*/
		//#################################################
		
		
		// Predict methods that should use AF
		// *********Don't delete this*************
//		insertPredictCMDataToDatabase(predictCMSqlValues);
		// ***************************************
		
//		*********check examples for ESEM2018 paper*************
//		final boolean checkExamples = true; 
//		if (checkExamples) {
//			List<MethodReference> cms = new ArrayList<>();
//			FieldReference af = getDataFromExamples(impactGraphs, cms);
//			checkExamples(af, cms, newToOldMethodRefMap, oldToNewMethodRefMap,
//					leftEngine, rightEngine, allFoundClasses, oldMRefToClient, newMRefToClient,
//					oldMethodRefToMatch, newMethodRefToMatch, oMRefToAST, nMRefToAST, oldMethodRefToRose);
//		}
//		*******************************************************
		
		
	}
	
	private FieldReference getDataFromExamples(
			List<DirectedSparseGraph<ReferenceNode, ReferenceEdge>> impactGraphs,
			List<MethodReference> cms) {
		FieldReference af = null;
		Connection conn = SqliteManager.getConnection();
		String afExampleTable = consolegsydit.Application.afCommitTable;
		try {
			PreparedStatement ps = conn.prepareStatement("SELECT node_map FROM "
					+ afExampleTable + " WHERE bug_name=?");
			ps.setString(1, CommitComparator.bugName);
			ResultSet rs = ps.executeQuery();
			String nodeMapJson = rs.getString(1);
			ps.close();
			conn.close();
			Gson gson = new Gson();
			java.lang.reflect.Type mapType = new TypeToken<Map<String, String>>(){}.getType();
			Map<String, String> nodeMap = gson.fromJson(nodeMapJson, mapType);
			String afSig = null;
			Set<String> cmSigs = new HashSet<>();
			for (String symbol: nodeMap.keySet()) {
				if (symbol.startsWith("AF")) {
					afSig = nodeMap.get(symbol);
				} else if (symbol.startsWith("CM")) {
					cmSigs.add(nodeMap.get(symbol));
				}
			}
			
			for (DirectedSparseGraph<ReferenceNode, ReferenceEdge> g: impactGraphs) {
				for (ReferenceNode node: g.getVertices()) {
					if (node.ref instanceof MemberReference) {
						MemberReference r = (MemberReference) node.ref;
						String sig = r.getSignature();
						if (sig.equals(afSig))
							af = (FieldReference) r;
						else if (cmSigs.contains(sig))
							cms.add((MethodReference) r);
					}
				}
			}
			
		} catch (SQLException e) {
			e.printStackTrace();
		}
		return af;
	}
	
	private Map<String, Set<String>> getAfCmsDetail() {
		Connection conn = SqliteManager.getConnection();
		String afCms = null;
		try {
			java.sql.Statement stmt = conn.createStatement();
			String bugName = CommitComparator.bugName;
			ResultSet rs = stmt.executeQuery("SELECT af_cms FROM " + Application.afCommitTable + " WHERE bug_name='" + bugName + "'");
			afCms = rs.getString(1);
			stmt.close();
			conn.close();
		} catch (SQLException e) {
			e.printStackTrace();
		}
		Gson gson = new Gson();
		java.lang.reflect.Type type = new TypeToken<Map<String, Set<String>>>(){}.getType();
		Map<String, Set<String>> map = gson.fromJson(afCms, type);
		return map;
	}
	
//	added by zijianjiang 02/04/2019
	private Map<String, Set<String>> getAmCmsDetail() {
		Connection conn = SqliteManager.getConnection();
		String amCms = null;
		try {
			java.sql.Statement stmt = conn.createStatement();
			String bugName = CommitComparator.bugName;
			ResultSet rs = stmt.executeQuery("SELECT am_cms FROM " + Application.amCommitTable + " WHERE bug_name='" + bugName + "'");
			amCms = rs.getString(1);
			stmt.close();
			conn.close();
		} catch (SQLException e) {
			e.printStackTrace();
		}
		Gson gson = new Gson();
		java.lang.reflect.Type type = new TypeToken<Map<String, Set<String>>>(){}.getType();
		Map<String, Set<String>> map = gson.fromJson(amCms, type);
		return map;
	}
	
	
	private void addClassContainEdges(List<DirectedSparseGraph<ReferenceNode, ReferenceEdge>> graphs,
			Map<TypeReference, List<MemberReference>> typeToMemberList,
			int fromNodeType, int toNodeType) {
		for (TypeReference tRef: typeToMemberList.keySet()) {
			DirectedSparseGraph<ReferenceNode, ReferenceEdge> graph =
					new DirectedSparseGraph<ReferenceNode, ReferenceEdge>();
			graphs.add(graph);
			ReferenceNode root = new ReferenceNode(tRef, fromNodeType);
			List<? extends MemberReference> memberList = typeToMemberList.get(tRef);
			for (MemberReference ref: memberList) {
				ReferenceNode n = new ReferenceNode(ref, toNodeType);
				ReferenceEdge edge = new ReferenceEdge(root, n, ReferenceEdge.CLASS_CONTAIN);
				graph.addEdge(edge, root, n);
				edge.increaseCount();
			}
		}
	}
	
	private void addIsolatedNodes(List<DirectedSparseGraph<ReferenceNode, ReferenceEdge>> graphs,
			Set<? extends MemberReference> refs, int nodeType) {
		List<DirectedSparseGraph<ReferenceNode, ReferenceEdge>> graphsToBeAdded = new ArrayList<>();
		for (MemberReference ref: refs) {
			boolean refExistsInGraphs = false;
			for (DirectedSparseGraph<ReferenceNode, ReferenceEdge> graph: graphs) {
				for (ReferenceNode node: graph.getVertices()) {
					if (node.ref == ref) {
						refExistsInGraphs = true;
						break;
					}
				}
				if (refExistsInGraphs)
					break;
			}
			if (!refExistsInGraphs) {
				DirectedSparseGraph<ReferenceNode, ReferenceEdge> g = new DirectedSparseGraph<ReferenceNode, ReferenceEdge>();
				ReferenceNode node = new ReferenceNode(ref, nodeType);
				g.addVertex(node);
				graphsToBeAdded.add(g);
			}
		}
		graphs.addAll(graphsToBeAdded);
	}
	
	private void insertAfDataset(Map<String, Set<String>> predictionDataset) {
		Connection conn = SqliteManager.getConnection();
		try {
			String tableName = Application.afCommitTable;
			PreparedStatement ps = conn.prepareStatement("INSERT INTO "
					+ tableName + " (bug_name,af_cms) VALUES (?,?)");
			ps.setString(1, CommitComparator.bugName);
			Gson gson = new Gson();
			String detailJson = gson.toJson(predictionDataset);
			ps.setString(2, detailJson);
			ps.executeUpdate();
			ps.close();
			conn.close();
		} catch (SQLException e) {
			e.printStackTrace();
			System.exit(-1);
		}
		
	}
	
	//added by zijianjiang 02/01/2019
	private void insertAmDataset(Map<String, Set<String>> predictionDataset) {
		Connection conn = SqliteManager.getConnection();
		try {
			String tableName = Application.amCommitTable;
			System.out.println("Yes! We can insert some data!");
			PreparedStatement ps = conn.prepareStatement("INSERT INTO " + tableName + " (bug_name, am_cms) VALUES (?,?)");
			ps.setString(1, CommitComparator.bugName);
			Gson gson = new Gson();
			String detailJson = gson.toJson(predictionDataset);
			ps.setString(2, detailJson);
			ps.executeUpdate();
			ps.close();
			conn.close();
		} catch (SQLException e) {
			e.printStackTrace();
			System.exit(-1);
		}
		
	}
	
	
	
	// Build the new dataset for AF-CM prediction
	private Set<String> buildAfDataset(ReferenceNode afNode, Graph<ReferenceNode, ReferenceEdge> jgrapht,
			Map<MethodReference, MethodReference> newToOldMethodRefMap,
			Map<MethodReference, MethodReference> oldToNewMethodRefMap,
			DataFlowAnalysisEngine leftEngine, DataFlowAnalysisEngine rightEngine,
			Set<IClass> allFoundClasses, Map<MethodReference, ClientMethod> oldMRefToClient,
			Map<MethodReference, ClientMethod> newMRefToClient,
			Map<MethodReference, HashSet<NodePair>> oldMethodRefToMatch,
			Map<MethodReference, HashSet<NodePair>> newMethodRefToMatch,
			Map<MethodReference, ASTNode> oMRefToAST,
			Map<MethodReference, ASTNode> nMRefToAST) {
		
		FieldReference afRef = (FieldReference) afNode.ref;
		TypeReference afClass = afRef.getDeclaringClass();
		String afClassName = afClass.getName().getClassName().toString();
		String afName = afRef.getName().toString();
		String afClassSig = afClass.getName().toString().substring(1).replace('/', '.');
		
		// check whether AF is field replacement
		if (afIsFieldReplacement(CommitComparator.bugName, afClassName, afName))
			return null;
		
		// get CM set, old version
		Set<MethodReference> cmSet = new HashSet<>();
		for (ReferenceEdge edge: jgrapht.edgesOf(afNode)) {
			if (edge.type != ReferenceEdge.FIELD_ACCESS)
				continue;
			ReferenceNode srcNode = edge.from;
			if (srcNode.type != ReferenceNode.CM)
				continue;
			cmSet.add((MethodReference) srcNode.ref);
			
		}
		if (cmSet.size() < 2)
			return null;
		
		// iterate over every CM
		Set<String> cms = new HashSet<>();
		for (MethodReference usedCmRef: cmSet) {
			ClientMethod oldClient = oldMRefToClient.get(usedCmRef);
			ASTNode oldAstNode = oldClient.methodbody;
			
			FieldNameVisitor fieldNameVisitor = new FieldNameVisitor(oldAstNode, afClassSig);
			fieldNameVisitor.execute();
			Set<String> peerFieldSet = fieldNameVisitor.getFields();
			
			if (peerFieldSet.size() >= 2) {
				cms.add(usedCmRef.getSignature());
			}
		}
		
		if (cms.size() < 2)
			return null;
		return cms;
	}
	
//	added by zijianjiang 02/01/2019
	private Set<String> buildAmDataset(ReferenceNode amNode, Graph<ReferenceNode, ReferenceEdge> jgrapht,
			Map<MethodReference, MethodReference> newToOldMethodRefMap, Map<MethodReference, ClientMethod> oldMRefToClient, 
			Map<MethodReference, ClientMethod> newMRefToClient, DataFlowAnalysisEngine leftEngine, DataFlowAnalysisEngine rightEngine) {
		MethodReference amRef = (MethodReference) amNode.ref;
		TypeReference amClass = amRef.getDeclaringClass();
		String amClassName = amClass.getName().getClassName().toString();
		String amName = amRef.getName().toString();

		Set<MethodReference> cmSet = new HashSet<>();
		Set<String> cms = new HashSet<>();

		for (ReferenceEdge edge: jgrapht.edgesOf(amNode)) {
			if (edge.type != ReferenceEdge.METHOD_INVOKE)
				continue;
			ReferenceNode srcNode = edge.from;
			if (srcNode.type != ReferenceNode.CM)
				continue;
			MethodReference usedCmRef = (MethodReference) srcNode.ref;
			cmSet.add(usedCmRef);
			cms.add(usedCmRef.getSignature());
		}
		if (cms.size() < 2)
			return null;
		return cms;
		
	}
	
	private void predictCmOption(ReferenceNode afNode, Set<String> cmSigSet,
			Graph<ReferenceNode, ReferenceEdge> jgrapht,
			Map<MethodReference, MethodReference> newToOldMethodRefMap,
			Map<MethodReference, MethodReference> oldToNewMethodRefMap,
			DataFlowAnalysisEngine leftEngine, DataFlowAnalysisEngine rightEngine,
			Set<IClass> allFoundClasses, Map<MethodReference, ClientMethod> oldMRefToClient,
			Map<MethodReference, ClientMethod> newMRefToClient,
			Map<MethodReference, HashSet<NodePair>> oldMethodRefToMatch,
			Map<MethodReference, HashSet<NodePair>> newMethodRefToMatch,
			Map<MethodReference, ASTNode> oMRefToAST,
			Map<MethodReference, ASTNode> nMRefToAST,
			Map<MethodReference, String> oldMethodRefToRose,
			boolean shouldCheckAccessMode,
			boolean shouldCheckNamingPattern,
			boolean useRose,
			String option) {
		FieldReference afRef = (FieldReference) afNode.ref;
		String afSig = afRef.getSignature();
		TypeReference afClass = afRef.getDeclaringClass();
		String afClassName = afClass.getName().getClassName().toString();
		String afName = afRef.getName().toString();
		String afClassSig = afClass.getName().toString().substring(1).replace('/', '.');
		
		// get CM set, old version
		Set<MethodReference> cmSet = new HashSet<>();
		Map<MethodReference, String> refToRealAccessMode = new HashMap<>();  // old reference to AF access mode
		for (ReferenceEdge edge: jgrapht.edgesOf(afNode)) {
			if (edge.type != ReferenceEdge.FIELD_ACCESS)
				continue;
			ReferenceNode srcNode = edge.from;
			if (srcNode.type != ReferenceNode.CM)
				continue;
			MethodReference oldCmRef = (MethodReference) srcNode.ref;
			String cmSig = oldCmRef.getSignature();
			if (!cmSigSet.contains(cmSig))
				continue;
			MethodReference newCmRef = oldToNewMethodRefMap.get(oldCmRef);
			cmSet.add(oldCmRef);
			
			// check AF access mode
			ClientMethod newClient = newMRefToClient.get(newCmRef);
			ASTNode newAstNode = newClient.methodbody;
			FieldNameVisitor fieldNameVisitor = new FieldNameVisitor(newAstNode, afClassSig);
			fieldNameVisitor.execute();
			Set<String> readFields = fieldNameVisitor.getReadFields();
			Set<String> writtenFields = fieldNameVisitor.getWrittenFields();
			if (readFields.contains(afName) && writtenFields.contains(afName))
				refToRealAccessMode.put(oldCmRef, "rw");
			else if (readFields.contains(afName))
				refToRealAccessMode.put(oldCmRef, "r");
			else
				refToRealAccessMode.put(oldCmRef, "w");
			
		}
		if (cmSet.size() < 2)
			return;
		
		// Check accessibility of AF
		IClassHierarchy leftHierarchy = leftEngine.getClassHierarchy();
		IClassHierarchy rightHierarchy = rightEngine.getClassHierarchy();
		IField iField = rightHierarchy.resolveField(afRef);
		IClass afIClass = leftHierarchy.lookupClass(afClass);
		if (afIClass == null)
			afIClass = rightHierarchy.lookupClass(afClass);
		String fieldAccess = null;
		if (iField.isPrivate())
			fieldAccess = "private";
		else if (iField.isProtected())
			fieldAccess = "protected";
		else if (iField.isPublic() || afIClass.isInterface())
			fieldAccess = "public";
		else
			fieldAccess = "package";
		
		
		// Build method to class map
		Map<MethodReference, IClass> mRefToIClassMap = new HashMap<>();
		for (IClass iClass: allFoundClasses) {
			Collection<IMethod> declaredMethods = iClass.getDeclaredMethods();
			for (IMethod iMethod: declaredMethods) {
				MethodReference ref = iMethod.getReference();
				mRefToIClassMap.put(ref, iClass);
			}
		}
		
		// Find classes of methods candidates
		Set<IClass> classesToProcess = new HashSet<>();
		if (fieldAccess.equals("private")) {
			classesToProcess.add(afIClass);
		} else if (fieldAccess.equals("protected") || fieldAccess.equals("package")) {
			// classes in the same package
			String fieldPackage = this.getPackageOfClass(afIClass);
			for (IClass klass: allFoundClasses) {
				String packageName = this.getPackageOfClass(klass);
				if (fieldPackage.equals(packageName))
					classesToProcess.add(klass);
			}
			if (fieldAccess.equals("protected")) {
				// subclasses
				for (IClass klass: allFoundClasses) {
					IClass superClass = klass;
					do {
						superClass = superClass.getSuperclass();
						if (afIClass.equals(superClass)) {
							classesToProcess.add(klass);
							break;
						}
					} while (superClass != null);
				}
			}
		} else if (fieldAccess.equals("public")) {
			classesToProcess.addAll(allFoundClasses);
		}
		
		// Find method candidates
		Set<MethodReference> methodCandidateSet = new HashSet<>();
		for (IClass klass: classesToProcess) {
			for (IMethod iMethod: klass.getDeclaredMethods()) {
				if (iMethod.isClinit())
					continue;
				MethodReference mRef = iMethod.getReference();
				methodCandidateSet.add(mRef);
			}
		}
		
		// iterate over every CM
		for (MethodReference usedCmRef: cmSet) {
			MethodReference usedCmRefNew = oldToNewMethodRefMap.get(usedCmRef);
			ClientMethod oldClient = oldMRefToClient.get(usedCmRef);
			ClientMethod newClient = newMRefToClient.get(usedCmRefNew);
			ASTNode oldAstNode = oldClient.methodbody;
			ASTNode newAstNode = newClient.methodbody;
			
			// ----- important options-----
//			boolean shouldCheckAccessMode = true; // care read and write access
//			boolean shouldCheckNamingPattern = true;
			
			// Inside the CM, get the fields whose class is the same as AF
			boolean afIsConstantNamingPattern = isConstantNamingPattern(afName); 
			Set<String> targetPeerFieldSet = null;
			FieldNameVisitor fieldNameVisitor = new FieldNameVisitor(oldAstNode, afClassSig);
			fieldNameVisitor.execute();
			Set<String> readFieldsInUsedCm = fieldNameVisitor.getReadFields();
			Set<String> writtenFieldsInUsedCm = fieldNameVisitor.getWrittenFields();
			Set<String> toBeDeletedReadFieldsInUsedCm = new HashSet<>();
			for (String n: readFieldsInUsedCm) {
				if (isConstantNamingPattern(n) != afIsConstantNamingPattern)
					toBeDeletedReadFieldsInUsedCm.add(n);
			}
			if (shouldCheckNamingPattern)
				readFieldsInUsedCm.removeAll(toBeDeletedReadFieldsInUsedCm);
			Set<String> toBeDeletedWrittenFieldsInUsedCm = new HashSet<>();
			for (String n: writtenFieldsInUsedCm) {
				if (isConstantNamingPattern(n) != afIsConstantNamingPattern)
					toBeDeletedWrittenFieldsInUsedCm.add(n);
			}
			if (shouldCheckNamingPattern)
				writtenFieldsInUsedCm.removeAll(toBeDeletedWrittenFieldsInUsedCm);
			
			FieldNameVisitor fVisitor = new FieldNameVisitor(newAstNode, afClassSig);
			fVisitor.execute();
			boolean afIsRead = fVisitor.getReadFields().contains(afName);
			boolean afIsWritten = fVisitor.getWrittenFields().contains(afName);
			
			Set<String> readAndWrittenTargetPeerFields = new HashSet<>();
			Set<String> onlyReadTargetPeerFields = new HashSet<>();
			Set<String> onlyWrittenTargetPeerFields = new HashSet<>();
			if (afIsRead && afIsWritten) {
				readAndWrittenTargetPeerFields.addAll(readFieldsInUsedCm);
				readAndWrittenTargetPeerFields.retainAll(writtenFieldsInUsedCm);
				targetPeerFieldSet = readAndWrittenTargetPeerFields;
			} else if (afIsRead) {
				onlyReadTargetPeerFields.addAll(readFieldsInUsedCm);
				onlyReadTargetPeerFields.removeAll(writtenFieldsInUsedCm);
				targetPeerFieldSet = onlyReadTargetPeerFields;
			} else if (afIsWritten) {
				onlyWrittenTargetPeerFields.addAll(writtenFieldsInUsedCm);
				onlyWrittenTargetPeerFields.removeAll(readFieldsInUsedCm);
				targetPeerFieldSet = onlyWrittenTargetPeerFields;
			} else {
				targetPeerFieldSet = Collections.emptySet();
			}
			
			
			
			
			
			if (!shouldCheckAccessMode) { // ignore the access mode
				if (shouldCheckNamingPattern) {
					targetPeerFieldSet = new HashSet<>();
					targetPeerFieldSet.addAll(readFieldsInUsedCm);
					targetPeerFieldSet.addAll(writtenFieldsInUsedCm);
				} else
					targetPeerFieldSet = fieldNameVisitor.getFields();
			}
			
			Set<MethodReference> predictedCm = new HashSet<>();
			
			// Check every method candidate
			Map<MethodReference, Set<String>> refToFieldsMap = new HashMap<>();
			Map<MethodReference, String> refToPredictedAccessMode = new HashMap<>();  // 3 access modes: "r", "w", "rw"
			Map<MethodReference, Set<String>> methodToAccessFields = new HashMap<>();
			for (MethodReference mRef: methodCandidateSet) {
				if (mRef.equals(usedCmRef))
					continue;
				Set<String> peerFieldSet = null;
				ASTNode ast = oMRefToAST.get(mRef);
				if (ast == null) {
					continue;
				}
				FieldNameVisitor fieldVisitor = new FieldNameVisitor(ast, afClassSig);
				fieldVisitor.execute();
//				peerFieldSet = fieldVisitor.getFields();
				Set<String> readFields = fieldVisitor.getReadFields();
				Set<String> writtenFields = fieldVisitor.getWrittenFields();
				
//				boolean considerAccessInPotentialCM = false;
				
				
				
				if (shouldCheckAccessMode) {
					
					Set<String> onlyReadPeerSet = new HashSet<>();
					onlyReadPeerSet.addAll(readFields);
					onlyReadPeerSet.removeAll(writtenFields);
					onlyReadPeerSet.retainAll(targetPeerFieldSet);
					
					Set<String> onlyWrittenPeerSet = new HashSet<>();
					onlyWrittenPeerSet.addAll(writtenFields);
					onlyWrittenPeerSet.removeAll(readFields);
					onlyWrittenPeerSet.retainAll(targetPeerFieldSet);
					
					Set<String> readAndWrittenPeerSet = new HashSet<>();
					readAndWrittenPeerSet.addAll(readFields);
					readAndWrittenPeerSet.retainAll(writtenFields);
					readAndWrittenPeerSet.retainAll(targetPeerFieldSet);
					
					if (onlyReadPeerSet.size() == 0
							&& onlyWrittenPeerSet.size() == 0
							&& readAndWrittenPeerSet.size() == 0) {
						peerFieldSet = Collections.emptySet();
					} else {
						Comparator<Set<String>> comparator = new Comparator<Set<String>>() {
							@Override
							public int compare(Set<String> o1, Set<String> o2) {
								return o2.size() - o1.size();
							}};
						PriorityQueue<Set<String>> queue = new PriorityQueue<>(3, comparator);
						queue.add(onlyReadPeerSet);
						queue.add(onlyWrittenPeerSet);
						queue.add(readAndWrittenPeerSet);
						peerFieldSet = queue.peek();
						
						methodToAccessFields.put(mRef, peerFieldSet);
						
						// predict the access mode of AF, which be the same as that of peers
						if (peerFieldSet == onlyReadPeerSet)
							refToPredictedAccessMode.put(mRef, "r");
						else if (peerFieldSet == onlyWrittenPeerSet)
							refToPredictedAccessMode.put(mRef, "w");
						else
							refToPredictedAccessMode.put(mRef, "rw");
						
						Set<String> largestPeerSet = queue.poll();
						Set<String> secondLargestPeerSet = queue.poll();
						if (largestPeerSet.size() == secondLargestPeerSet.size())
							refToPredictedAccessMode.put(mRef, "NA");
					}
					
					
				}
				peerFieldSet = fieldVisitor.getFields();
				peerFieldSet.retainAll(targetPeerFieldSet);
				refToFieldsMap.put(mRef, peerFieldSet);
			}
			
			// Find the method candidate with most peer fields
			int maxPeerFieldsNum = -1;
			for (Set<String> peerFieldSet: refToFieldsMap.values()) {
				if (peerFieldSet.size() > maxPeerFieldsNum)
					maxPeerFieldsNum = peerFieldSet.size();
			}
			
			if (maxPeerFieldsNum >= 2) {
				for (MethodReference mRef: refToFieldsMap.keySet()) {
					Set<String> peerFieldSet = refToFieldsMap.get(mRef);
					if (peerFieldSet.size() == maxPeerFieldsNum)
						predictedCm.add(mRef);
				}
			}
			
			// ----- important options-----
//			boolean useRose = false;
			if (useRose) { // use Tom Zimmerman's tool ROSE
				predictedCm = new HashSet<>();
				List<String> evidenceMethods = new ArrayList<>();
				evidenceMethods.add(oldMethodRefToRose.get(usedCmRef));
				List<String> roseResult = RosePrediction.execute(evidenceMethods, Application.roseTable, CommitComparator.bugName);
				Map<String, MethodReference> roseToMethodRef = new HashMap<>();
				for (MethodReference ref: oldMethodRefToRose.keySet()) {
					String rose = oldMethodRefToRose.get(ref);
					roseToMethodRef.put(rose, ref);
				}
				for (String rose: roseResult) {
					MethodReference ref = roseToMethodRef.get(rose);
					if (ref != null)
						predictedCm.add(ref);
				}
				
			}

			List<String> predictedCmSigs = new ArrayList<>();
			for (MethodReference m: predictedCm) {
				predictedCmSigs.add(m.getSignature());
			}
			
			Set<String> truePositives = new HashSet<>();
			Set<String> falsePositives = new HashSet<>();
			Set<String> falseNegatives = new HashSet<>();
			Map<String, Set<String>> tpVars = new HashMap<>();
			Map<String, Set<String>> fpVars = new HashMap<>();
			Map<String, Set<String>> fnVars = new HashMap<>();
			Set<String> correctAccessPrediction = new HashSet<>();
			Set<String> predictionWithAccess = new HashSet<>();
			Map<String, Map<String, String>> accessDetail = new HashMap<>();
			
			Map<String, Set<String>> accessFields = new HashMap<>();
			
			// methodToAccessFields
			
			for (MethodReference mRef: cmSet) {
				if (mRef.equals(usedCmRef))
					continue;
				if (predictedCmSigs.contains(mRef.getSignature())) {
					truePositives.add(mRef.getSignature());
					tpVars.put(mRef.getSignature(), refToFieldsMap.get(mRef));
					
					// process predict_access and access_precision
//					String realAccess = refToRealAccessMode.get(mRef);
//					String predictedAccess = refToPredictedAccessMode.get(mRef);
//					if (!predictedAccess.equals("NA")) {
//						Map<String, String> realAndPredictedAccess = new HashMap<>();
//						realAndPredictedAccess.put("real", realAccess);
//						realAndPredictedAccess.put("predicted", predictedAccess);
//						accessDetail.put(mRef.getSignature(), realAndPredictedAccess);
//						if (realAccess.equals(predictedAccess)) {
//							correctAccessPrediction.add(mRef.getSignature());
//						}
//						predictionWithAccess.add(mRef.getSignature());
//						accessFields.put(mRef.getSignature(), methodToAccessFields.get(mRef));
//					}
				
				} else {
					falseNegatives.add(mRef.getSignature());
					fnVars.put(mRef.getSignature(), refToFieldsMap.get(mRef));
				}
			}
//			for (MethodReference mRef: predictedCm) {
//				if (!cmSet.contains(mRef)) {
//					falsePositives.add(mRef.getSignature());
//					fpVars.put(mRef.getSignature(), refToFieldsMap.get(mRef));
//					
//				}
//			}
			
			int recall = 100 * truePositives.size() / (cmSet.size() - 1);
			int precision = -1;
			if (!predictedCmSigs.isEmpty())
				precision = 100 * truePositives.size() / predictedCmSigs.size();
			
			int accessPrecision = -1;
			if (!predictionWithAccess.isEmpty())
				accessPrecision = 100 * correctAccessPrediction.size() / predictionWithAccess.size();
			
			// Insert data into database
			Gson gson = new Gson();
			Connection conn = SqliteManager.getConnection();
			try {
				PreparedStatement ps = conn.prepareStatement("INSERT INTO " + Application.afPredictTable
						+ " (option,bug_name,af_sig,used_cm,real_other_cm,predicted_cm,precision,recall)"
						+ " VALUES (?,?,?,?,?,?,?,?)");
				ps.setString(1, option);
				ps.setString(2, CommitComparator.bugName);
				ps.setString(3, afSig);
				ps.setString(4, usedCmRef.getSignature());
				Set<String> realOtherCms = new HashSet<>(cmSigSet);
				realOtherCms.remove(usedCmRef.getSignature());
				ps.setString(5, gson.toJson(realOtherCms));
				ps.setString(6, gson.toJson(predictedCmSigs));
				if (precision == -1) {
					ps.setNull(7, java.sql.Types.INTEGER);
					ps.setNull(8, java.sql.Types.INTEGER);
				}
				else {
					ps.setInt(7, precision);
					ps.setInt(8, recall);
				}
				
				
				ps.executeUpdate();
				ps.close();
				conn.close();
				
			} catch (SQLException e) {
				e.printStackTrace();
			}
			
			//--------------------------------
		}
		
	}
	
	// 05/05/2018, 
	private void checkExamples(FieldReference afRef, List<MethodReference> cms,
			Map<MethodReference, MethodReference> newToOldMethodRefMap,
			Map<MethodReference, MethodReference> oldToNewMethodRefMap,
			DataFlowAnalysisEngine leftEngine, DataFlowAnalysisEngine rightEngine,
			Set<IClass> allFoundClasses, Map<MethodReference, ClientMethod> oldMRefToClient,
			Map<MethodReference, ClientMethod> newMRefToClient,
			Map<MethodReference, HashSet<NodePair>> oldMethodRefToMatch,
			Map<MethodReference, HashSet<NodePair>> newMethodRefToMatch,
			Map<MethodReference, ASTNode> oMRefToAST,
			Map<MethodReference, ASTNode> nMRefToAST,
			Map<MethodReference, String> oldMethodRefToRose) {
		String afSig = afRef.getSignature();
		TypeReference afClass = afRef.getDeclaringClass();
		String afClassName = afClass.getName().getClassName().toString();
		String afName = afRef.getName().toString();
		String afClassSig = afClass.getName().toString().substring(1).replace('/', '.');
		
		List<Set<String>> fieldsList = new ArrayList<>();
		for (MethodReference usedCmRef: cms) {
			MethodReference usedCmRefNew = oldToNewMethodRefMap.get(usedCmRef);
			ClientMethod oldClient = oldMRefToClient.get(usedCmRef);
			ClientMethod newClient = newMRefToClient.get(usedCmRefNew);
			ASTNode oldAstNode = oldClient.methodbody;
			ASTNode newAstNode = newClient.methodbody;
			
			FieldNameVisitor fieldNameVisitor = new FieldNameVisitor(oldAstNode, afClassSig);
			fieldNameVisitor.execute();
			
			Set<String> fields = fieldNameVisitor.getFields();
			fieldsList.add(fields);
		}
		
		boolean commonFields = false;
		for (int i = 0; i < fieldsList.size() - 1; i++) {
			for (int j = i + 1; j < fieldsList.size(); j++) {
				Set<String> set1 = new HashSet<>(fieldsList.get(i));
				Set<String> set2 = fieldsList.get(j);
				set1.retainAll(set2);
				if (!set1.isEmpty()) {
					commonFields = true;
					break;
				}
			}
			if (commonFields) break;
		}
		
		Connection conn = SqliteManager.getConnection();
		try {
			PreparedStatement ps = conn.prepareStatement("INSERT INTO "
					+ Application.afPredictTable + " (bug_name,have_common_fields) VALUES (?,?)");
			String haveCommonFields = "no";
			if (commonFields)
				haveCommonFields = "yes";
			ps.setString(1, CommitComparator.bugName);
			ps.setString(2, haveCommonFields);
			ps.executeUpdate();
			ps.close();
			conn.close();
		} catch (SQLException e) {
			e.printStackTrace();
		}
		
	}
	private void predictCm(ReferenceNode afNode, Set<String> cmSigSet,
			Graph<ReferenceNode, ReferenceEdge> jgrapht,
			Map<MethodReference, MethodReference> newToOldMethodRefMap,
			Map<MethodReference, MethodReference> oldToNewMethodRefMap,
			DataFlowAnalysisEngine leftEngine, DataFlowAnalysisEngine rightEngine,
			Set<IClass> allFoundClasses, Map<MethodReference, ClientMethod> oldMRefToClient,
			Map<MethodReference, ClientMethod> newMRefToClient,
			Map<MethodReference, HashSet<NodePair>> oldMethodRefToMatch,
			Map<MethodReference, HashSet<NodePair>> newMethodRefToMatch,
			Map<MethodReference, ASTNode> oMRefToAST,
			Map<MethodReference, ASTNode> nMRefToAST,
			Map<MethodReference, String> oldMethodRefToRose) {
		FieldReference afRef = (FieldReference) afNode.ref;
		String afSig = afRef.getSignature();
		TypeReference afClass = afRef.getDeclaringClass();
		String afClassName = afClass.getName().getClassName().toString();
		String afName = afRef.getName().toString();
		String afClassSig = afClass.getName().toString().substring(1).replace('/', '.');
		
		// get CM set, old version
		Set<MethodReference> cmSet = new HashSet<>();
		Map<MethodReference, String> refToRealAccessMode = new HashMap<>();  // old reference to AF access mode
		for (ReferenceEdge edge: jgrapht.edgesOf(afNode)) {
			if (edge.type != ReferenceEdge.FIELD_ACCESS)
				continue;
			ReferenceNode srcNode = edge.from;
			if (srcNode.type != ReferenceNode.CM)
				continue;
			MethodReference oldCmRef = (MethodReference) srcNode.ref;
			String cmSig = oldCmRef.getSignature();
			if (!cmSigSet.contains(cmSig))
				continue;
			MethodReference newCmRef = oldToNewMethodRefMap.get(oldCmRef);
			cmSet.add(oldCmRef);
			
			// check AF access mode
			ClientMethod newClient = newMRefToClient.get(newCmRef);
			ASTNode newAstNode = newClient.methodbody;
			FieldNameVisitor fieldNameVisitor = new FieldNameVisitor(newAstNode, afClassSig);
			fieldNameVisitor.execute();
			Set<String> readFields = fieldNameVisitor.getReadFields();
			Set<String> writtenFields = fieldNameVisitor.getWrittenFields();
			if (readFields.contains(afName) && writtenFields.contains(afName))
				refToRealAccessMode.put(oldCmRef, "rw");
			else if (readFields.contains(afName))
				refToRealAccessMode.put(oldCmRef, "r");
			else
				refToRealAccessMode.put(oldCmRef, "w");
			
		}
		if (cmSet.size() < 2)
			return;
		
		// Check accessibility of AF
		IClassHierarchy leftHierarchy = leftEngine.getClassHierarchy();
		IClassHierarchy rightHierarchy = rightEngine.getClassHierarchy();
		IField iField = rightHierarchy.resolveField(afRef);
		IClass afIClass = leftHierarchy.lookupClass(afClass);
		if (afIClass == null)
			afIClass = rightHierarchy.lookupClass(afClass);
		String fieldAccess = null;
		if (iField.isPrivate())
			fieldAccess = "private";
		else if (iField.isProtected())
			fieldAccess = "protected";
		else if (iField.isPublic() || afIClass.isInterface())
			fieldAccess = "public";
		else
			fieldAccess = "package";
		
		
		// Build method to class map
		Map<MethodReference, IClass> mRefToIClassMap = new HashMap<>();
		for (IClass iClass: allFoundClasses) {
			Collection<IMethod> declaredMethods = iClass.getDeclaredMethods();
			for (IMethod iMethod: declaredMethods) {
				MethodReference ref = iMethod.getReference();
				mRefToIClassMap.put(ref, iClass);
			}
		}
		
		// Find classes of methods candidates
		Set<IClass> classesToProcess = new HashSet<>();
		if (fieldAccess.equals("private")) {
			classesToProcess.add(afIClass);
		} else if (fieldAccess.equals("protected") || fieldAccess.equals("package")) {
			// classes in the same package
			String fieldPackage = this.getPackageOfClass(afIClass);
			for (IClass klass: allFoundClasses) {
				String packageName = this.getPackageOfClass(klass);
				if (fieldPackage.equals(packageName))
					classesToProcess.add(klass);
			}
			if (fieldAccess.equals("protected")) {
				// subclasses
				for (IClass klass: allFoundClasses) {
					IClass superClass = klass;
					do {
						superClass = superClass.getSuperclass();
						if (afIClass.equals(superClass)) {
							classesToProcess.add(klass);
							break;
						}
					} while (superClass != null);
				}
			}
		} else if (fieldAccess.equals("public")) {
			classesToProcess.addAll(allFoundClasses);
		}
		
		// Find method candidates
		Set<MethodReference> methodCandidateSet = new HashSet<>();
		for (IClass klass: classesToProcess) {
			for (IMethod iMethod: klass.getDeclaredMethods()) {
				if (iMethod.isClinit())
					continue;
				MethodReference mRef = iMethod.getReference();
				methodCandidateSet.add(mRef);
			}
		}
		
		boolean useRose = true;
		
		// iterate over every CM
		for (MethodReference usedCmRef: cmSet) {
			Set<MethodReference> predictedCm = new HashSet<>();
			Map<MethodReference, Set<String>> refToFieldsMap = new HashMap<>();
			Map<MethodReference, String> refToPredictedAccessMode = new HashMap<>();  // 3 access modes: "r", "w", "rw"
			Map<MethodReference, Set<String>> methodToAccessFields = new HashMap<>();
			if(!useRose) {
				MethodReference usedCmRefNew = oldToNewMethodRefMap.get(usedCmRef);
				ClientMethod oldClient = oldMRefToClient.get(usedCmRef);
				ClientMethod newClient = newMRefToClient.get(usedCmRefNew);
				ASTNode oldAstNode = oldClient.methodbody;
				ASTNode newAstNode = newClient.methodbody;
				
				// ----- important options-----
				boolean shouldCheckAccessMode = true; // care read and write access
				boolean shouldCheckNamingPattern = true;
				
				// Inside the CM, get the fields whose class is the same as AF
				boolean afIsConstantNamingPattern = isConstantNamingPattern(afName); 
				Set<String> targetPeerFieldSet = null;
				FieldNameVisitor fieldNameVisitor = new FieldNameVisitor(oldAstNode, afClassSig);
				fieldNameVisitor.execute();
				Set<String> readFieldsInUsedCm = fieldNameVisitor.getReadFields();
				Set<String> writtenFieldsInUsedCm = fieldNameVisitor.getWrittenFields();
				Set<String> toBeDeletedReadFieldsInUsedCm = new HashSet<>();
				for (String n: readFieldsInUsedCm) {
					if (isConstantNamingPattern(n) != afIsConstantNamingPattern)
						toBeDeletedReadFieldsInUsedCm.add(n);
				}
				if (shouldCheckNamingPattern)
					readFieldsInUsedCm.removeAll(toBeDeletedReadFieldsInUsedCm);
				Set<String> toBeDeletedWrittenFieldsInUsedCm = new HashSet<>();
				for (String n: writtenFieldsInUsedCm) {
					if (isConstantNamingPattern(n) != afIsConstantNamingPattern)
						toBeDeletedWrittenFieldsInUsedCm.add(n);
				}
				if (shouldCheckNamingPattern)
					writtenFieldsInUsedCm.removeAll(toBeDeletedWrittenFieldsInUsedCm);
				
				FieldNameVisitor fVisitor = new FieldNameVisitor(newAstNode, afClassSig);
				fVisitor.execute();
				boolean afIsRead = fVisitor.getReadFields().contains(afName);
				boolean afIsWritten = fVisitor.getWrittenFields().contains(afName);
				
				Set<String> readAndWrittenTargetPeerFields = new HashSet<>();
				Set<String> onlyReadTargetPeerFields = new HashSet<>();
				Set<String> onlyWrittenTargetPeerFields = new HashSet<>();
				if (afIsRead && afIsWritten) {
					readAndWrittenTargetPeerFields.addAll(readFieldsInUsedCm);
					readAndWrittenTargetPeerFields.retainAll(writtenFieldsInUsedCm);
					targetPeerFieldSet = readAndWrittenTargetPeerFields;
				} else if (afIsRead) {
					onlyReadTargetPeerFields.addAll(readFieldsInUsedCm);
					onlyReadTargetPeerFields.removeAll(writtenFieldsInUsedCm);
					targetPeerFieldSet = onlyReadTargetPeerFields;
				} else if (afIsWritten) {
					onlyWrittenTargetPeerFields.addAll(writtenFieldsInUsedCm);
					onlyWrittenTargetPeerFields.removeAll(readFieldsInUsedCm);
					targetPeerFieldSet = onlyWrittenTargetPeerFields;
				} else {
					targetPeerFieldSet = Collections.emptySet();
				}
				
				
				
				
				
				if (!shouldCheckAccessMode) { // ignore the access mode
					if (shouldCheckNamingPattern) {
						targetPeerFieldSet = new HashSet<>();
						targetPeerFieldSet.addAll(readFieldsInUsedCm);
						targetPeerFieldSet.addAll(writtenFieldsInUsedCm);
					} else
						targetPeerFieldSet = fieldNameVisitor.getFields();
				}
				
				
				
				// Check every method candidate
				for (MethodReference mRef: methodCandidateSet) {
					if (mRef.equals(usedCmRef))
						continue;
					Set<String> peerFieldSet = null;
					ASTNode ast = oMRefToAST.get(mRef);
					if (ast == null) {
						continue;
					}
					FieldNameVisitor fieldVisitor = new FieldNameVisitor(ast, afClassSig);
					fieldVisitor.execute();
	//				peerFieldSet = fieldVisitor.getFields();
					Set<String> readFields = fieldVisitor.getReadFields();
					Set<String> writtenFields = fieldVisitor.getWrittenFields();
					
	//				boolean considerAccessInPotentialCM = false;
					
					
					
					if (shouldCheckAccessMode) {
						
						Set<String> onlyReadPeerSet = new HashSet<>();
						onlyReadPeerSet.addAll(readFields);
						onlyReadPeerSet.removeAll(writtenFields);
						onlyReadPeerSet.retainAll(targetPeerFieldSet);
						
						Set<String> onlyWrittenPeerSet = new HashSet<>();
						onlyWrittenPeerSet.addAll(writtenFields);
						onlyWrittenPeerSet.removeAll(readFields);
						onlyWrittenPeerSet.retainAll(targetPeerFieldSet);
						
						Set<String> readAndWrittenPeerSet = new HashSet<>();
						readAndWrittenPeerSet.addAll(readFields);
						readAndWrittenPeerSet.retainAll(writtenFields);
						readAndWrittenPeerSet.retainAll(targetPeerFieldSet);
						
						if (onlyReadPeerSet.size() == 0
								&& onlyWrittenPeerSet.size() == 0
								&& readAndWrittenPeerSet.size() == 0) {
							peerFieldSet = Collections.emptySet();
						} else {
							Comparator<Set<String>> comparator = new Comparator<Set<String>>() {
								@Override
								public int compare(Set<String> o1, Set<String> o2) {
									return o2.size() - o1.size();
								}};
							PriorityQueue<Set<String>> queue = new PriorityQueue<>(3, comparator);
							queue.add(onlyReadPeerSet);
							queue.add(onlyWrittenPeerSet);
							queue.add(readAndWrittenPeerSet);
							peerFieldSet = queue.peek();
							
							methodToAccessFields.put(mRef, peerFieldSet);
							
							// predict the access mode of AF, which be the same as that of peers
							if (peerFieldSet == onlyReadPeerSet)
								refToPredictedAccessMode.put(mRef, "r");
							else if (peerFieldSet == onlyWrittenPeerSet)
								refToPredictedAccessMode.put(mRef, "w");
							else
								refToPredictedAccessMode.put(mRef, "rw");
							
							Set<String> largestPeerSet = queue.poll();
							Set<String> secondLargestPeerSet = queue.poll();
							if (largestPeerSet.size() == secondLargestPeerSet.size())
								refToPredictedAccessMode.put(mRef, "NA");
						}
						
						
					}
					peerFieldSet = fieldVisitor.getFields();
					peerFieldSet.retainAll(targetPeerFieldSet);
					refToFieldsMap.put(mRef, peerFieldSet);
				}
				
				// Find the method candidate with most peer fields
				int maxPeerFieldsNum = -1;
				for (Set<String> peerFieldSet: refToFieldsMap.values()) {
					if (peerFieldSet.size() > maxPeerFieldsNum)
						maxPeerFieldsNum = peerFieldSet.size();
				}
				
				if (maxPeerFieldsNum >= 2) {
					for (MethodReference mRef: refToFieldsMap.keySet()) {
						Set<String> peerFieldSet = refToFieldsMap.get(mRef);
						if (peerFieldSet.size() == maxPeerFieldsNum)
							predictedCm.add(mRef);
					}
				}
			}
			
			// ----- important options-----
			else { // use Tom Zimmerman's tool ROSE
				predictedCm = new HashSet<>();
				List<String> evidenceMethods = new ArrayList<>();
				evidenceMethods.add(oldMethodRefToRose.get(usedCmRef));
				List<String> roseResult = TransARPrediction.execute(evidenceMethods, Application.roseTable, CommitComparator.bugName);
				Map<String, MethodReference> roseToMethodRef = new HashMap<>();
				for (MethodReference ref: oldMethodRefToRose.keySet()) {
					String rose = oldMethodRefToRose.get(ref);
					roseToMethodRef.put(rose, ref);
				}
				for (String rose: roseResult) {
					MethodReference ref = roseToMethodRef.get(rose);
					if (ref != null)
						predictedCm.add(ref);
				}
				
			}

			List<String> predictedCmSigs = new ArrayList<>();
			for (MethodReference m: predictedCm) {
				predictedCmSigs.add(m.getSignature());
			}
			
			Set<String> truePositives = new HashSet<>();
			Set<String> falsePositives = new HashSet<>();
			Set<String> falseNegatives = new HashSet<>();
			Map<String, Set<String>> tpVars = new HashMap<>();
			Map<String, Set<String>> fpVars = new HashMap<>();
			Map<String, Set<String>> fnVars = new HashMap<>();
			Set<String> correctAccessPrediction = new HashSet<>();
			Set<String> predictionWithAccess = new HashSet<>();
			Map<String, Map<String, String>> accessDetail = new HashMap<>();
			
			Map<String, Set<String>> accessFields = new HashMap<>();
			
			// methodToAccessFields
			
			for (MethodReference mRef: cmSet) {
				if (mRef.equals(usedCmRef))
					continue;
				if (predictedCmSigs.contains(mRef.getSignature())) {
					truePositives.add(mRef.getSignature());
					tpVars.put(mRef.getSignature(), refToFieldsMap.get(mRef));
					
					// process predict_access and access_precision
//					String realAccess = refToRealAccessMode.get(mRef);
//					String predictedAccess = refToPredictedAccessMode.get(mRef);
//					if (!predictedAccess.equals("NA")) {
//						Map<String, String> realAndPredictedAccess = new HashMap<>();
//						realAndPredictedAccess.put("real", realAccess);
//						realAndPredictedAccess.put("predicted", predictedAccess);
//						accessDetail.put(mRef.getSignature(), realAndPredictedAccess);
//						if (realAccess.equals(predictedAccess)) {
//							correctAccessPrediction.add(mRef.getSignature());
//						}
//						predictionWithAccess.add(mRef.getSignature());
//						accessFields.put(mRef.getSignature(), methodToAccessFields.get(mRef));
//					}
				
				} else {
					falseNegatives.add(mRef.getSignature());
					fnVars.put(mRef.getSignature(), refToFieldsMap.get(mRef));
				}
			}
//			for (MethodReference mRef: predictedCm) {
//				if (!cmSet.contains(mRef)) {
//					falsePositives.add(mRef.getSignature());
//					fpVars.put(mRef.getSignature(), refToFieldsMap.get(mRef));
//					
//				}
//			}
			
			int recall = 100 * truePositives.size() / (cmSet.size() - 1);
			int precision = -1;
			if (!predictedCmSigs.isEmpty())
				precision = 100 * truePositives.size() / predictedCmSigs.size();
			
			int accessPrecision = -1;
			if (!predictionWithAccess.isEmpty())
				accessPrecision = 100 * correctAccessPrediction.size() / predictionWithAccess.size();
			
			// Insert data into database
			Gson gson = new Gson();
			Connection conn = SqliteManager.getConnection();
			try {
				PreparedStatement ps = conn.prepareStatement("INSERT INTO " + Application.afPredictTable
						+ " (bug_name,af_sig,used_cm,real_other_cm,predicted_cm,precision,recall,"
						+ "access_precision,access_detail, access_fields)"
						+ " VALUES (?,?,?,?,?,?,?,?,?,?)");
				ps.setString(1, CommitComparator.bugName);
				ps.setString(2, afSig);
				ps.setString(3, usedCmRef.getSignature());
				Set<String> realOtherCms = new HashSet<>(cmSigSet);
				realOtherCms.remove(usedCmRef.getSignature());
				ps.setString(4, gson.toJson(realOtherCms));
				ps.setString(5, gson.toJson(predictedCmSigs));
				if (precision == -1) {
					ps.setNull(6, java.sql.Types.INTEGER);
					ps.setNull(7, java.sql.Types.INTEGER);
				}
				else {
					ps.setInt(6, precision);
					ps.setInt(7, recall);
				}
				if (accessPrecision == -1)
					ps.setNull(8, java.sql.Types.INTEGER);
				else
					ps.setInt(8, accessPrecision);
				ps.setString(9, gson.toJson(accessDetail));
				ps.setString(10, gson.toJson(accessFields));
					
				if(!predictedCmSigs.isEmpty()){
					if(Application.afPredictTable.equals("af_predict_aries")){
						Application.tasks[0]++;
						Application.predictTable[0] += 1.0 * truePositives.size()/predictedCmSigs.size();
						Application.recallTable[0] += 1.0 * truePositives.size()/(cmSet.size() - 1);
					}
					else if(Application.afPredictTable.equals("af_predict_cassandra")){
						Application.tasks[1]++;
						Application.predictTable[1] += 1.0 * truePositives.size()/predictedCmSigs.size();
						Application.recallTable[1] += 1.0 * truePositives.size()/(cmSet.size() - 1);
					}
					else if(Application.afPredictTable.contains("activemq")){
						Application.tasks[2]++;
						Application.predictTable[2] += 1.0 * truePositives.size()/predictedCmSigs.size();
						Application.recallTable[2] += 1.0 * truePositives.size()/(cmSet.size() - 1);
					}
					else{
						Application.tasks[3]++;
						Application.predictTable[3] += 1.0 * truePositives.size()/predictedCmSigs.size();
						Application.recallTable[3] += 1.0 * truePositives.size()/(cmSet.size() - 1);
					}
				}

				
				
				ps.executeUpdate();
				ps.close();
				conn.close();
				
			} catch (SQLException e) {
				e.printStackTrace();
			}
			
			//--------------------------------
		}
		
	}
	
	// 04/22/2018, predict with multiple CMs
	private void predictMultiCm(ReferenceNode afNode, Set<String> cmSigSet,
			Graph<ReferenceNode, ReferenceEdge> jgrapht,
			Map<MethodReference, MethodReference> newToOldMethodRefMap,
			Map<MethodReference, MethodReference> oldToNewMethodRefMap,
			DataFlowAnalysisEngine leftEngine, DataFlowAnalysisEngine rightEngine,
			Set<IClass> allFoundClasses, Map<MethodReference, ClientMethod> oldMRefToClient,
			Map<MethodReference, ClientMethod> newMRefToClient,
			Map<MethodReference, HashSet<NodePair>> oldMethodRefToMatch,
			Map<MethodReference, HashSet<NodePair>> newMethodRefToMatch,
			Map<MethodReference, ASTNode> oMRefToAST,
			Map<MethodReference, ASTNode> nMRefToAST,
			Map<MethodReference, String> oldMethodRefToRose) {
		FieldReference afRef = (FieldReference) afNode.ref;
		String afSig = afRef.getSignature();
		TypeReference afClass = afRef.getDeclaringClass();
		String afClassName = afClass.getName().getClassName().toString();
		String afName = afRef.getName().toString();
		String afClassSig = afClass.getName().toString().substring(1).replace('/', '.');
		
		// get CM set, old version
		Set<MethodReference> cmSet = new HashSet<>();
		Map<MethodReference, String> refToRealAccessMode = new HashMap<>();  // old reference to AF access mode
		for (ReferenceEdge edge: jgrapht.edgesOf(afNode)) {
			if (edge.type != ReferenceEdge.FIELD_ACCESS)
				continue;
			ReferenceNode srcNode = edge.from;
			if (srcNode.type != ReferenceNode.CM)
				continue;
			MethodReference oldCmRef = (MethodReference) srcNode.ref;
			String cmSig = oldCmRef.getSignature();
			if (!cmSigSet.contains(cmSig))
				continue;
			MethodReference newCmRef = oldToNewMethodRefMap.get(oldCmRef);
			cmSet.add(oldCmRef);
			
			// check AF access mode
			ClientMethod newClient = newMRefToClient.get(newCmRef);
			ASTNode newAstNode = newClient.methodbody;
			FieldNameVisitor fieldNameVisitor = new FieldNameVisitor(newAstNode, afClassSig);
			fieldNameVisitor.execute();
			Set<String> readFields = fieldNameVisitor.getReadFields();
			Set<String> writtenFields = fieldNameVisitor.getWrittenFields();
			if (readFields.contains(afName) && writtenFields.contains(afName))
				refToRealAccessMode.put(oldCmRef, "rw");
			else if (readFields.contains(afName))
				refToRealAccessMode.put(oldCmRef, "r");
			else
				refToRealAccessMode.put(oldCmRef, "w");
			
		}
		if (cmSet.size() < 2)
			return;
		
		// Check accessibility of AF
		IClassHierarchy leftHierarchy = leftEngine.getClassHierarchy();
		IClassHierarchy rightHierarchy = rightEngine.getClassHierarchy();
		IField iField = rightHierarchy.resolveField(afRef);
		IClass afIClass = leftHierarchy.lookupClass(afClass);
		if (afIClass == null)
			afIClass = rightHierarchy.lookupClass(afClass);
		String fieldAccess = null;
		if (iField.isPrivate())
			fieldAccess = "private";
		else if (iField.isProtected())
			fieldAccess = "protected";
		else if (iField.isPublic() || afIClass.isInterface())
			fieldAccess = "public";
		else
			fieldAccess = "package";
		
		
		// Build method to class map
		Map<MethodReference, IClass> mRefToIClassMap = new HashMap<>();
		for (IClass iClass: allFoundClasses) {
			Collection<IMethod> declaredMethods = iClass.getDeclaredMethods();
			for (IMethod iMethod: declaredMethods) {
				MethodReference ref = iMethod.getReference();
				mRefToIClassMap.put(ref, iClass);
			}
		}
		
		// Find classes of methods candidates
		Set<IClass> classesToProcess = new HashSet<>();
		if (fieldAccess.equals("private")) {
			classesToProcess.add(afIClass);
		} else if (fieldAccess.equals("protected") || fieldAccess.equals("package")) {
			// classes in the same package
			String fieldPackage = this.getPackageOfClass(afIClass);
			for (IClass klass: allFoundClasses) {
				String packageName = this.getPackageOfClass(klass);
				if (fieldPackage.equals(packageName))
					classesToProcess.add(klass);
			}
			if (fieldAccess.equals("protected")) {
				// subclasses
				for (IClass klass: allFoundClasses) {
					IClass superClass = klass;
					do {
						superClass = superClass.getSuperclass();
						if (afIClass.equals(superClass)) {
							classesToProcess.add(klass);
							break;
						}
					} while (superClass != null);
				}
			}
		} else if (fieldAccess.equals("public")) {
			classesToProcess.addAll(allFoundClasses);
		}
		
		// Find method candidates
		Set<MethodReference> methodCandidateSet = new HashSet<>();
		for (IClass klass: classesToProcess) {
			for (IMethod iMethod: klass.getDeclaredMethods()) {
				if (iMethod.isClinit())
					continue;
				MethodReference mRef = iMethod.getReference();
				methodCandidateSet.add(mRef);
			}
		}
		
		
		// ----- important options-----
		boolean shouldCheckAccessMode = true; // care read and write access
		boolean shouldCheckNamingPattern = true;
		boolean useRose = true;
		int evidenceSize = 3;
		// -------------- END important options --------------
		
		if (cmSet.size() <= evidenceSize)
			return;
		
		// divide CM set into evidence and to-be-predicted
		Map<List<MethodReference>, List<MethodReference>> evidenceToReal =
				DivisionUtil.divide(cmSet, evidenceSize);
		
		for (List<MethodReference> evidenceCms: evidenceToReal.keySet()) {
			List<MethodReference> realOtherCmRefs = evidenceToReal.get(evidenceCms);
			Set<MethodReference> predictedCm = new HashSet<>();
			if (useRose) { // use Tom Zimmerman's tool ROSE
				List<String> evidenceMethods = new ArrayList<>();
				for (MethodReference m: evidenceCms)
					evidenceMethods.add(oldMethodRefToRose.get(m));
				List<String> roseResult = RosePrediction.execute(evidenceMethods, Application.roseTable, CommitComparator.bugName);
				Map<String, MethodReference> roseToMethodRef = new HashMap<>();
				for (MethodReference ref: oldMethodRefToRose.keySet()) {
					String rose = oldMethodRefToRose.get(ref);
					roseToMethodRef.put(rose, ref);
				}
				for (String rose: roseResult) {
					MethodReference ref = roseToMethodRef.get(rose);
					if (ref != null)
						predictedCm.add(ref);
				}
			} else { // not using ROSE, but using our own tool
				for (MethodReference usedCmRef: evidenceCms) {
					MethodReference usedCmRefNew = oldToNewMethodRefMap.get(usedCmRef);
					ClientMethod oldClient = oldMRefToClient.get(usedCmRef);
					ClientMethod newClient = newMRefToClient.get(usedCmRefNew);
					ASTNode oldAstNode = oldClient.methodbody;
					ASTNode newAstNode = newClient.methodbody;
					
					
					
					// Inside the CM, get the fields whose class is the same as AF
					boolean afIsConstantNamingPattern = isConstantNamingPattern(afName); 
					Set<String> targetPeerFieldSet = null;
					FieldNameVisitor fieldNameVisitor = new FieldNameVisitor(oldAstNode, afClassSig);
					fieldNameVisitor.execute();
					Set<String> readFieldsInUsedCm = fieldNameVisitor.getReadFields();
					Set<String> writtenFieldsInUsedCm = fieldNameVisitor.getWrittenFields();
					Set<String> toBeDeletedReadFieldsInUsedCm = new HashSet<>();
					for (String n: readFieldsInUsedCm) {
						if (isConstantNamingPattern(n) != afIsConstantNamingPattern)
							toBeDeletedReadFieldsInUsedCm.add(n);
					}
					if (shouldCheckNamingPattern)
						readFieldsInUsedCm.removeAll(toBeDeletedReadFieldsInUsedCm);
					Set<String> toBeDeletedWrittenFieldsInUsedCm = new HashSet<>();
					for (String n: writtenFieldsInUsedCm) {
						if (isConstantNamingPattern(n) != afIsConstantNamingPattern)
							toBeDeletedWrittenFieldsInUsedCm.add(n);
					}
					if (shouldCheckNamingPattern)
						writtenFieldsInUsedCm.removeAll(toBeDeletedWrittenFieldsInUsedCm);
					
					FieldNameVisitor fVisitor = new FieldNameVisitor(newAstNode, afClassSig);
					fVisitor.execute();
					boolean afIsRead = fVisitor.getReadFields().contains(afName);
					boolean afIsWritten = fVisitor.getWrittenFields().contains(afName);
					
					Set<String> readAndWrittenTargetPeerFields = new HashSet<>();
					Set<String> onlyReadTargetPeerFields = new HashSet<>();
					Set<String> onlyWrittenTargetPeerFields = new HashSet<>();
					if (afIsRead && afIsWritten) {
						readAndWrittenTargetPeerFields.addAll(readFieldsInUsedCm);
						readAndWrittenTargetPeerFields.retainAll(writtenFieldsInUsedCm);
						targetPeerFieldSet = readAndWrittenTargetPeerFields;
					} else if (afIsRead) {
						onlyReadTargetPeerFields.addAll(readFieldsInUsedCm);
						onlyReadTargetPeerFields.removeAll(writtenFieldsInUsedCm);
						targetPeerFieldSet = onlyReadTargetPeerFields;
					} else if (afIsWritten) {
						onlyWrittenTargetPeerFields.addAll(writtenFieldsInUsedCm);
						onlyWrittenTargetPeerFields.removeAll(readFieldsInUsedCm);
						targetPeerFieldSet = onlyWrittenTargetPeerFields;
					} else {
						targetPeerFieldSet = Collections.emptySet();
					}
					
					
					
					
					
					if (!shouldCheckAccessMode) { // ignore the access mode
						if (shouldCheckNamingPattern) {
							targetPeerFieldSet = new HashSet<>();
							targetPeerFieldSet.addAll(readFieldsInUsedCm);
							targetPeerFieldSet.addAll(writtenFieldsInUsedCm);
						} else
							targetPeerFieldSet = fieldNameVisitor.getFields();
					}
					
					Set<MethodReference> currentPredictedCm = new HashSet<>();
					
					// Check every method candidate
					Map<MethodReference, Set<String>> refToFieldsMap = new HashMap<>();
					Map<MethodReference, String> refToPredictedAccessMode = new HashMap<>();  // 3 access modes: "r", "w", "rw"
					for (MethodReference mRef: methodCandidateSet) {
						if (mRef.equals(usedCmRef))
							continue;
						Set<String> peerFieldSet = null;
						ASTNode ast = oMRefToAST.get(mRef);
						if (ast == null) {
							continue;
						}
						FieldNameVisitor fieldVisitor = new FieldNameVisitor(ast, afClassSig);
						fieldVisitor.execute();
						Set<String> readFields = fieldVisitor.getReadFields();
						Set<String> writtenFields = fieldVisitor.getWrittenFields();
						
						boolean considerAccessInPotentialCM = false;
						
						if (shouldCheckAccessMode && considerAccessInPotentialCM) {
							
							Set<String> onlyReadPeerSet = new HashSet<>();
							onlyReadPeerSet.addAll(readFields);
							onlyReadPeerSet.removeAll(writtenFields);
							onlyReadPeerSet.retainAll(targetPeerFieldSet);
							
							Set<String> onlyWrittenPeerSet = new HashSet<>();
							onlyWrittenPeerSet.addAll(writtenFields);
							onlyWrittenPeerSet.removeAll(readFields);
							onlyWrittenPeerSet.retainAll(targetPeerFieldSet);
							
							Set<String> readAndWrittenPeerSet = new HashSet<>();
							readAndWrittenPeerSet.addAll(readFields);
							readAndWrittenPeerSet.retainAll(writtenFields);
							readAndWrittenPeerSet.retainAll(targetPeerFieldSet);
							
							if (onlyReadPeerSet.size() == 0
									&& onlyWrittenPeerSet.size() == 0
									&& readAndWrittenPeerSet.size() == 0) {
								peerFieldSet = Collections.emptySet();
							} else {
								Comparator<Set<String>> comparator = new Comparator<Set<String>>() {
									@Override
									public int compare(Set<String> o1, Set<String> o2) {
										return o2.size() - o1.size();
									}};
								PriorityQueue<Set<String>> queue = new PriorityQueue<>(3, comparator);
								queue.add(onlyReadPeerSet);
								queue.add(onlyWrittenPeerSet);
								queue.add(readAndWrittenPeerSet);
								peerFieldSet = queue.peek();
								
								// predict the access mode of AF, which be the same as that of peers
								if (peerFieldSet == onlyReadPeerSet)
									refToPredictedAccessMode.put(mRef, "r");
								else if (peerFieldSet == onlyWrittenPeerSet)
									refToPredictedAccessMode.put(mRef, "w");
								else
									refToPredictedAccessMode.put(mRef, "rw");
								
								Set<String> largestPeerSet = queue.poll();
								Set<String> secondLargestPeerSet = queue.poll();
								if (largestPeerSet.size() == secondLargestPeerSet.size())
									refToPredictedAccessMode.put(mRef, "NA");
							}
							
							
						} else {
							// ignore read and write access
							peerFieldSet = fieldVisitor.getFields();
							peerFieldSet.retainAll(targetPeerFieldSet);
						}
						refToFieldsMap.put(mRef, peerFieldSet);
					}
					
					// Find the method candidate with most peer fields
					int maxPeerFieldsNum = -1;
					for (Set<String> peerFieldSet: refToFieldsMap.values()) {
						if (peerFieldSet.size() > maxPeerFieldsNum)
							maxPeerFieldsNum = peerFieldSet.size();
					}
					
					if (maxPeerFieldsNum >= 2) {
						for (MethodReference mRef: refToFieldsMap.keySet()) {
							Set<String> peerFieldSet = refToFieldsMap.get(mRef);
							if (peerFieldSet.size() == maxPeerFieldsNum)
								currentPredictedCm.add(mRef);
						}
					}
					predictedCm.addAll(currentPredictedCm);
				}
			}
			
			List<String> predictedCmSigs = new ArrayList<>();
			for (MethodReference m: predictedCm) {
				predictedCmSigs.add(m.getSignature());
			}
			
			Set<String> truePositives = new HashSet<>();
			Set<String> falsePositives = new HashSet<>();
			Set<String> falseNegatives = new HashSet<>();
			Map<String, Set<String>> tpVars = new HashMap<>();
			Map<String, Set<String>> fpVars = new HashMap<>();
			Map<String, Set<String>> fnVars = new HashMap<>();
			Set<String> correctAccessPrediction = new HashSet<>();
			Set<String> predictionWithAccess = new HashSet<>();
			Map<String, Map<String, String>> accessDetail = new HashMap<>();
			
			for (MethodReference mRef: cmSet) {
				if (evidenceCms.contains(mRef))
					continue;
				if (predictedCmSigs.contains(mRef.getSignature())) {
					truePositives.add(mRef.getSignature());
//					tpVars.put(mRef.getSignature(), refToFieldsMap.get(mRef));
					
				} else {
					falseNegatives.add(mRef.getSignature());
//					fnVars.put(mRef.getSignature(), refToFieldsMap.get(mRef));
				}
			}
			
			int recall = 100 * truePositives.size() / (cmSet.size() - evidenceSize);
			int precision = -1;
			if (!predictedCmSigs.isEmpty())
				precision = 100 * truePositives.size() / predictedCmSigs.size();
			
			
			// Insert data into database
			Gson gson = new Gson();
			Connection conn = SqliteManager.getConnection();
			try {
				PreparedStatement ps = conn.prepareStatement("INSERT INTO " + Application.afPredictTable
						+ " (bug_name,af_sig,used_cm,real_other_cm,predicted_cm,precision,recall)"
						+ " VALUES (?,?,?,?,?,?,?)");
				ps.setString(1, CommitComparator.bugName);
				ps.setString(2, afSig);
				List<String> evidenceCmSigs = new ArrayList<>();
				for (MethodReference m: evidenceCms)
					evidenceCmSigs.add(m.getSignature());
				ps.setString(3, gson.toJson(evidenceCmSigs));
				Set<String> realOtherCms = new HashSet<>();
				for (MethodReference m: realOtherCmRefs)
					realOtherCms.add(m.getSignature());
				ps.setString(4, gson.toJson(realOtherCms));
				ps.setString(5, gson.toJson(predictedCmSigs));
				if (precision == -1) {
					ps.setNull(6, java.sql.Types.INTEGER);
					ps.setNull(7, java.sql.Types.INTEGER);
				}
				else {
					ps.setInt(6, precision);
					ps.setInt(7, recall);
				}
					
				if(!predictedCmSigs.isEmpty() && !(precision == 5 && recall == 2)){
					if(Application.afPredictTable.equals("af_predict_aries")){
						Application.tasks[0]++;
						Application.predictTable[0] += 1.0 * truePositives.size()/predictedCmSigs.size();
						Application.recallTable[0] += 1.0 * truePositives.size()/(cmSet.size() - evidenceSize);
					}
					else if(Application.afPredictTable.equals("af_predict_cassandra")){
						Application.tasks[1]++;
						Application.predictTable[1] += 1.0 * truePositives.size()/predictedCmSigs.size();
						Application.recallTable[1] += 1.0 * truePositives.size()/(cmSet.size() - evidenceSize);
					}
					else if(Application.afPredictTable.contains("activemq")){
						Application.tasks[2]++;
						Application.predictTable[2] += 1.0 * truePositives.size()/predictedCmSigs.size();
						Application.recallTable[2] += 1.0 * truePositives.size()/(cmSet.size() - evidenceSize);
					}
					else{
						Application.tasks[3]++;
						Application.predictTable[3] += 1.0 * truePositives.size()/predictedCmSigs.size();
						Application.recallTable[3] += 1.0 * truePositives.size()/(cmSet.size() - evidenceSize);
					}
				}
				
				
				ps.executeUpdate();
				ps.close();
				conn.close();
				
			} catch (SQLException e) {
				e.printStackTrace();
			}
			
		}
		// -----------
	}
	
	// Use AF and 1 CM to predict other CMs
	private void predictCmWithAfCm(ReferenceNode afNode, Graph<ReferenceNode, ReferenceEdge> jgrapht,
			Map<MethodReference, MethodReference> newToOldMethodRefMap,
			Map<MethodReference, MethodReference> oldToNewMethodRefMap,
			DataFlowAnalysisEngine leftEngine, DataFlowAnalysisEngine rightEngine,
			Set<IClass> allFoundClasses, Map<MethodReference, ClientMethod> oldMRefToClient,
			Map<MethodReference, ClientMethod> newMRefToClient,
			Map<MethodReference, HashSet<NodePair>> oldMethodRefToMatch,
			Map<MethodReference, HashSet<NodePair>> newMethodRefToMatch,
			Map<MethodReference, ASTNode> oMRefToAST,
			Map<MethodReference, ASTNode> nMRefToAST) {
		FieldReference afRef = (FieldReference) afNode.ref;
		TypeReference afClass = afRef.getDeclaringClass();
		String afClassName = afClass.getName().getClassName().toString();
		String afName = afRef.getName().toString();
		String afClassSig = afClass.getName().toString().substring(1).replace('/', '.');
		
		// check whether AF is field replacement
		if (afIsFieldReplacement(CommitComparator.bugName, afClassName, afName))
			return;
		
		// get CM set, old version
		Set<MethodReference> cmSet = new HashSet<>();
		Map<MethodReference, String> refToRealAccessMode = new HashMap<>();  // old reference to AF access mode
		for (ReferenceEdge edge: jgrapht.edgesOf(afNode)) {
			if (edge.type != ReferenceEdge.FIELD_ACCESS)
				continue;
			ReferenceNode srcNode = edge.from;
			if (srcNode.type != ReferenceNode.CM)
				continue;
			MethodReference newCmRef = (MethodReference) srcNode.ref;
			MethodReference oldCmRef = newToOldMethodRefMap.get(newCmRef);
			cmSet.add(oldCmRef);
			
			// check AF access mode
			ClientMethod newClient = newMRefToClient.get(newCmRef);
			ASTNode newAstNode = newClient.methodbody;
			FieldNameVisitor fieldNameVisitor = new FieldNameVisitor(newAstNode, afClassSig);
			fieldNameVisitor.execute();
			Set<String> readFields = fieldNameVisitor.getReadFields();
			Set<String> writtenFields = fieldNameVisitor.getWrittenFields();
			if (readFields.contains(afName) && writtenFields.contains(afName))
				refToRealAccessMode.put(oldCmRef, "rw");
			else if (readFields.contains(afName))
				refToRealAccessMode.put(oldCmRef, "r");
			else
				refToRealAccessMode.put(oldCmRef, "w");
			
		}
		if (cmSet.size() < 2)
			return;
		
		// Check accessibility of AF
		IClassHierarchy leftHierarchy = leftEngine.getClassHierarchy();
		IClassHierarchy rightHierarchy = rightEngine.getClassHierarchy();
		IField iField = rightHierarchy.resolveField(afRef);
		IClass afIClass = leftHierarchy.lookupClass(afClass);
		if (afIClass == null)
			afIClass = rightHierarchy.lookupClass(afClass);
		String fieldAccess = null;
		if (iField.isPrivate())
			fieldAccess = "private";
		else if (iField.isProtected())
			fieldAccess = "protected";
		else if (iField.isPublic() || afIClass.isInterface())
			fieldAccess = "public";
		else
			fieldAccess = "package";
		
		
		// Build method to class map
		Map<MethodReference, IClass> mRefToIClassMap = new HashMap<>();
		for (IClass iClass: allFoundClasses) {
			Collection<IMethod> declaredMethods = iClass.getDeclaredMethods();
			for (IMethod iMethod: declaredMethods) {
				MethodReference ref = iMethod.getReference();
				mRefToIClassMap.put(ref, iClass);
			}
		}
		
		// Find classes of methods candidates
		Set<IClass> classesToProcess = new HashSet<>();
		if (fieldAccess.equals("private")) {
			classesToProcess.add(afIClass);
		} else if (fieldAccess.equals("protected") || fieldAccess.equals("package")) {
			// classes in the same package
			String fieldPackage = this.getPackageOfClass(afIClass);
			for (IClass klass: allFoundClasses) {
				String packageName = this.getPackageOfClass(klass);
				if (fieldPackage.equals(packageName))
					classesToProcess.add(klass);
			}
			if (fieldAccess.equals("protected")) {
				// subclasses
				for (IClass klass: allFoundClasses) {
					IClass superClass = klass;
					do {
						superClass = superClass.getSuperclass();
						if (afIClass.equals(superClass)) {
							classesToProcess.add(klass);
							break;
						}
					} while (superClass != null);
				}
			}
		} else if (fieldAccess.equals("public")) {
			classesToProcess.addAll(allFoundClasses);
		}
		
		// Find method candidates
		Set<MethodReference> methodCandidateSet = new HashSet<>();
		for (IClass klass: classesToProcess) {
			for (IMethod iMethod: klass.getDeclaredMethods()) {
				if (iMethod.isClinit())
					continue;
//				if (iMethod.isInit())
//					continue;
				MethodReference mRef = iMethod.getReference();
				methodCandidateSet.add(mRef);
			}
		}
		
		// iterate over every CM
		for (MethodReference usedCmRef: cmSet) {
			// Check whether the usage of AF is replacing an existing field or a literal
			MethodReference usedCmRefNew = oldToNewMethodRefMap.get(usedCmRef);
			ClientMethod oldClient = oldMRefToClient.get(usedCmRef);
			ClientMethod newClient = newMRefToClient.get(usedCmRefNew);
			ASTNode oldAstNode = oldClient.methodbody;
			ASTNode newAstNode = newClient.methodbody;
			
			// Field Replacement Checker
			//-------------------------------------
//			HashSet<NodePair> treeMatches = oldMethodRefToMatch.get(usedCmRef);
//			if (treeMatches != null) {
//				FieldReplacementDatabaseInserter fpInserter =
//						new FieldReplacementDatabaseInserter(CommitComparator.bugName, afClassName,
//								afName, fieldAccess, usedCmRef.getSignature(), Application.fieldReplacementTable);
//				TopDownTreeMatcher treeMatcher = new TopDownTreeMatcher(afName, afClassName);
//				FieldReplacementChecker fieldChecker =
//						new FieldReplacementChecker(fpInserter, treeMatcher, treeMatches, oldAstNode, newAstNode);
//				fieldChecker.execute();
//			}
			//-------------------------------------
			
			
			
			// Get used CM's IR
//			IClass iClassOfUsedCm = mRefToIClassMap.get(usedCmRef);
//			leftEngine.getCFGBuilder(usedCmRef, iClassOfUsedCm);
//			IR ir = leftEngine.getCurrentIR();
			
			// Inside the CM, get the fields whose class is the same as AF
			boolean afIsConstantNamingPattern = isConstantNamingPattern(afName); 
			Set<String> targetPeerFieldSet = null;
			FieldNameVisitor fieldNameVisitor = new FieldNameVisitor(oldAstNode, afClassSig);
			fieldNameVisitor.execute();
//			targetPeerFieldSet = fieldNameVisitor.getFields();
			Set<String> readFieldsInUsedCm = fieldNameVisitor.getReadFields();
			Set<String> writtenFieldsInUsedCm = fieldNameVisitor.getWrittenFields();
			Set<String> toBeDeletedReadFieldsInUsedCm = new HashSet<>();
			for (String n: readFieldsInUsedCm) {
				if (isConstantNamingPattern(n) != afIsConstantNamingPattern)
					toBeDeletedReadFieldsInUsedCm.add(n);
			}
			readFieldsInUsedCm.removeAll(toBeDeletedReadFieldsInUsedCm);
			Set<String> toBeDeletedWrittenFieldsInUsedCm = new HashSet<>();
			for (String n: writtenFieldsInUsedCm) {
				if (isConstantNamingPattern(n) != afIsConstantNamingPattern)
					toBeDeletedWrittenFieldsInUsedCm.add(n);
			}
			writtenFieldsInUsedCm.removeAll(toBeDeletedWrittenFieldsInUsedCm);
			
			FieldNameVisitor fVisitor = new FieldNameVisitor(newAstNode, afClassSig);
			fVisitor.execute();
			boolean afIsRead = fVisitor.getReadFields().contains(afName);
			boolean afIsWritten = fVisitor.getWrittenFields().contains(afName);
			
			Set<String> readAndWrittenTargetPeerFields = new HashSet<>();
			Set<String> onlyReadTargetPeerFields = new HashSet<>();
			Set<String> onlyWrittenTargetPeerFields = new HashSet<>();
			if (afIsRead && afIsWritten) {
				readAndWrittenTargetPeerFields.addAll(readFieldsInUsedCm);
				readAndWrittenTargetPeerFields.retainAll(writtenFieldsInUsedCm);
//				readAndWrittenTargetPeerFields.remove(afName);
				targetPeerFieldSet = readAndWrittenTargetPeerFields;
			} else if (afIsRead) {
				onlyReadTargetPeerFields.addAll(readFieldsInUsedCm);
				onlyReadTargetPeerFields.removeAll(writtenFieldsInUsedCm);
//				onlyReadTargetPeerFields.remove(afName);
				targetPeerFieldSet = onlyReadTargetPeerFields;
			} else if (afIsWritten) {
				onlyWrittenTargetPeerFields.addAll(writtenFieldsInUsedCm);
				onlyWrittenTargetPeerFields.removeAll(readFieldsInUsedCm);
//				onlyWrittenTargetPeerFields.remove(afName);
				targetPeerFieldSet = onlyWrittenTargetPeerFields;
			} else {
				targetPeerFieldSet = Collections.emptySet();
			}
			
			boolean shouldCheckAccessMode = true; // default plan A, care read and write access
			if (targetPeerFieldSet.size() < 2)  {
				// Plan B, ignore read and write access
				shouldCheckAccessMode = false;
//				targetPeerFieldSet = fieldNameVisitor.getFields();
//				targetPeerFieldSet.remove(afName);
			}
			
			
			Set<MethodReference> predictedCm = new HashSet<>();
			
//			if (targetPeerFieldSet.isEmpty()) {
				// Get the surrounding statements of the statement containing AF
				// 0. Get the AST of new version of used CM
				// 1. Locate the AF statement from AST. To be concise, we only 
				//    locate the first AF statement.
				// 2. Find 2 stmts above AF stmt and 2 stmts below AF stmt
				// 3. Search within every method candidate AST, find statements
				//    similar to the surrounding statements
//				NearStmtFinder nearFinder = new NearStmtFinder(newAstNode, afName, afClassSig);
//				nearFinder.execute();
//				List<ASTNode> stmtsAboveAF = nearFinder.getAboves();
//				List<ASTNode> stmtsBelowAF = nearFinder.getBelows();
//				for (MethodReference mRef: methodCandidateSet) {
//					if (mRef.equals(usedCmRef))
//						continue;
//					ASTNode ast = oMRefToAST.get(mRef);
//					if (ast == null)
//						continue;
//					SimilarStatementMethodChecker statementChecker = 
//							new SimilarStatementMethodChecker(ast, stmtsAboveAF, stmtsBelowAF);
//					statementChecker.execute();
//					if (statementChecker.hasSimilarStatements())
//						predictedCm.add(mRef);
//				}
//			}
			
			
			
			
			
			
			
			// Check every method candidate
			Map<MethodReference, Set<String>> refToFieldsMap = new HashMap<>();
			Map<MethodReference, String> refToPredictedAccessMode = new HashMap<>();  // 3 access modes: "r", "w", "rw"
			for (MethodReference mRef: methodCandidateSet) {
				if (mRef.equals(usedCmRef))
					continue;
//				leftEngine.getCFGBuilder(mRef, mRefToIClassMap.get(mRef));
//				IR candidateIr = leftEngine.getCurrentIR();
				Set<String> peerFieldSet = null;
//				if (mRef.isInit()) {
					ASTNode ast = oMRefToAST.get(mRef);
					if (ast == null) {
						continue;
					}
					FieldNameVisitor fieldVisitor = new FieldNameVisitor(ast, afClassSig);
					fieldVisitor.execute();
//					peerFieldSet = fieldVisitor.getFields();
					Set<String> readFields = fieldVisitor.getReadFields();
					Set<String> writtenFields = fieldVisitor.getWrittenFields();
//					Set<String> toBeDeletedReadFields = new HashSet<>();
//					for (String n: readFields) {
//						if (isConstantNamingPattern(n) != afIsConstantNamingPattern)
//							toBeDeletedReadFields.add(n);
//					}
//					readFields.removeAll(toBeDeletedReadFields);
//					Set<String> toBeDeletedWrittenFields = new HashSet<>();
//					for (String n: writtenFields) {
//						if (isConstantNamingPattern(n) != afIsConstantNamingPattern)
//							toBeDeletedWrittenFields.add(n);
//					}
//					writtenFields.removeAll(toBeDeletedWrittenFields);
					if (shouldCheckAccessMode) {
						// Plan A, peer fields in a candidate method should be accessed in the same way,
						// but their access modes in the candidate method are not necessarily same with
						// those in the known method
//						Set<String> readPeerSet = new HashSet<>();
//						readPeerSet.addAll(readFields);
//						readPeerSet.retainAll(targetPeerFieldSet);
//						Set<String> writtenPeerSet = new HashSet<>();
//						writtenPeerSet.addAll(writtenFields);
//						writtenPeerSet.retainAll(targetPeerFieldSet);
						
						Set<String> onlyReadPeerSet = new HashSet<>();
						onlyReadPeerSet.addAll(readFields);
						onlyReadPeerSet.removeAll(writtenFields);
						onlyReadPeerSet.retainAll(targetPeerFieldSet);
						
						Set<String> onlyWrittenPeerSet = new HashSet<>();
						onlyWrittenPeerSet.addAll(writtenFields);
						onlyWrittenPeerSet.removeAll(readFields);
						onlyWrittenPeerSet.retainAll(targetPeerFieldSet);
						
						Set<String> readAndWrittenPeerSet = new HashSet<>();
						readAndWrittenPeerSet.addAll(readFields);
						readAndWrittenPeerSet.retainAll(writtenFields);
						readAndWrittenPeerSet.retainAll(targetPeerFieldSet);
						
						if (onlyReadPeerSet.size() == 0
								&& onlyWrittenPeerSet.size() == 0
								&& readAndWrittenPeerSet.size() == 0) {
							peerFieldSet = Collections.emptySet();
						} else {
							Comparator<Set<String>> comparator = new Comparator<Set<String>>() {
								@Override
								public int compare(Set<String> o1, Set<String> o2) {
									return o2.size() - o1.size();
								}};
							PriorityQueue<Set<String>> queue = new PriorityQueue<>(3, comparator);
							queue.add(onlyReadPeerSet);
							queue.add(onlyWrittenPeerSet);
							queue.add(readAndWrittenPeerSet);
							peerFieldSet = queue.peek();
							
							// predict the access mode of AF, which be the same as that of peers
							if (peerFieldSet == onlyReadPeerSet)
								refToPredictedAccessMode.put(mRef, "r");
							else if (peerFieldSet == onlyWrittenPeerSet)
								refToPredictedAccessMode.put(mRef, "w");
							else
								refToPredictedAccessMode.put(mRef, "rw");
							
							Set<String> largestPeerSet = queue.poll();
							Set<String> secondLargestPeerSet = queue.poll();
							if (largestPeerSet.size() == secondLargestPeerSet.size())
								refToPredictedAccessMode.put(mRef, "NA");
						}
						
						
					} else {
						// Plan B, ignore read and write access
//						peerFieldSet = fieldVisitor.getFields();
//						peerFieldSet.retainAll(targetPeerFieldSet);
						
						// Now there is no plan B
						peerFieldSet = Collections.emptySet();
						
					}
//					if (afIsRead && afIsWritten) {
//						peerFieldSet.addAll(readFields);
//						peerFieldSet.retainAll(writtenFields);
//						peerFieldSet.retainAll(readAndWrittenTargetPeerFields);
//					} else if (afIsRead) {
//						peerFieldSet.addAll(readFields);
//						peerFieldSet.retainAll(onlyReadTargetPeerFields);
//					} else if (afIsWritten) {
//						peerFieldSet.addAll(writtenFields);
//						peerFieldSet.retainAll(onlyWrittenTargetPeerFields);
//					}
					
//				} else {
//					peerFieldSet = getFieldNames(candidateIr, afClass);
//				}
//				peerFieldSet.retainAll(targetPeerFieldSet);
				refToFieldsMap.put(mRef, peerFieldSet);
			}
			
			// Find the method candidate with most peer fields
			int maxPeerFieldsNum = -1;
			for (Set<String> peerFieldSet: refToFieldsMap.values()) {
				if (peerFieldSet.size() > maxPeerFieldsNum)
					maxPeerFieldsNum = peerFieldSet.size();
			}
			
			if (maxPeerFieldsNum >= 2) {
				for (MethodReference mRef: refToFieldsMap.keySet()) {
					Set<String> peerFieldSet = refToFieldsMap.get(mRef);
					if (peerFieldSet.size() == maxPeerFieldsNum)
						predictedCm.add(mRef);
				}
			}
			
			Set<String> truePositives = new HashSet<>();
			Set<String> falsePositives = new HashSet<>();
			Set<String> falseNegatives = new HashSet<>();
			Map<String, Set<String>> tpVars = new HashMap<>();
			Map<String, Set<String>> fpVars = new HashMap<>();
			Map<String, Set<String>> fnVars = new HashMap<>();
			Set<String> correctAccessPrediction = new HashSet<>();
			Set<String> predictionWithAccess = new HashSet<>();
			Map<String, Map<String, String>> accessDetail = new HashMap<>();
			
			for (MethodReference mRef: cmSet) {
				if (mRef.equals(usedCmRef))
					continue;
				if (predictedCm.contains(mRef)) {
					truePositives.add(mRef.getSignature());
					tpVars.put(mRef.getSignature(), refToFieldsMap.get(mRef));
					
					// process predict_access and access_precision
					
					String realAccess = refToRealAccessMode.get(mRef);
					String predictedAccess = refToPredictedAccessMode.get(mRef);
					if (!predictedAccess.equals("NA")) {
						Map<String, String> realAndPredictedAccess = new HashMap<>();
						realAndPredictedAccess.put("real", realAccess);
						realAndPredictedAccess.put("predicted", predictedAccess);
						accessDetail.put(mRef.getSignature(), realAndPredictedAccess);
						if (realAccess.equals(predictedAccess)) {
							correctAccessPrediction.add(mRef.getSignature());
						}
						predictionWithAccess.add(mRef.getSignature());
					}
				
					
				} else {
					falseNegatives.add(mRef.getSignature());
					fnVars.put(mRef.getSignature(), refToFieldsMap.get(mRef));
				}
			}
			for (MethodReference mRef: predictedCm) {
				if (!cmSet.contains(mRef)) {
					falsePositives.add(mRef.getSignature());
					fpVars.put(mRef.getSignature(), refToFieldsMap.get(mRef));
					
					// process access prediction
					String predictedAccess = refToPredictedAccessMode.get(mRef);
					if (!predictedAccess.equals("NA")) {
						Map<String, String> realAndPredictedAccess = new HashMap<>();
						realAndPredictedAccess.put("real", "none");
						realAndPredictedAccess.put("predicted", predictedAccess);
						accessDetail.put(mRef.getSignature(), realAndPredictedAccess);
						predictionWithAccess.add(mRef.getSignature());
					}
				}
			}
			
			int recall = 100 * truePositives.size() / (cmSet.size() - 1);
			int precision = -1;
			if (!predictedCm.isEmpty())
				precision = 100 * truePositives.size() / predictedCm.size();
			
			int accessPrecision = -1;
			if (!predictionWithAccess.isEmpty())
				accessPrecision = 100 * correctAccessPrediction.size() / predictionWithAccess.size();
			
			// Insert data into database
			Gson gson = new Gson();
			Connection conn = SqliteManager.getConnection();
			try {
				// prediction_cm_neo_derby
				PreparedStatement ps = conn.prepareStatement("INSERT INTO " + Application.neoResultTable
						+ " (bug_name,af_class,af_name,field_access,cm_num,predict_cm_num,recall,precision,"
						+ "used_cm,used_cm_vars,tp,tp_vars,fp,fp_vars,fn,fn_vars,access_precision,access_detail) VALUES "
						+ "(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)");
				ps.setString(1, CommitComparator.bugName);
				ps.setString(2, afClassName);
				ps.setString(3, afName);
				ps.setString(4, fieldAccess);
				ps.setInt(5, cmSet.size());
				ps.setInt(6, predictedCm.size());
				ps.setInt(7, recall);
				if (precision == -1)
					ps.setNull(8, java.sql.Types.INTEGER);
				else
					ps.setInt(8, precision);
				ps.setString(9, usedCmRef.getSignature());
				ps.setString(10, gson.toJson(targetPeerFieldSet));
				ps.setString(11, gson.toJson(truePositives));
				ps.setString(12, gson.toJson(tpVars));
				ps.setString(13, gson.toJson(falsePositives));
				ps.setString(14, gson.toJson(fpVars));
				ps.setString(15, gson.toJson(falseNegatives));
				ps.setString(16, gson.toJson(fnVars));
				if (accessPrecision == -1)
					ps.setNull(17, java.sql.Types.INTEGER);
				else
					ps.setInt(17, accessPrecision);
				ps.setString(18, gson.toJson(accessDetail));
				
				
				ps.executeUpdate();
				ps.close();
				conn.close();
				
			} catch (SQLException e) {
				e.printStackTrace();
			}
			
			
			// Insert data to TABLE false_positives
			conn = SqliteManager.getConnection();
			try {
				PreparedStatement ps = conn.prepareStatement("INSERT INTO " + Application.fpTable
						+ " (bug_name, fp_package, fp_class, fp_method, fp_sig, fp_used_cm,"
						+ "af_class, af_name, af_sig)"
						+ " VALUES (?,?,?,?,?,?,?,?,?)");
				Set<MethodReference> fpSet = new HashSet<>();
				fpSet.addAll(predictedCm);
				fpSet.removeAll(cmSet);
				ps.setString(7, afClassName);
				ps.setString(8, afName);
				ps.setString(9, afRef.getSignature());
				for (MethodReference m: fpSet) {
					ps.setString(1, CommitComparator.bugName);
					ps.setString(2, m.getDeclaringClass().getName().getPackage().toString().replace('/', '.'));
					ps.setString(3, m.getDeclaringClass().getName().getClassName().toString());
					ps.setString(4, m.getName().toString());
					ps.setString(5, m.getSignature());
					ps.setString(6, usedCmRef.getSignature());
					ps.executeUpdate();
				}
				ps.close();
				conn.close();
			} catch (SQLException e) {
				e.printStackTrace();
			}
			//--------------------------------
		}
		
	}
	
	private boolean afIsFieldReplacement(String bugName, String afClass, String afName) {
		Connection conn = SqliteManager.getConnection();
		PreparedStatement ps;
		boolean result = false;
		try {
			ps = conn.prepareStatement("SELECT result FROM field_replacement_result "
					+ "WHERE bug_name=? AND af_class=? AND af_name=?");
			ps.setString(1, bugName);
			ps.setString(2, afClass);
			ps.setString(3, afName);
			ResultSet rs = ps.executeQuery();
			
			if (rs.next())
				result = rs.getString(1).equals("true");
			ps.close();
			conn.close();
		} catch (SQLException e) {
			e.printStackTrace();
		}
		return result;
	}
	
	
	private void analyzeCmAmGraphs(ReferenceNode node, Graph<ReferenceNode, ReferenceEdge> jgrapht,
			Map<MethodReference, MethodReference> newToOldMethodRefMap,
			DataFlowAnalysisEngine leftEngine, DataFlowAnalysisEngine rightEngine) {
		MethodReference amRef = (MethodReference) node.ref;
		TypeReference amClass = amRef.getDeclaringClass();
		String amClassName = amClass.getName().getClassName().toString();
		String amName = amRef.getName().toString();
		System.out.println(amName);
		
////		modified by zijian jiang 02/01/2019
//
//		Set<MethodReference> cmSet = new HashSet<>();
//		Set<String> cms = new HashSet<>();
//
//		for (ReferenceEdge edge: jgrapht.edgesOf(node)) {
//			if (edge.type != ReferenceEdge.METHOD_INVOKE)
//				continue;
//			ReferenceNode srcNode = edge.from;
//			if (srcNode.type != ReferenceNode.CM)
//				continue;
//			MethodReference usedCmRef = (MethodReference) srcNode.ref;
//			cmSet.add(usedCmRef);
//			cms.add(usedCmRef.getSignature());
//		}
//		Connection conn = SqliteManager.getConnection();
//		try{
//			PreparedStatement ps = conn.prepareStatement("INSERT INTO predict_cmam_initial_analysis (bug_name, am_cms) VALUES (?,?)");
//			ps.setString(1, CommitComparator.bugName);
//			Gson gson = new Gson();
//			String detailJson = gson.toJson(cms);
//			ps.setString(2, detailJson);
//			ps.executeUpdate();
//			ps.close();
//			conn.close();
//		} catch (SQLException e) {
//			e.printStackTrace();
//			System.exit(-1);
//		}
//	}

		for (ReferenceEdge edge: jgrapht.edgesOf(node)) {
			if (edge.type != ReferenceEdge.METHOD_INVOKE)
				continue;
			ReferenceNode srcNode = edge.from;
			if (srcNode.type != ReferenceNode.CM)
				continue;
			MethodReference newRef = (MethodReference) srcNode.ref;
			MethodReference mRef = newToOldMethodRefMap.get(newRef);
			
			TypeReference cmClass = mRef.getDeclaringClass();
			String cmClassName = cmClass.getName().getClassName().toString();
			String cmName = mRef.getName().toString();
			System.out.println(cmName);
			
			Connection conn = SqliteManager.getConnection();
			try {
				PreparedStatement ps = conn.prepareStatement("INSERT INTO predict_cmam_initial_analysis (bug_name,am_class,am_name,am_sig,cm_class,cm_name,cm_sig) VALUES (?,?,?,?,?,?,?)");
				ps.setString(1, CommitComparator.bugName);
				ps.setString(2, amClassName);
				ps.setString(3, amName);
				ps.setString(4, amRef.getSignature());
				ps.setString(5, cmClassName);
				ps.setString(6, cmName);
				ps.setString(7, mRef.getSignature());
				System.out.println("can it go through here?");
				ps.executeUpdate();
				ps.close();
				conn.close();
			} catch (SQLException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			
		}
	}
//	
	/**
	 * Check if the var name is like AA_BBER_FWE1, i.e. only contains
	 * Uppercase letters, underscore, or number 
	 * @return
	 */
	private static boolean isConstantNamingPattern(String name) {
		for (char c: name.toCharArray()) {
			if (!Character.isUpperCase(c) && !Character.isDigit(c) && c != '_')
				return false;
		}
		return true;
	}
	
	private boolean hasSwitchInMethod(IR ir) {
		if (ir == null)
			return false;
		for (SSAInstruction instr: ir.getInstructions()) {
			if (instr != null && instr instanceof SSASwitchInstruction) {
				return true;
			}
		}
		return false;
	}
	
	private void insertPredictCMDataToDatabase(List<SqlPredictData> sqlValues) {
		if (!sqlValues.isEmpty()) {
			String resultTable = consolegsydit.Application.predictionCmResultTable;
			if (resultTable == null)
				resultTable = "prediction_cm";
			
			StringBuilder sqlBuilder = new StringBuilder();
			sqlBuilder.append("INSERT INTO ");
			sqlBuilder.append(resultTable);
			sqlBuilder.append(" (bug_name, af_class, af_name, field_access, cm_num, ");
			sqlBuilder.append("predict_cm_num, recall, precision, decisive_template, tp, tp_vars, fp, fp_vars, fn, fn_vars) ");
			sqlBuilder.append("VALUES ");
			
			
			for (int i = 0; i < sqlValues.size() - 1; i++) {
				sqlBuilder.append("(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?),");
			}
			sqlBuilder.append("(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)");
			
			String sql = sqlBuilder.toString();
			
			Connection connection = SqliteManager.getConnection();
			try {
				PreparedStatement stmt = connection.prepareStatement(sql);
				int colNum = 15;
				for (int i = 0; i < sqlValues.size(); i++) {
					SqlPredictData d = sqlValues.get(i); 
					stmt.setString(colNum * i + 1, d.bugName);
					stmt.setString(colNum * i + 2, d.afClass);
					stmt.setString(colNum * i + 3, d.afName);
					stmt.setString(colNum * i + 4, d.fieldAccess);
					stmt.setInt(colNum * i + 5, d.cmNum);
					stmt.setInt(colNum * i + 6, d.predictCmNum);
					stmt.setInt(colNum * i + 7, d.recall);
					if (d.precision == -1)
						stmt.setNull(colNum * i + 8, java.sql.Types.INTEGER);
					else
						stmt.setInt(colNum * i + 8, d.precision);
					stmt.setString(colNum * i + 9, d.decisiveTemplate);
					stmt.setString(colNum * i + 10, d.tp);
					stmt.setString(colNum * i + 11, d.tpVars);
					stmt.setString(colNum * i + 12, d.fp);
					stmt.setString(colNum * i + 13, d.fpVars);
					stmt.setString(colNum * i + 14, d.fn);
					stmt.setString(colNum * i + 15, d.fnVars);
				}
				stmt.executeUpdate();
				stmt.close();
			} catch (SQLException e) {
				e.printStackTrace();
				// System.exit(-1);
			}
			
			try {
				connection.close();
			} catch (SQLException e) {
				e.printStackTrace();
			}
		}
	}
	
	// Added by Ye Wang, 03/22/2017
	// Predict changed methods that should use the added field
	private void predictChangedMethods(ReferenceNode node, Graph<ReferenceNode, ReferenceEdge> jgrapht,
			Map<MethodReference, MethodReference> newToOldMethodRefMap, DataFlowAnalysisEngine leftEngine,
			DataFlowAnalysisEngine rightEngine, Set<IClass> allFoundClasses, List<SqlPredictData> sqlValues) {
		String afName = ((MemberReference) node.ref).getName().toString();
		String afClassName = ((MemberReference)node.ref).getDeclaringClass().getName().getClassName().toString();
		
		// get changed methods
		Set<MethodReference> changedMethodSet = new HashSet<>();
		for (ReferenceEdge edge: jgrapht.edgesOf(node)) {
			ReferenceNode mNode = jgrapht.getEdgeSource(edge);
			MethodReference newRef = (MethodReference)mNode.ref;
			MethodReference mRef = newToOldMethodRefMap.get(newRef);
			changedMethodSet.add(mRef);
		}
		
		//********************************************************
		// This part is for finding the methods with switch-case
//		for (MethodReference mRef: changedMethodSet) {
//			TypeReference typeRef = mRef.getDeclaringClass();
//			IClassHierarchy leftHierarchy = leftEngine.getClassHierarchy();
//			IClass klass = leftHierarchy.lookupClass(typeRef);
//			leftEngine.getCFGBuilder(mRef, klass);
//			IR ir = leftEngine.getCurrentIR();
//			if (hasSwitchInMethod(ir)) {
//				Connection conn = SqliteManager.getConnection();
//				java.sql.Statement stmt = null;
//				try {
//					stmt = conn.createStatement();
//					stmt.executeUpdate("CREATE TABLE IF NOT EXISTS prediction_cm_methods_with_similarly_used_vars (bug_name TEXT,af_class TEXT,af_name TEXT,method TEXT)");
//					
//					PreparedStatement ps = conn.prepareStatement("INSERT INTO prediction_cm_methods_with_similarly_used_vars (bug_name,af_class,af_name,method) VALUES (?,?,?,?)");
//					ps.setString(1, CommitComparator.bugName);
//					ps.setString(2, afClassName);
//					ps.setString(3, afName);
//					ps.setString(4, mRef.getSignature());
//					ps.executeUpdate();
//					ps.close();
//					
//					stmt.close();
//					conn.close();
//				} catch (SQLException e) {
//					// TODO Auto-generated catch block
//					e.printStackTrace();
//				}	
//			}
//		}
		//********************************************************
		
		
		FieldReference fieldRef = (FieldReference)node.ref;
		TypeReference afClass = fieldRef.getDeclaringClass();
		IClassHierarchy rightHierarchy = rightEngine.getClassHierarchy();
		IClass afIClass = rightHierarchy.lookupClass(afClass);
		IField iField = rightHierarchy.resolveField(fieldRef);
		
		String fieldAccessControl;
		Set<IClass> classesToProcess = new HashSet<>();
		IClassHierarchy leftHierarchy = leftEngine.getClassHierarchy();
		if (iField.isPrivate()) {
			// private
			// methods in the same class
			fieldAccessControl = "private";
			TypeReference typeRef = fieldRef.getDeclaringClass();
			IClass klass = leftHierarchy.lookupClass(typeRef);
			classesToProcess = new HashSet<>();
			classesToProcess.add(klass);
			
		} else if (iField.isProtected()) {
			fieldAccessControl = "protected";
			// classes in the same package
			TypeReference typeRef = fieldRef.getDeclaringClass();
			IClass fieldClass = leftHierarchy.lookupClass(typeRef);
			if (fieldClass == null)
				fieldClass = rightHierarchy.lookupClass(typeRef);
			String fieldPackage = this.getPackageOfClass(fieldClass);
			for (IClass klass: allFoundClasses) {
				String packageName = this.getPackageOfClass(klass);
				if (fieldPackage.equals(packageName))
					classesToProcess.add(klass);
			}
			// and subclasses
			for (IClass klass: allFoundClasses) {
				IClass superClass = klass;
				do {
					superClass = superClass.getSuperclass();
					if (fieldClass.equals(superClass)) {
						classesToProcess.add(klass);
						break;
					}
				} while (superClass != null);
			}
			
		} else if (iField.isPublic()  || afIClass.isInterface()) {
			fieldAccessControl = "public";
			// scan all
			classesToProcess = allFoundClasses;
			
		} else {
			// package-private
			fieldAccessControl = "package";
			// classes in the same package
			TypeReference typeRef = fieldRef.getDeclaringClass();
			IClass fieldClass = leftHierarchy.lookupClass(typeRef);
			if (fieldClass == null)
				fieldClass = rightHierarchy.lookupClass(typeRef);
			String fieldPackage = this.getPackageOfClass(fieldClass);
			for (IClass klass: allFoundClasses) {
				String packageName = this.getPackageOfClass(klass);
				if (fieldPackage.equals(packageName))
					classesToProcess.add(klass);
			}
			
		}
		
		Gson gson = new Gson();
		
		// predict output methods
		Map<MethodReference, JsonTemplateEvidence> methodToEvidence = new HashMap<>();
		Set<MethodReference> outputMethods = new HashSet<MethodReference>();
		Map<MethodReference, Set<String>> similarVarsInMethod = new HashMap<>();
		Map<MethodReference, Set<String>> allVarsInMethod = new HashMap<>();
		Map<MethodReference, String> VarRawInfoInMethod = new HashMap<>(); 
		List<MethodReference> scannedMethods = new ArrayList<>();
		
		// Map: method -> templates
		// It's used for ranking all template
		Map<MethodReference, Map<List<String>, List<String>>> methodToTemplates = new HashMap<>();
		
		for (IClass klass: classesToProcess) {
			Collection<IMethod> methods = klass.getDeclaredMethods();
			for (IMethod method: methods) {
				if (method.isClinit())
					continue;
				
				// Don't predict constructors and init()
				if (method.isInit())
					continue;
				MethodReference mRef = method.getReference();
				String methodName = mRef.getName().toString();
				if (methodName.equals("init"))
					continue;
				
				
				
				leftEngine.getCFGBuilder(mRef, klass);
				IR ir = leftEngine.getCurrentIR();
//				Set<String> varSet = this.getVarNames(ir);
				
				
				/* If a method name starts with "get", "set", or "is", and
				 * the name covers all words in the name of one field used
				 * in the method, we don't predict this method.
				 */
				if (methodNameStartsWithGetSetIs(methodName) && methodNameCoverFieldName(methodName, getFieldNames(ir, klass.getReference()))) {
					continue;
				}
				
				
				
				
				Set<String> varSet = getFieldNames(ir, afClass);
				scannedMethods.add(mRef);
				allVarsInMethod.put(mRef, varSet);
				
				// extract template
				Map<List<String>, List<String>> templateToVars = new HashMap<>();
				for (String var: varSet) {
					List<String> complexTemplate = MethodPredictor.extractTemplate(afName, var);
					List<String> template = MethodPredictor.simplifyTemplate(complexTemplate);
					if (!template.isEmpty()) {
						if (templateToVars.containsKey(template)) {
							templateToVars.get(template).add(var);
						} else {
							List<String> vars = new ArrayList<>();
							vars.add(var);
							templateToVars.put(template, vars);
						}
					}
				}
				Map<List<String>, List<String>> mergedTtv = MethodPredictor.mergeTemplates(templateToVars);
//				Map<List<String>, List<String>> mergedTtv = templateToVars;
				methodToTemplates.put(mRef, mergedTtv);
				
				
//				// Analyze the number of words and the length of words in a template
//				List<VariableTemplate> templates = new ArrayList<>();
//				for (List<String> t: templateToVars.keySet()) {
//					List<String> similarVars = templateToVars.get(t);
//					VariableTemplate template = new VariableTemplate(t, similarVars);
//					templates.add(template);
//				}
//				VariableTemplate strongEvidence = null;
//				for (VariableTemplate t: templates) {
//					if (t.isSignificant()) {
//						strongEvidence = t;
//						break;
//					}
//				}
//				List<VariableTemplate> weakEvidence = null;
//				if (strongEvidence == null && VariableTemplate.isSignificant(templates)) {
//					// No strong evidence, has weak evidence
//					weakEvidence = VariableTemplate.extractWeakEvidence(templates);
//				}
//				if (strongEvidence != null || weakEvidence != null) {
//					outputMethods.add(mRef);
//				}
//				
//				List<VariableTemplate> nonEvidence = new ArrayList<>();
//				for (VariableTemplate t: templates) {
//					if (t == strongEvidence)
//						break;
//					boolean isWeakEvidence = false;
//					if (weakEvidence != null) {
//						for (VariableTemplate weak: weakEvidence) {
//							if (t == weak) {
//								isWeakEvidence = true;
//								break;
//							}
//						}
//					}
//					if (!isWeakEvidence)
//						nonEvidence.add(t);
//				}
//				
//				// {
//				//   name: "methodSig",
//				//   evidence: [
//				//     {template: ["mike", "*"], vars:["mikeKan", "mikeGi", "mikeFi"], rating:"weak"},
//				//     {template: [...], vars:[...], rating:"none"}
//				//   ]
//				// }
//				JsonTemplateEvidence jsonEvidence = new JsonTemplateEvidence(mRef.getSignature());
//				if (strongEvidence != null) {
//					jsonEvidence.addTemplate(new JsonTemplateContent(strongEvidence.getTemplate(), strongEvidence.getSimilarVars(), "strong"));
//				} else if (weakEvidence != null) {
//					for (VariableTemplate weak: weakEvidence) {
//						jsonEvidence.addTemplate(new JsonTemplateContent(weak.getTemplate(), weak.getSimilarVars(), "weak"));
//					}
//				}
//				for (VariableTemplate t: nonEvidence) {
//					jsonEvidence.addTemplate(new JsonTemplateContent(t.getTemplate(), t.getSimilarVars(), "none"));
//				}
//				methodToEvidence.put(mRef, jsonEvidence);
				
				JsonTemplateEvidence jsonEvidence = new JsonTemplateEvidence(mRef.getSignature());
				for (List<String> template: mergedTtv.keySet()) {
					List<String> vars = mergedTtv.get(template);
					jsonEvidence.addTemplate(new JsonTemplateContent(template, vars));
				}
				MethodAnalyzer methodAnalyzer = new MethodAnalyzer(ir);
				jsonEvidence.fieldNameList = methodAnalyzer.getFieldNameList();
				jsonEvidence.localNameList = methodAnalyzer.getLocalNameList();
				jsonEvidence.methodNameList = methodAnalyzer.getMethodNameList();
				methodToEvidence.put(mRef, jsonEvidence);
				
				
				
				
				
//				// choose template with more matching variables
//				int maxSize = 0;
//				for (List<String> varList: templateToVars.values()) {
//					if (varList.size() > maxSize)
//						maxSize = varList.size();
//				}
//				Set<List<String>> mostPopularTemplates = new HashSet<>();
//				for (List<String> t: templateToVars.keySet()) {
//					if (templateToVars.get(t).size() == maxSize)
//						mostPopularTemplates.add(t);
//				}
//				List<String> winningTemplate = null;
//				int maxComplexity = 0;
//				for (List<String> t: mostPopularTemplates) {
//					if (t.size() > maxComplexity) {
//						maxComplexity = t.size();
//						winningTemplate = t;
//					}
//				}
//				
//				Set<List<String>> rankCTemplates = new HashSet<>(templateToVars.keySet());
//				rankCTemplates.removeAll(mostPopularTemplates);
//				Set<List<String>> rankBTemplates = new HashSet<>(mostPopularTemplates);
//				rankBTemplates.remove(winningTemplate);
//				
//				if (maxSize >= 2) {
//					outputMethods.add(mRef);
//				}
//				
//				List<List<String>> templateList = new ArrayList<>();
//				List<String> templateRank = new ArrayList<>();
//				
//				if (winningTemplate != null) {
//					templateList.add(winningTemplate);
//					templateRank.add("A");
//				}
//				for (List<String> t: rankBTemplates) {
//					templateList.add(t);
//					templateRank.add("B");
//				}
//				for (List<String> t: rankCTemplates) {
//					templateList.add(t);
//					templateRank.add("C");
//				}
//				
//				StringBuilder rawInfo = new StringBuilder();
//				rawInfo.append("{");
//				for (int j = 0; j < templateList.size(); j++) {
//					rawInfo.append("[");
//					List<String> template = templateList.get(j);
//					if (template == null)
//						System.out.print("");
//					for (String s: template) {
//						rawInfo.append(s);
//						rawInfo.append(",");
//					}
//					rawInfo.append("][");
//					rawInfo.append(templateRank.get(j));
//					rawInfo.append("](");
//					List<String> vars = templateToVars.get(template);
//					for (String var: vars) {
//						rawInfo.append(var);
//						rawInfo.append(",");
//					}
//					rawInfo.append("),");
//				}
//				rawInfo.append("}/{");
//				for (String var: varSet) {
//					rawInfo.append(var);
//					rawInfo.append(",");
//				}
//				rawInfo.append("}");
//				VarRawInfoInMethod.put(mRef, rawInfo.toString());
				
				
				
				
				
				
				// get variable names sharing a pattern with AF name
//				Set<String> patternVars = MethodPredictor.getPatternVars(afName, varSet);
//				similarVarsInMethod.put(mRef, patternVars);
//				
//				if (patternVars.size() >= 2) {
//					outputMethods.add(mRef);
//				}
				
//				// use the majority of variables with similar names
//				int similarNum = 0;
//				for (String var: varSet) {
//					SimilarityChecker checker = new SimilarityChecker(afName, var);
//					if (checker.containsSimilarWord())
//						similarNum++;
//				}
//				if (similarNum >= 2) {
//					outputMethods.add(method.getReference());
//				}
			}
		} // for-loop on class
		
		// Analyze the templates across all methods
		Map<List<String>, List<MethodReference>> templateToMethods = new HashMap<>();
		for (MethodReference mRef: methodToTemplates.keySet()) {
			Map<List<String>, List<String>> ttv = methodToTemplates.get(mRef);
			for (List<String> t: ttv.keySet()) {
				List<String> varList = ttv.get(t);
				if (varList.size() >= 2) {
					if (!templateToMethods.containsKey(t)) {
						templateToMethods.put(t, new ArrayList<MethodReference>());
					}
					templateToMethods.get(t).add(mRef);
				}
			}
		}
		
		// Find the template that has the most characters
		int maxTemplateCharNum = 0;
		List<String> templateHavingMostChars = null;
		for (List<String> template: templateToMethods.keySet()) {
			int templateCharNum = 0;
			for (String w: template) {
				if (!w.equals("*"))
					templateCharNum += w.length();
				if (templateCharNum > maxTemplateCharNum) {
					maxTemplateCharNum = templateCharNum;
					templateHavingMostChars = template;
				}
			}
		}
		if (templateHavingMostChars != null) {
			outputMethods.addAll(templateToMethods.get(templateHavingMostChars));
		}
		
		// compare expected CMs with actual CMs
		// get TP, FN, FP
		// recall = TP / (TP + FN)
		// precision = TP / (TP + FP)
		Set<MethodReference> truePositive = new HashSet<>();
		Set<MethodReference> falsePositive = new HashSet<>();
		Set<MethodReference> falseNegative = new HashSet<>();
		
		for (MethodReference m: outputMethods) {
			if (changedMethodSet.contains(m))
				truePositive.add(m);
			else
				falsePositive.add(m);
		}
		for (MethodReference m: changedMethodSet) {
			if (!outputMethods.contains(m))
				falseNegative.add(m);
		}
		
		int recall = 100 * truePositive.size() / (truePositive.size() + falseNegative.size());
		int precision = -1;
		if (outputMethods.size() > 0)
			precision = 100 * truePositive.size() / (truePositive.size() + falsePositive.size());
		
		SqlPredictData sqlData = new SqlPredictData();
		sqlData.bugName = CommitComparator.bugName;
		sqlData.afClass = afClassName;
		sqlData.afName = afName;
		sqlData.fieldAccess = fieldAccessControl;
		sqlData.cmNum = changedMethodSet.size();
		sqlData.predictCmNum = outputMethods.size();
		sqlData.recall = recall;
		sqlData.precision = precision;
		sqlData.decisiveTemplate = gson.toJson(templateHavingMostChars);
		List<String> tpJson = new ArrayList<>();
		List<JsonTemplateEvidence> tpVarsJson = new ArrayList<>();
		for (MethodReference m: truePositive) {
			tpJson.add(m.getSignature());
			tpVarsJson.add(methodToEvidence.get(m));
		}
		sqlData.tp = gson.toJson(tpJson);
		sqlData.tpVars = gson.toJson(tpVarsJson);
		List<String> fpJson = new ArrayList<>();
		List<JsonTemplateEvidence> fpVarsJson = new ArrayList<>();
		for (MethodReference m: falsePositive) {
			fpJson.add(m.getSignature());
			fpVarsJson.add(methodToEvidence.get(m));
		}
		sqlData.fp = gson.toJson(fpJson);
		sqlData.fpVars = gson.toJson(fpVarsJson);
		List<String> fnJson = new ArrayList<>();
		List<JsonTemplateEvidence> fnVarsJson = new ArrayList<>();
		for (MethodReference m: falseNegative) {
			fnJson.add(m.getSignature());
			fnVarsJson.add(methodToEvidence.get(m));
		}
		sqlData.fn = gson.toJson(fnJson);
		sqlData.fnVars = gson.toJson(fnVarsJson);
		sqlValues.add(sqlData);
		
		
		// output
		// bugName,AFClass,AFName,field_access,CM_num,predictCM_num,recall(%),precision(%),TP,varsInTP,FP,varsInFP,FN,varsInFN
//		StringBuilder output = new StringBuilder();
//		output.append("(");
//		output.append("\"");
//		output.append(CommitComparator.bugName);
//		output.append("\",\"");
//		output.append(afClassName);
//		output.append("\",\"");
//		output.append(afName);
//		output.append("\",\"");
//		output.append(fieldAccessControl);
//		output.append("\",");
//		output.append(changedMethodSet.size());
//		output.append(",");
//		output.append(outputMethods.size());
//		output.append(",");
//		output.append(recall);
//		output.append(",");
//		if (precision == -1)
//			output.append("NULL");
//		else
//			output.append(precision);
//		output.append(",");
//		
//		output.append("\"");
//		for (MethodReference m: truePositive) {
//			output.append(m.getSignature());
//			output.append(",");
//		}
//		output.append("\"");
//		output.append(",");
//		
//		output.append("\"");
//		for (MethodReference m: truePositive) {
//			output.append(m.getSignature());
//			output.append("=");
//			output.append(VarRawInfoInMethod.get(m));
//			output.append(",");
//		}
//		output.append("\"");
//		output.append(",");
//		
//		output.append("\"");
//		for (MethodReference m: falsePositive) {
//			output.append(m.getSignature());
//			output.append(",");
//		}
//		output.append("\"");
//		output.append(",");
//		
//		output.append("\"");
//		for (MethodReference m: falsePositive) {
//			output.append(m.getSignature());
//			output.append("=");
//			output.append(VarRawInfoInMethod.get(m));
//			output.append(",");
//		}
//		output.append("\"");
//		output.append(",");
//		
//		output.append("\"");
//		for (MethodReference m: falseNegative) {
//			output.append(m.getSignature());
//			output.append(",");
//		}
//		output.append("\"");
//		output.append(",");
//		
//		output.append("\"");
//		for (MethodReference m: falseNegative) {
//			output.append(m.getSignature());
//			output.append("=");
//			output.append(VarRawInfoInMethod.get(m));
//			output.append(",");
//		}
//		output.append("\"");
//		output.append(")");
//		sqlValues.add(output.toString());
	}
	
	private boolean methodNameStartsWithGetSetIs(String methodName) {
		return methodName.startsWith("get") || methodName.startsWith("set") || methodName.startsWith("is");
	}
	
	
	/**
	 * Check if a method name contains all words in the name of any of the fields used in the method
	 * @param methodName
	 * @param fieldNames
	 * @return true if the method name covers field name words.
	 */
	private boolean methodNameCoverFieldName(String methodName, Set<String> fieldNames) {
		String lowerMethodName = methodName.toLowerCase();
		for (String field: fieldNames) {
			List<String> fieldWords = NameProcessor.split(field);
			boolean containsAllWords = true;
			for (String w: fieldWords) {
				if (!lowerMethodName.contains(w.toLowerCase())) {
					containsAllWords = false;
					break;
				}
			}
			if (containsAllWords)
				return true;
		}
		
		return false;
	}


	// added by Ye Wang, 03/20/2017
	// Used to find the package of a class
	private String getPackageOfClass(IClass klass) {
		com.ibm.wala.types.TypeName typeName = klass.getName();
		String packageName = null;
		try {
			Object typeNameKey = this.getPrivateFieldValue(typeName, "key");
			Object packageNameAtom = this.getPrivateFieldValue(typeNameKey, "packageName");
			if (packageNameAtom == null)
				return null;
			else
				packageName = packageNameAtom.toString();
		} catch (NoSuchFieldException e) {
			e.printStackTrace();
			consolegsydit.ExceptionHandler.process(e);
		}
		return packageName;
	}
	
	
	// added by Ye Wang, 02/08/2017
	private void analyzePeerVariable(Graph<ReferenceNode, ReferenceEdge> graph, Map<MethodReference, MethodReference> newToOldMethodRefMap, DataFlowAnalysisEngine leftEngine) {
		for (ReferenceNode node: graph.vertexSet()) {
			// for every AF
			if (node.type == ReferenceNode.AF) {
				String afName = ((MemberReference) node.ref).getName().toString();
				String afClassName = ((MemberReference) node.ref).getDeclaringClass().getName().getClassName().toString();
				// get changed methods
				Set<MethodReference> changedMethodSet = new HashSet<>();
				for (ReferenceEdge edge: graph.edgesOf(node)) {
					ReferenceNode mNode = graph.getEdgeSource(edge);
					MethodReference newRef = (MethodReference)mNode.ref;
					MethodReference mRef = newToOldMethodRefMap.get(newRef);
					changedMethodSet.add(mRef);
				}
				// get all classes using a changed method
				Set<IClass> classSet = new HashSet<>();
				for (MethodReference m: changedMethodSet) {
					TypeReference typeRef = m.getDeclaringClass();
					IClassHierarchy cha = leftEngine.getClassHierarchy();
					IClass klass = cha.lookupClass(typeRef);
					classSet.add(klass);
				}
				Set<IMethod> allIMethodSet = new HashSet<>();
				Map<IClass, Set<IMethod>> classToMethodMap = new HashMap<>();
				for (IClass klass: classSet) {
					allIMethodSet.addAll(klass.getDeclaredMethods());
					classToMethodMap.put(klass, new HashSet<IMethod>(klass.getDeclaredMethods()));
				}
				Map<MethodReference, IR> mRefToIR = new HashMap<>();
				for (IClass klass: classToMethodMap.keySet()) {
					for (IMethod m: classToMethodMap.get(klass)) {
						leftEngine.getCFGBuilder(m.getReference(), klass);
						IR ir = leftEngine.getCurrentIR();
						mRefToIR.put(m.getReference(), ir);
					}
				}
				Set<MethodReference> allMethodSet = new HashSet<>();
				allMethodSet.addAll(mRefToIR.keySet());
				
				List<Set<String>> varSetList = new ArrayList<Set<String>>();
				Map<MethodReference, Set<String>> mRefToVarMap = new HashMap<>();
				for (MethodReference mRef: mRefToIR.keySet()) {
					IR ir = mRefToIR.get(mRef);
					Set<String> varNames = this.getVarNames(ir);
					varSetList.add(varNames);
					mRefToVarMap.put(mRef, varNames);
				}
				
				if (changedMethodSet.size() >= 2) {
					Map<String, Integer> varInChangedMethod = new HashMap<>();
					Map<String, Integer> varInAllMethod = new HashMap<>();
					for (MethodReference m: changedMethodSet) {
						Set<String> vars = mRefToVarMap.get(m);
						for (String v: vars) {
							if (!varInChangedMethod.containsKey(v))
								varInChangedMethod.put(v, 1);
							else
								varInChangedMethod.put(v, varInChangedMethod.get(v) + 1);
						}
					}
					for (MethodReference m: allMethodSet) {
						Set<String> vars = mRefToVarMap.get(m);
						for (String v: vars) {
							if (!varInAllMethod.containsKey(v))
								varInAllMethod.put(v, 1);
							else
								varInAllMethod.put(v, varInAllMethod.get(v) + 1);
						}
					}
					List<Map.Entry<String, Integer>> sortedVarNumInCM = new ArrayList<>(varInChangedMethod.entrySet());
					Comparator<Map.Entry<String, Integer>> comparatorForVarNum = new Comparator<Map.Entry<String, Integer>>() {
						@Override
						public int compare(Map.Entry<String, Integer> a, Map.Entry<String, Integer> b) {
							return b.getValue() - a.getValue();
						}
					};
					Collections.sort(sortedVarNumInCM, comparatorForVarNum);
					List<String> completeVarList = new ArrayList<>();
					List<String> partialVarList = new ArrayList<>();
					int cmNum = changedMethodSet.size();
					for (Map.Entry<String, Integer> e: sortedVarNumInCM) {
						if (((Integer)e.getValue()).intValue() == cmNum)
							completeVarList.add(e.getKey());
						else
							partialVarList.add(e.getKey());
					}
					
					// write info to file
					// bugName,AFClass,AFName,cmNum,allMethodNum,classNum,
					// completeVarNum,partialVarNum,completeVars(numInAllM),partialVars(numInCM/numInAllM)
					StringBuilder output = new StringBuilder(CommitComparator.bugName);
					output.append(",");
					output.append(afClassName);
					output.append(",");
					output.append(afName);
					output.append(",");
					output.append(changedMethodSet.size());
					output.append(",");
					output.append(allMethodSet.size());
					output.append(",");
					output.append(classSet.size());
					output.append(",");
					output.append(completeVarList.size());
					output.append(",");
					output.append(partialVarList.size());
					output.append(",");
					for (String var: completeVarList) {
						output.append(var);
						output.append("(");
						output.append(varInAllMethod.get(var));
						output.append(");");
					}
					output.append(",");
					for (String var: partialVarList) {
						output.append(var);
						output.append("(");
						output.append(varInChangedMethod.get(var));
						output.append("/");
						output.append(varInAllMethod.get(var));
						output.append(");");
					}
					output.append("\n");
					
					Path peerOutputPath = FileSystems.getDefault().getPath("/Users/zijianjiang/Documents/NaM/peerVars.csv");
					try {
						Files.write(peerOutputPath, output.toString().getBytes(), APPEND);
					} catch (IOException e) {
						e.printStackTrace();
					}
					
				}

			}
		}
	}
	
	/**
	 * Get the names of fields used in a method, and the field must be in the same
	 * class of AF. 
	 * @param ir the IR of a method
	 * @param afClass class of AF
	 * @return set of field names
	 */
	private Set<String> getFieldNames(IR ir, TypeReference afClass) {
		if (ir == null)
			return Collections.emptySet();
		// get fields
		Set<String> fieldNames = new HashSet<String>();
		for (SSAInstruction instr: ir.getInstructions()) {
			if (instr instanceof SSAFieldAccessInstruction) {
				SSAFieldAccessInstruction fInstr = (SSAFieldAccessInstruction)instr;
				FieldReference fieldRef = fInstr.getDeclaredField();
				
				// check if the field is in the same class as AF
				if (afClass.equals(fieldRef.getDeclaringClass())) {
					String fieldName = fieldRef.getName().toString();
					fieldNames.add(fieldName);
				}
			}
		}
		return fieldNames;
	}
	
	/**
	 * Get the names of fields and local variables of a method
	 * @param ir the IR of a method
	 * @return set of variable names
	 */
	private Set<String> getVarNames(IR ir) {
		if (ir == null)
			return Collections.emptySet();
		// get fields
		Set<String> fieldNames = new HashSet<String>();
		for (SSAInstruction instr: ir.getInstructions()) {
			if (instr instanceof SSAFieldAccessInstruction) {
				SSAFieldAccessInstruction fInstr = (SSAFieldAccessInstruction)instr;
				FieldReference fieldRef = fInstr.getDeclaredField();
				String fieldName = fieldRef.getName().toString();
				fieldNames.add(fieldName);
			}
		}
		
		// get local variables
//		Set<String> localVars = new HashSet<String>();
//		SSAInstruction[] instructions = ir.getInstructions();
//		for (int instrIndex = 0; instrIndex < instructions.length; instrIndex++) {
//			SSAInstruction instr = instructions[instrIndex];
//			if (instr != null) {
//				try {
//					int def = instr.getDef();
//					if (def != -1) {
//						String[] localNames = ir.getLocalNames(instrIndex, def);
//						if (localNames.length == 1) {
//							String localName = localNames[0];
//							localVars.add(localName);
//						}
//					}
//				} catch (NullPointerException x) {
//					// do nothing, just skip this one
//				}
//			}
//		}
		
		// get local vars through valueNumberNames[][]
		// Indices start from 1, 0 is not used. For non-static method, index 1 is this.
		String[][] valueNumberNames = null;
		try {
			Object localMap = this.getPrivateFieldValue(ir, "localMap");
			Object dontKnowWhatItIs = this.getPrivateFieldValue(localMap, "this$0");
			Object debugInfo = this.getPrivateFieldValueInSuperClass(dontKnowWhatItIs, "debugInfo");
			valueNumberNames = (String[][])this.getPrivateFieldValue(debugInfo, "valueNumberNames");
		} catch (NoSuchFieldException e) {
			e.printStackTrace();
			consolegsydit.ExceptionHandler.process(e);
		}
		Set<String> localVars = new HashSet<String>();
		// check if the method is a static method
		if (valueNumberNames.length >= 2 && valueNumberNames[1].length == 1 && !valueNumberNames[1][0].equals("this")) {
			localVars.add(valueNumberNames[1][0]);
		}
		for (int i = 2; i < valueNumberNames.length; i++) {
			if (valueNumberNames[i].length == 1)
				localVars.add(valueNumberNames[i][0]);
		}
		
		// merge fields and local variables
		Set<String> fieldsAndLocals = new HashSet<String>();
		fieldsAndLocals.addAll(fieldNames);
		fieldsAndLocals.addAll(localVars);
		
		return fieldsAndLocals;
	}
	
	private Object getPrivateFieldValue(Object c, String fieldName) throws NoSuchFieldException {
		Class<?> klass = c.getClass();
		Field field = null;
		try {
			field = klass.getDeclaredField(fieldName);
		} catch (SecurityException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
			consolegsydit.ExceptionHandler.process(e);
		}
		
		field.setAccessible(true);
		Object fieldObject = null;
		try {
			fieldObject = field.get(c);
		} catch (IllegalArgumentException | IllegalAccessException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
			consolegsydit.ExceptionHandler.process(e);
		}
//		field.setAccessible(false);
		
		return fieldObject;
	}
	
	private Object getPrivateFieldValueInSuperClass(Object c, String fieldName) throws NoSuchFieldException {
		Class<?> klass = c.getClass();
		Class<?> superClass = (Class<?>) klass.getGenericSuperclass();
		Field field = null;
		try {
			field = superClass.getDeclaredField(fieldName);
		} catch (SecurityException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
			consolegsydit.ExceptionHandler.process(e);
		}
		
		field.setAccessible(true);
		Object fieldObject = null;
		try {
			fieldObject = field.get(c);
		} catch (IllegalArgumentException | IllegalAccessException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
			consolegsydit.ExceptionHandler.process(e);
		}
//		field.setAccessible(false);
		
		return fieldObject;
	}
	
	// Added by Ye Wang, 10/29/2016
	// store the found graphs in the first parameter graphs
	@Deprecated
	private void analyzeChangeLink(List<DirectedSparseGraph<ReferenceNode, ReferenceEdge>> graphs,
			DataFlowAnalysisEngine leftEngine, DataFlowAnalysisEngine rightEngine,
			Set<ClientMethod> oldChangedMethods, Set<ClientMethod> newChangedMethods,
			Set<ClientMethod> insertedMethods, Set<ClientMethod> deletedMethods,
			Set<MethodReference> changedMethodRefs, Set<MethodReference> insertedMethodRefs,
			Set<MethodReference> deletedMethodRefs, Set<FieldReference> insertedFieldRefs,
			Set<FieldReference> deletedFieldRefs, Map<ClientMethod, List<SourceCodeRange>> oldMethodToRange,
			Map<ClientMethod, List<SourceCodeRange>> newMethodToRange) {	
		analyzeFieldAccess(graphs, leftEngine, oldChangedMethods, ReferenceNode.CM,
				deletedFieldRefs, ReferenceNode.DF);
		analyzeFieldAccess(graphs, leftEngine, deletedMethods, ReferenceNode.DM,
				deletedFieldRefs, ReferenceNode.DF);
		analyzeFieldAccess(graphs, rightEngine, newChangedMethods, ReferenceNode.CM,
				insertedFieldRefs, ReferenceNode.AF);
		analyzeFieldAccess(graphs, rightEngine, insertedMethods, ReferenceNode.AM,
				insertedFieldRefs, ReferenceNode.AF);
		
		analyzeMethodToMethod(graphs, leftEngine, oldChangedMethods, ReferenceNode.CM,
				oldMethodToRange, deletedMethodRefs, ReferenceNode.DM);
		analyzeMethodToMethod(graphs, leftEngine, oldChangedMethods, ReferenceNode.CM,
				oldMethodToRange, changedMethodRefs, ReferenceNode.CM);
		analyzeMethodToMethod(graphs, leftEngine, deletedMethods, ReferenceNode.DM,
				null, deletedMethodRefs, ReferenceNode.DM);
		analyzeMethodToMethod(graphs, leftEngine, deletedMethods, ReferenceNode.DM,
				null, changedMethodRefs, ReferenceNode.CM);
		analyzeMethodToMethod(graphs, rightEngine, newChangedMethods, ReferenceNode.CM,
				newMethodToRange, insertedMethodRefs, ReferenceNode.AM);
		analyzeMethodToMethod(graphs, rightEngine, newChangedMethods, ReferenceNode.CM,
				newMethodToRange, changedMethodRefs, ReferenceNode.CM);
		analyzeMethodToMethod(graphs, rightEngine, insertedMethods, ReferenceNode.AM,
				null, insertedMethodRefs, ReferenceNode.AM);
		analyzeMethodToMethod(graphs, rightEngine, insertedMethods, ReferenceNode.AM,
				null, changedMethodRefs, ReferenceNode.CM);
	}
	
	private void analyzeFieldAccess(List<DirectedSparseGraph<ReferenceNode, ReferenceEdge>> graphs,
			DataFlowAnalysisEngine engine, Set<ClientMethod> methods, int rootMethodNodeType,
			Set<FieldReference> fieldRefs, int fieldNodeType) {
		if (fieldRefs.isEmpty()) return;
		for (ClientMethod m: methods) {
			DirectedSparseGraph<ReferenceNode, ReferenceEdge> graph =
					new DirectedSparseGraph<ReferenceNode, ReferenceEdge>();
			graphs.add(graph);
			ReferenceNode root = new ReferenceNode(m.mRef, rootMethodNodeType);
			engine.getCFGBuilder(m);
			IR ir = engine.getCurrentIR();
			if (ir == null)
				continue;
			for (SSAInstruction instr: ir.getInstructions()) {
				if (instr == null)
					continue;
				if (!fieldRefs.isEmpty() && instr instanceof SSAFieldAccessInstruction) {
					SSAFieldAccessInstruction sInstr = (SSAFieldAccessInstruction)instr;
					FieldReference fRef = sInstr.getDeclaredField();
					if (fieldRefs.contains(fRef)) {
						ReferenceNode n = new ReferenceNode(fRef, fieldNodeType);
						ReferenceEdge edge = graph.findEdge(root, n);
						if (edge == null) {
							edge = new ReferenceEdge(root, n, ReferenceEdge.FIELD_ACCESS);
							graph.addEdge(edge, root, n);
						}
						edge.increaseCount();
					}
				}
			}
		}
	}
	
	private void analyzeMethodToMethod(List<DirectedSparseGraph<ReferenceNode, ReferenceEdge>> graphs,
			DataFlowAnalysisEngine engine, Set<ClientMethod> methods, int rootMethodNodeType,
			Map<ClientMethod, List<SourceCodeRange>> methodToRange,
			Set<MethodReference> methodRefs, int methodNodeType) {
		if (methodRefs.isEmpty()) return;
		for (ClientMethod m: methods) {
			DirectedSparseGraph<ReferenceNode, ReferenceEdge> graph =
					new DirectedSparseGraph<ReferenceNode, ReferenceEdge>();
			graphs.add(graph);
			ReferenceNode root = new ReferenceNode(m.mRef, rootMethodNodeType);
					
			// Analyze method invocation
			engine.getCFGBuilder(m);
			IR ir = engine.getCurrentIR();
			if (ir == null)
				continue;
			
			// Build sdg for dependency analysis
			boolean dependencyAnalysisHasProblem = false;
			SDG sdg = engine.buildSystemDependencyGraph2(m);
			if (sdg == null)
				dependencyAnalysisHasProblem = true;
			CGNode cgNode = null;
			PDG pdg = null;
			Map<SSAInstruction, Integer> instructionIndices = null;
			ConcreteJavaMethod concreteJavaMethod = null;
			List<LineRange> lineRanges = null;
			if (!dependencyAnalysisHasProblem) {
				CallGraph callGraph = sdg.getCallGraph();
				Set<CGNode> cgNodeSet =callGraph.getNodes(m.mRef);
				boolean cgNodeSetIsEmpty = false;
				if (cgNodeSet.isEmpty()) {
					System.err.println("cgNodeSet is empty! ");
					final boolean writeEmptyCGNodeLog = false;
					if (writeEmptyCGNodeLog) {
						String emptyCGNodeLog = "/Users/zijianjiang/Documents/NaM/emptyCGNode.txt";
						Path logPath = FileSystems.getDefault().getPath(emptyCGNodeLog);
						String logInfo = m.toString() + "\n";
						try {
							Files.write(logPath, logInfo.getBytes(), CREATE, APPEND);
						} catch (IOException e) {
							System.err.println(e.getMessage());
						}
					}
					cgNodeSetIsEmpty = true;
					dependencyAnalysisHasProblem = true;
				}
				if (!cgNodeSetIsEmpty) {
	//			CGNode cgNode = callGraph.getNode(0);
					cgNode = cgNodeSet.iterator().next();
					pdg = sdg.getPDG(cgNode);
					instructionIndices = PDG.computeInstructionIndices(ir);
					
					
					concreteJavaMethod = (ConcreteJavaMethod)cgNode.getMethod();
					lineRanges = null;
					// Changed Method, not AM or DM
					if (methodToRange != null) {
						// build a map from instruction index to line number
						Map<Integer, Integer> indexToLine = new HashMap<Integer, Integer>();
						Iterator<Statement> it = pdg.iterator();
						while (it.hasNext()) {
							Statement stmt = it.next();
							int instructionIndex;
							if (stmt instanceof StatementWithInstructionIndex) {
								StatementWithInstructionIndex stmtWithIndex = (StatementWithInstructionIndex)stmt;
								instructionIndex = stmtWithIndex.getInstructionIndex();
							} else {
								continue;
							}
							int lineNumber = concreteJavaMethod.getLineNumber(instructionIndex);
							indexToLine.put(instructionIndex, lineNumber);
						}
						
						// find the changed line range
						List<SourceCodeRange> ranges = methodToRange.get(m);
						lineRanges = new ArrayList<LineRange>();
						for (SourceCodeRange range: ranges) {
							CompilationUnit cu = (CompilationUnit)m.ast;
							LineRange lineRange = LineRange.get(cu, range);
							lineRanges.add(lineRange);
						}
					}
				}
			
			}
			
			
			
			
			for (SSAInstruction instr: ir.getInstructions()) {
				if (instr == null)
					continue;
				if (!methodRefs.isEmpty() && (instr instanceof SSAAbstractInvokeInstruction)) {
					MethodReference mRef = ((SSAAbstractInvokeInstruction)instr).getDeclaredTarget();
					if (methodRefs.contains(mRef)) {
						ReferenceNode n = new ReferenceNode(mRef, methodNodeType);
						ReferenceEdge edge = graph.findEdge(root, n);
						if (edge == null) {
							edge = new ReferenceEdge(root, n, ReferenceEdge.METHOD_INVOKE);
							graph.addEdge(edge, root, n);
						}
						edge.increaseCount();
						
						if (!dependencyAnalysisHasProblem) {
							// Analyze dependency
							Statement statement = PDG.ssaInstruction2Statement(cgNode, instr, instructionIndices, ir);
							
							
							
	//						Iterator<Statement> DepSuccIter = pdg.getSuccNodes(statement);
	//						while (DepSuccIter.hasNext()) {
	//							Statement succStmt = DepSuccIter.next();
	//							if (pdg.isControlDependend(statement, succStmt)) {
	//								// another statement is control-dependent on callee
	//								edge.dep |= ReferenceEdge.OTHER_CONTROL_DEP_CALLEE;
	//							} else {
	//								// another statement is data-dependent on callee
	//								edge.dep |= ReferenceEdge.OTHER_DATA_DEP_CALLEE;
	//							}
	//						}
							
							
							Iterator<Statement> stmtIter = pdg.iterator();
							while (stmtIter.hasNext()) {
								// check whether callee is dependent on another statement
								Statement stmt = stmtIter.next();
								
								
								// check if stmt is changed statement
								boolean statementIsChanged = false;
								if (methodToRange != null) { // for CM
									boolean canGetIndex = true;
									// from Statement to instruction index
									int instructionIndex = -1;
									if (stmt instanceof StatementWithInstructionIndex) {
										StatementWithInstructionIndex stmtWithIndex = (StatementWithInstructionIndex)stmt;
										instructionIndex = stmtWithIndex.getInstructionIndex();
									} else if (stmt instanceof GetCaughtExceptionStatement) {
										GetCaughtExceptionStatement s = (GetCaughtExceptionStatement)stmt;
										SSAInstruction instruction = s.getInstruction();
										instructionIndex = instruction.iindex;
									} else {
										canGetIndex = false;
									}
									if (canGetIndex) {
										// from instruction index to line number
										int lineNumber = concreteJavaMethod.getLineNumber(instructionIndex);
										
										// check if line number is in line ranges
										for (LineRange range: lineRanges) {
											if (lineNumber >= range.startLine && lineNumber <= range.endLine) {
												statementIsChanged = true;
												break;
											}
										}
									}
								} else { // for AM or DM
									statementIsChanged = true;
								}
								
								if (!statementIsChanged)
									continue;
								
								
								if (pdg.hasEdge(stmt, statement)) {
									// callee is dependent on another statement
									if (pdg.isControlDependend(stmt, statement)) {
										// control dependent
										edge.dep |= ReferenceEdge.CALLEE_CONTROL_DEP_OTHER;
									} else {
										// data dependent
										edge.dep |= ReferenceEdge.CALLEE_DATA_DEP_OTHER;
									}
								}
								
								if (pdg.hasEdge(statement, stmt)) {
									// another statement is dependent on callee
									if (pdg.isControlDependend(statement, stmt)) {
										// control dependent
										edge.dep |= ReferenceEdge.OTHER_CONTROL_DEP_CALLEE;
									} else {
										// data dependent
										edge.dep |= ReferenceEdge.OTHER_DATA_DEP_CALLEE;
									}
								}
								
							}
						}
						
					}
				}
			}
			
			
			
			// Analyze method overriding
			MethodReference mRef = m.mRef;
			if (mRef == null)
				continue;
			TypeReference typeRef = mRef.getDeclaringClass();
			IClassHierarchy cha = engine.getClassHierarchy();
			IMethod method = cha.resolveMethod(mRef);
			Selector selector = method.getSelector();
			IClass klass = cha.lookupClass(typeRef);
			Collection<? extends IClass> directInterfaces = klass.getDirectInterfaces();
			IClass superclass = klass.getSuperclass();
			Set<IClass> supertypes = new HashSet<IClass>(directInterfaces);
			if (superclass != null)
				supertypes.add(superclass);
			for (IClass supertype: supertypes) {
				Collection<IMethod> supertypeMethods = supertype.getDeclaredMethods();
				for (IMethod supertypeMethod: supertypeMethods) {
					Selector supertypeMethodSelector = supertypeMethod.getSelector();
					if (selector.equals(supertypeMethodSelector)) {
						MethodReference suptertypeMRef = supertypeMethod.getReference();
						if (methodRefs.contains(suptertypeMRef)) {
							ReferenceNode n = new ReferenceNode(suptertypeMRef, methodNodeType);
							ReferenceEdge edge = graph.findEdge(root, n);
							if (edge == null) {
								edge = new ReferenceEdge(root, n, ReferenceEdge.METHOD_OVERRIDE);
								graph.addEdge(edge, root, n);
							}
							edge.increaseCount();
						}
					}
				}
			}
			
		}
	}
	
//	private void analyzeMethodOverride(List<DirectedSparseGraph<ReferenceNode, ReferenceEdge>> graphs,
//			DataFlowAnalysisEngine engine, Set<ClientMethod> methods, int rootMethodNodeType,
//			Set<MethodReference> methodRefs, int methodNodeType) {
//		for (ClientMethod m: methods) {
//			DirectedSparseGraph<ReferenceNode, ReferenceEdge> graph =
//					new DirectedSparseGraph<ReferenceNode, ReferenceEdge>();
//			graphs.add(graph);
//			ReferenceNode root = new ReferenceNode(m.mRef, rootMethodNodeType);
//			MethodReference mRef = m.mRef;
//			TypeReference typeRef = mRef.getDeclaringClass();
//			IClassHierarchy cha = engine.getClassHierarchy();
//			IMethod method = cha.resolveMethod(mRef);
//			Selector selector = method.getSelector();
//			IClass klass = cha.lookupClass(typeRef);
//			Collection<? extends IClass> directInterfaces = klass.getDirectInterfaces();
//			IClass superclass = klass.getSuperclass();
//			Set<IClass> supertypes = new HashSet<IClass>(directInterfaces);
//			if (superclass != null)
//				supertypes.add(superclass);
//			for (IClass supertype: supertypes) {
//				Collection<IMethod> supertypeMethods = supertype.getDeclaredMethods();
//				for (IMethod supertypeMethod: supertypeMethods) {
//					Selector supertypeMethodSelector = supertypeMethod.getSelector();
//					if (selector.equals(supertypeMethodSelector)) {
//						MethodReference suptertypeMRef = supertypeMethod.getReference();
//						if (methodRefs.contains(suptertypeMRef)) {
//							ReferenceNode n = new ReferenceNode(suptertypeMRef, methodNodeType);
//							ReferenceEdge edge = graph.findEdge(root, n);
//							if (edge == null) {
//								edge = new ReferenceEdge(root, n, ReferenceEdge.METHOD_OVERRIDE);
//								graph.addEdge(edge, root, n);
//							}
//							edge.increaseCount();
//						}
//					}
//				}
//			}
//		}
//	}
	
//	private void analyzePartialChangeLink(List<DirectedSparseGraph<ReferenceNode, ReferenceEdge>> graphs,
//			DataFlowAnalysisEngine engine, Set<ClientMethod> methods,
//			Set<MethodReference> changedMethodRefs, int changedMethodNodeType,
//			Set<MethodReference> methodRefs2, int methodNodeType2,
//			Set<FieldReference> fieldRefs, int fieldNodeType) {
//		for (ClientMethod m: methods) {
//			DirectedSparseGraph<ReferenceNode, ReferenceEdge> graph = new DirectedSparseGraph<ReferenceNode, ReferenceEdge>();
//			graphs.add(graph);
//			ReferenceNode root = new ReferenceNode(m.mRef, ReferenceNode.CM);
//			engine.getCFGBuilder(m);
//			IR ir = engine.getCurrentIR();
//			if (ir == null)
//				continue;
//			for (SSAInstruction instr: ir.getInstructions()) {
//				if (instr == null)
//					continue;
//				if (instr instanceof SSAAbstractInvokeInstruction) {
//					MethodReference mRef = ((SSAAbstractInvokeInstruction)instr).getDeclaredTarget();
//					if (changedMethodRefs.contains(mRef)) {
//						// The node is a changed method node
//						ReferenceNode n = new ReferenceNode(mRef, changedMethodNodeType);
//						ReferenceEdge edge = graph.findEdge(root, n);
//						if (edge == null) {
//							edge = new ReferenceEdge(root, n, ReferenceEdge.METHOD_INVOKE);
//							graph.addEdge(edge, root, n);
//						}
//						edge.increaseCount();
//					} else if (methodRefs2.contains(mRef)) {
//						ReferenceNode n = new ReferenceNode(mRef, methodNodeType2);
//						ReferenceEdge edge = graph.findEdge(root, n);
//						if (edge == null) {
//							edge = new ReferenceEdge(root, n, ReferenceEdge.METHOD_INVOKE);
//							graph.addEdge(edge, root, n);
//						}
//						edge.increaseCount();
//					}
//				}
//			}
//		}
//	}

	private static List<DirectedSparseGraph<ReferenceNode, ReferenceEdge>> convertNewVersionToOldVersion(
			List<DirectedSparseGraph<ReferenceNode, ReferenceEdge>> graphs,
			Map<? extends MemberReference, ? extends MemberReference> newToOldVersionMap) {
		List<DirectedSparseGraph<ReferenceNode, ReferenceEdge>> result = new ArrayList<>();
		for (DirectedSparseGraph<ReferenceNode, ReferenceEdge> graph: graphs) {
			
			if (graph.getVertexCount() == 0)
				continue;
			
			DirectedSparseGraph<ReferenceNode, ReferenceEdge> modifiedGraph =
					new DirectedSparseGraph<ReferenceNode, ReferenceEdge>();
			
			Map<MemberReference, ReferenceNode> refToNode = new HashMap<>();
			
			Collection<ReferenceNode> vertices = graph.getVertices();
			for (ReferenceNode vertex: vertices) {
				if (newToOldVersionMap.containsKey(vertex.ref)) {
					MemberReference oldVersionRef = newToOldVersionMap.get(vertex.ref);
					ReferenceNode oldVersionVertex = new ReferenceNode(oldVersionRef, vertex.type);
					modifiedGraph.addVertex(oldVersionVertex);
					refToNode.put((MemberReference) vertex.ref, oldVersionVertex);
				} else {
					modifiedGraph.addVertex(vertex);
					refToNode.put((MemberReference) vertex.ref, vertex);
				}
			}
			
			Collection<ReferenceEdge> edges = graph.getEdges();
			for (ReferenceEdge edge: edges) {
				ReferenceNode src = edge.from;
				ReferenceNode dst = edge.to;
				ReferenceNode newSrc = refToNode.get(src.ref);
				ReferenceNode newDst = refToNode.get(dst.ref);
				
				ReferenceEdge modifiedEdge = new ReferenceEdge(newSrc, newDst, edge.type);
				modifiedEdge.dep = edge.dep;
//				System.out.println("src: " + src);
//				System.out.println("dst: " + dst);
//				System.out.println("newSrc: " + newSrc);
//				System.out.println("newDst: " + newDst);
				modifiedGraph.addEdge(modifiedEdge, newSrc, newDst);
			}
			
			result.add(modifiedGraph);
		}
		
		return result;
	}
	
	private List<DirectedSparseGraph<ReferenceNode, ReferenceEdge>> mergeChanges(List<DirectedSparseGraph<ReferenceNode, ReferenceEdge>> graphs) {
		List<DirectedSparseGraph<ReferenceNode, ReferenceEdge>> result = new ArrayList<DirectedSparseGraph<ReferenceNode, ReferenceEdge>>();
	
		DirectedSparseGraph<ReferenceNode, ReferenceEdge> g1 = null, g2 = null;
		boolean isChanged = true;
		Set<ReferenceNode> nSet1 = null, nSet2 = null;
		while(isChanged) {
			isChanged = false;
			for (int i = 0; i < graphs.size() - 1; i++) {
				g1 = graphs.get(i);
				if (g1.getVertexCount() == 0)
					continue;
				nSet1 = new HashSet<ReferenceNode>(g1.getVertices());
				for (int j = i + 1; j < graphs.size(); j++) {
					// added by Ye Wang, to fix bug
					boolean isChangedThisTime = false;
					
					g2 = graphs.get(j);
					if (g2.getVertexCount() == 0)
						continue;
					for (ReferenceNode n : nSet1) {
						if (g2.containsVertex(n)) {
							// added by Ye Wang, to fix bug
							isChangedThisTime = true;
							
							isChanged = true;
							break;
						}
					}
					// if (isChanged) {
					// changed by Ye Wang, to fix bug
					if (isChangedThisTime) {
						for (ReferenceNode n : g2.getVertices()) {
							if (!g1.containsVertex(n)) {								
								g1.addVertex(n);
							}
						}
						for (ReferenceEdge e : g2.getEdges()) {
							if (!g1.containsEdge(e)) {
								g1.addEdge(e, e.from, e.to);
							}
						}
						nSet2 = new HashSet<ReferenceNode>(g2.getVertices());
						for (ReferenceNode n : nSet2) {
							g2.removeVertex(n);
						}
						break;
					}
				}
			}
		}
		for (int i = 0; i < graphs.size(); i++) {
			g1 = graphs.get(i);
			if (g1.getVertexCount() != 0) {
				result.add(g1);
//				for (ReferenceEdge e : g1.getEdges()) {
//					System.out.println(e);
//				}
			}
		}
		return result;
	}
	
	private void relateChangesBasedOnIR(List<DirectedSparseGraph<ReferenceNode, ReferenceEdge>> graphs,  
			DataFlowAnalysisEngine engine, Set<ClientMethod> methods, 
			Set<MethodReference> mRefs, Set<FieldReference> fRefs, 
			Set<TypeReference> cRefs) {
		for (ClientMethod m : methods) {
			DirectedSparseGraph<ReferenceNode, ReferenceEdge> graph = new DirectedSparseGraph<ReferenceNode, ReferenceEdge>();
			graphs.add(graph);
			ReferenceNode root = new ReferenceNode(m.mRef);
			engine.getCFGBuilder(m);
			IR ir = engine.getCurrentIR();
			if (ir == null)
				continue;
			for (SSAInstruction instr : ir.getInstructions()) {
				if (instr == null)
			        continue;
				if (!fRefs.isEmpty() && instr instanceof SSAFieldAccessInstruction) {
					SSAFieldAccessInstruction sInstr = (SSAFieldAccessInstruction)instr;
					FieldReference fRef = sInstr.getDeclaredField();
					if (fRefs.contains(fRef)) {
						ReferenceNode n = new ReferenceNode(fRef);
						ReferenceEdge edge = graph.findEdge(root, n);
						if (edge == null) {
							edge = new ReferenceEdge(root, n, ReferenceEdge.FIELD_ACCESS);
							graph.addEdge(edge, root, n);
						}								
						edge.increaseCount();						
					}
				} 
				if (!mRefs.isEmpty() && (instr instanceof SSAAbstractInvokeInstruction)) {
					MethodReference mRef = ((SSAAbstractInvokeInstruction)instr).getDeclaredTarget();
					if (mRefs.contains(mRef)) {
						ReferenceNode n = new ReferenceNode(mRef);						
						ReferenceEdge edge = graph.findEdge(root, n);
						if (edge == null) {
							edge = new ReferenceEdge(root, n, ReferenceEdge.METHOD_INVOKE);
							graph.addEdge(edge, root, n);
						}								
						edge.increaseCount();
					}
				}
			}
		}
	}
	
	// Added by Ye Wang, since 10/02/2016
	private void relateAllChangesBasedOnIR(List<DirectedSparseGraph<ReferenceNode, ReferenceEdge>> graphs,  
			DataFlowAnalysisEngine leftEngine, DataFlowAnalysisEngine rightEngine, Set<ClientMethod> oldMethods,
			Set<ClientMethod> newMethods, Set<MethodReference> oMRefs, Set<MethodReference> nMRefs,
			Set<FieldReference> oFRefs, Set<FieldReference> nFRefs, 
			Set<TypeReference> oCRefs, Set<TypeReference> nCRefs) {
		relatePartialChanges(graphs, leftEngine, oldMethods, oMRefs, nMRefs, oFRefs, nFRefs, oCRefs, nCRefs);
		relatePartialChanges(graphs, rightEngine, newMethods, oMRefs, nMRefs, oFRefs, nFRefs, oCRefs, nCRefs);
	}
	
	// added by Ye Wang, since 10/18/2016
	// avoid copy-paste in relateAllChangesBasedOnIR()
	private void relatePartialChanges(List<DirectedSparseGraph<ReferenceNode, ReferenceEdge>> graphs,  
			DataFlowAnalysisEngine engine, Set<ClientMethod> methods,
			Set<MethodReference> oMRefs, Set<MethodReference> nMRefs,
			Set<FieldReference> oFRefs, Set<FieldReference> nFRefs, 
			Set<TypeReference> oCRefs, Set<TypeReference> nCRefs) {
		for (ClientMethod m : methods) {
			DirectedSparseGraph<ReferenceNode, ReferenceEdge> graph = new DirectedSparseGraph<ReferenceNode, ReferenceEdge>();
			graphs.add(graph);
			ReferenceNode root = new ReferenceNode(m.mRef);
			engine.getCFGBuilder(m);
			IR ir = engine.getCurrentIR();
			if (ir == null)
				continue;
			for (SSAInstruction instr : ir.getInstructions()) {
				if (instr == null)
					continue;
				if ((!oFRefs.isEmpty() || !nFRefs.isEmpty()) && instr instanceof SSAFieldAccessInstruction) {
					SSAFieldAccessInstruction sInstr = (SSAFieldAccessInstruction)instr;
					FieldReference fRef = sInstr.getDeclaredField();
					if (oFRefs.contains(fRef) || nFRefs.contains(fRef)) {
						ReferenceNode n = new ReferenceNode(fRef);
						ReferenceEdge edge = graph.findEdge(root, n);
						if (edge == null) {
							edge = new ReferenceEdge(root, n, ReferenceEdge.FIELD_ACCESS);
							graph.addEdge(edge, root, n);
						}								
						edge.increaseCount();						
					}
				} 
				if ((!oMRefs.isEmpty() || !nMRefs.isEmpty()) && (instr instanceof SSAAbstractInvokeInstruction)) {
					MethodReference mRef = ((SSAAbstractInvokeInstruction)instr).getDeclaredTarget();
					if (oMRefs.contains(mRef) || nMRefs.contains(mRef)) {
						ReferenceNode n = new ReferenceNode(mRef);						
						ReferenceEdge edge = graph.findEdge(root, n);
						if (edge == null) {
							edge = new ReferenceEdge(root, n, ReferenceEdge.METHOD_INVOKE);
							graph.addEdge(edge, root, n);
						}								
						edge.increaseCount();
					}
				}
			}

			MethodReference mRef = m.mRef;
			TypeReference typeRef = mRef.getDeclaringClass();
			IClassHierarchy cha = engine.getClassHierarchy();
			IMethod method = cha.resolveMethod(mRef);
			Selector selector = method.getSelector();
			IClass klass = cha.lookupClass(typeRef);
			Collection<? extends IClass> directInterfaces = klass.getDirectInterfaces();
			IClass superclass = klass.getSuperclass();
			Set<IClass> supertypes = new HashSet<IClass>(directInterfaces);
			if (superclass != null) 
				supertypes.add(superclass);
			for (IClass supertype: supertypes) {
//				System.out.println(supertype);
				Collection<IMethod> supertypeMethods = supertype.getDeclaredMethods();
				for (IMethod supertypeMethod: supertypeMethods) {
					Selector supertypeMethodSelector = supertypeMethod.getSelector();
					if (selector.equals(supertypeMethodSelector)) {
						MethodReference suptertypeMRef = supertypeMethod.getReference();
						if (oMRefs.contains(suptertypeMRef) || nMRefs.contains(suptertypeMRef)) {
							ReferenceNode n = new ReferenceNode(suptertypeMRef);
							ReferenceEdge edge = graph.findEdge(root, n);
							if (edge == null) {
								edge = new ReferenceEdge(root, n, ReferenceEdge.METHOD_OVERRIDE);
								graph.addEdge(edge, root, n);
							}
							edge.increaseCount();
						}
					}
				}
			}
			
			
		}
	}
	
	/**
	 * Convert JUNG to JGraphT
	 * @param g JUNG graph
	 * @return JGraphT graph
	 */
	public static Graph<ReferenceNode, ReferenceEdge>
			convertJungToJGraphT(DirectedSparseGraph<ReferenceNode, ReferenceEdge> graph) {
		Graph<ReferenceNode, ReferenceEdge> g =
				new DefaultDirectedGraph<ReferenceNode, ReferenceEdge>(ReferenceEdge.class);
		
		Collection<ReferenceNode> vertices = graph.getVertices();
		for (ReferenceNode vertex: vertices) {
			g.addVertex(vertex);
		}
		
		Collection<ReferenceEdge> edges = graph.getEdges();
		for (ReferenceEdge edge: edges) {
			ReferenceNode sourceVertex = edge.from;
			ReferenceNode targetVertex = edge.to;
			try {
				g.addEdge(sourceVertex, targetVertex, edge);
			} catch (Exception e) {
				e.printStackTrace();
				consolegsydit.ExceptionHandler.process(e);
			}
		}
		
		return g;
	}
	
	public static void writeRelationGraph(DirectedSparseGraph<ReferenceNode, ReferenceEdge> g, String filename) {
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
			 consolegsydit.ExceptionHandler.process(e);
		}
	}

	
	
	private List<Set<ClientMethod>> groupMethods(List<ClientMethod> ms, List<CallGraph> cgs) {
//		System.out.print("");
		List<Set<ClientMethod>> g = new ArrayList<Set<ClientMethod>>();
		for (int i = 0; i < ms.size(); i++) {
			CallGraph cg = cgs.get(i);
			ClientMethod m = ms.get(i);
			Set<CGNode> cgnodes = cg.getNodes(m.mRef);
			Set<ClientMethod> groupedMethods = new HashSet<ClientMethod>();
			for (int j = i + 1; j < ms.size(); j++) {
				ClientMethod m2 = ms.get(j);
				Set<CGNode> cgnodes2 = cg.getNodes(m2.mRef);
				for (CGNode n1 : cgnodes) {
					for (CGNode n2 : cgnodes2) {
						if (cg.hasEdge(n1, n2) || cg.hasEdge(n2, n1)) {
							groupedMethods.add(ms.get(i));
							groupedMethods.add(ms.get(j));
							break;
						}
					}
				}
			}
			g.add(groupedMethods);
		}
		boolean isChanged = true;
		while (isChanged) { // merge groups as much as we can 
			isChanged = false;
			for (int i = 0; i < g.size(); i++) {
				Set<ClientMethod> mSet1 = g.get(i);
				for (int j = i + 1; j < g.size(); j++) {
					Set<ClientMethod> mSet2 = g.get(j);
					Set<ClientMethod> copy = new HashSet<ClientMethod>(mSet2);
					copy.retainAll(mSet2);
					if (!copy.isEmpty()) {
						mSet1.addAll(mSet2);
						mSet2.clear();
						isChanged = true;
						break;
					}
				}
			}
		}				
		return g;
	}
	
//	added by zijianjiang
	private void predictCmforzijian(ReferenceNode amNode, Set<String> cmSigSet,
			Graph<ReferenceNode, ReferenceEdge> jgrapht,
			Map<MethodReference, MethodReference> newToOldMethodRefMap,
			Map<MethodReference, MethodReference> oldToNewMethodRefMap,
			DataFlowAnalysisEngine leftEngine, DataFlowAnalysisEngine rightEngine,
			Set<IClass> allFoundClasses, Map<MethodReference, ClientMethod> oldMRefToClient,
			Map<MethodReference, ClientMethod> newMRefToClient,
			Map<MethodReference, HashSet<NodePair>> oldMethodRefToMatch,
			Map<MethodReference, HashSet<NodePair>> newMethodRefToMatch,
			Map<MethodReference, ASTNode> oMRefToAST,
			Map<MethodReference, ASTNode> nMRefToAST,
			Map<MethodReference, String> oldMethodRefToRose) {
		MethodReference amRef = (MethodReference) amNode.ref;
		String amSig = amRef.getSignature();
		TypeReference amClass = amRef.getDeclaringClass();
		String amClassName = amClass.getName().getClassName().toString();
		String amName = amRef.getName().toString();
		String amClassSig = amClass.getName().toString().substring(1).replace('/', '.');
		
		//get all the peerfileds in the AM
//		Set<String> peerAmFieldSet = null;
//		ClientMethod newAmClient = newMRefToClient.get(amRef);
//		ASTNode newAmAstNode = newAmClient.methodbody;
//		FieldNameVisitor fAmVisitor = new FieldNameVisitor(newAmAstNode, amClassSig);
//		fAmVisitor.execute();
//		peerAmFieldSet = fAmVisitor.getFields();
		
		// get CM set, old version
		Set<MethodReference> cmSet = new HashSet<>();
//		Map<MethodReference, String> refToRealAccessMode = new HashMap<>();  // old reference to AF access mode
		for (ReferenceEdge edge: jgrapht.edgesOf(amNode)) {
			if (edge.type != ReferenceEdge.METHOD_INVOKE)
				continue;
			ReferenceNode srcNode = edge.from;
			if (srcNode.type != ReferenceNode.CM)
				continue;
			MethodReference oldCmRef = (MethodReference) srcNode.ref;
			String cmSig = oldCmRef.getSignature();
			if (!cmSigSet.contains(cmSig))
				continue;
//			MethodReference newCmRef = oldToNewMethodRefMap.get(oldCmRef);
			ClientMethod oldClient = oldMRefToClient.get(oldCmRef);
			ASTNode oldAstNode = oldClient.methodbody;
			Set<String> targetPeerFieldSet = null;
			FieldNameVisitor fieldNameVisitor = new FieldNameVisitor(oldAstNode, amClassSig);
			fieldNameVisitor.execute();
			targetPeerFieldSet = fieldNameVisitor.getFields();
//			if(targetPeerFieldSet.size() == 0) continue;
//			targetPeerFieldSet.addAll(peerAmFieldSet);
			
			if(targetPeerFieldSet.size() >= 2)
				cmSet.add(oldCmRef);
			
			// check AF access mode
//			ClientMethod newClient = newMRefToClient.get(newCmRef);
//			ASTNode newAstNode = newClient.methodbody;
//			FieldNameVisitor fieldNameVisitor = new FieldNameVisitor(newAstNode, afClassSig);
//			fieldNameVisitor.execute();
//			Set<String> readFields = fieldNameVisitor.getReadFields();
//			Set<String> writtenFields = fieldNameVisitor.getWrittenFields();
//			if (readFields.contains(afName) && writtenFields.contains(afName))
//				refToRealAccessMode.put(oldCmRef, "rw");
//			else if (readFields.contains(afName))
//				refToRealAccessMode.put(oldCmRef, "r");
//			else
//				refToRealAccessMode.put(oldCmRef, "w");
			
		}
		if (cmSet.size() < 2)
			return;
		
		// Check accessibility of AF
		IClassHierarchy leftHierarchy = leftEngine.getClassHierarchy();
		IClassHierarchy rightHierarchy = rightEngine.getClassHierarchy();
		IMethod iMethod = rightHierarchy.resolveMethod(amRef);
		IClass amIClass = leftHierarchy.lookupClass(amClass);
		if (amIClass == null)
			amIClass = rightHierarchy.lookupClass(amClass);
		String methodAccess = null;
		if (iMethod.isPrivate())
			methodAccess = "private";
		else if (iMethod.isProtected())
			methodAccess = "protected";
		else if (iMethod.isPublic() || amIClass.isInterface())
			methodAccess = "public";
		else
			methodAccess = "package";
		
		
		// Build method to class map
		Map<MethodReference, IClass> mRefToIClassMap = new HashMap<>();
		for (IClass iClass: allFoundClasses) {
			Collection<IMethod> declaredMethods = iClass.getDeclaredMethods();
			for (IMethod iOldMethod: declaredMethods) {
				MethodReference ref = iOldMethod.getReference();
				mRefToIClassMap.put(ref, iClass);
			}
		}
		
		// Find classes of methods candidates
		Set<IClass> classesToProcess = new HashSet<>();
		if (methodAccess.equals("private")) {
			classesToProcess.add(amIClass);
		} else if (methodAccess.equals("protected") || methodAccess.equals("package")) {
			// classes in the same package
			String methodPackage = this.getPackageOfClass(amIClass);
			for (IClass klass: allFoundClasses) {
				String packageName = this.getPackageOfClass(klass);
				if (methodPackage.equals(packageName))
					classesToProcess.add(klass);
			}
			if (methodAccess.equals("protected")) {
				// subclasses
				for (IClass klass: allFoundClasses) {
					IClass superClass = klass;
					do {
						superClass = superClass.getSuperclass();
						if (amIClass.equals(superClass)) {
							classesToProcess.add(klass);
							break;
						}
					} while (superClass != null);
				}
			}
		} else if (methodAccess.equals("public")) {
			classesToProcess.addAll(allFoundClasses);
		}
		
		// Find method candidates
		Set<MethodReference> methodCandidateSet = new HashSet<>();
		for (IClass klass: classesToProcess) {
			for (IMethod iOldMethod: klass.getDeclaredMethods()) {
				if (iOldMethod.isClinit())
					continue;
				MethodReference mRef = iOldMethod.getReference();
				methodCandidateSet.add(mRef);
			}
		}		
		
		
		// iterate over every CM
		for (MethodReference usedCmRef: cmSet) {
			MethodReference usedCmRefNew = oldToNewMethodRefMap.get(usedCmRef);
			ClientMethod oldClient = oldMRefToClient.get(usedCmRef);
			ClientMethod newClient = newMRefToClient.get(usedCmRefNew);
			ASTNode oldAstNode = oldClient.methodbody;
			ASTNode newAstNode = newClient.methodbody;
			
			// ----- important options-----
//			boolean shouldCheckAccessMode = true; // care read and write access
//			boolean shouldCheckNamingPattern = true;
			
			// Inside the CM, get the fields whose class is the same as AM
//			boolean afIsConstantNamingPattern = isConstantNamingPattern(afName); 
			Set<String> targetPeerFieldSet = null;
			FieldNameVisitor fieldNameVisitor = new FieldNameVisitor(oldAstNode, amClassSig);
			fieldNameVisitor.execute();
			targetPeerFieldSet = fieldNameVisitor.getFields();
//			targetPeerFieldSet.addAll(peerAmFieldSet);
			
//			get the targetPeerMethodSet
//			Set<String> targetPeerMethodSet = null;
//			MethodNameVisitor methodNameVisitor = new MethodNameVisitor(oldAstNode, amClassSig);
//			methodNameVisitor.execute();
//			targetPeerMethodSet = methodNameVisitor.getMethods();
//			if(targetPeerMethodSet != null && targetPeerMethodSet.size() > 0) 
//				System.out.println("Not empty, Goodddddddddd");
//			else System.out.println("It's totally empty, you did something wrong");
			
			
//			Set<String> readFieldsInUsedCm = fieldNameVisitor.getReadFields();
//			Set<String> writtenFieldsInUsedCm = fieldNameVisitor.getWrittenFields();
//			Set<String> toBeDeletedReadFieldsInUsedCm = new HashSet<>();
//			for (String n: readFieldsInUsedCm) {
//				if (isConstantNamingPattern(n) != afIsConstantNamingPattern)
//					toBeDeletedReadFieldsInUsedCm.add(n);
//			}
//			if (shouldCheckNamingPattern)
//				readFieldsInUsedCm.removeAll(toBeDeletedReadFieldsInUsedCm);
//			Set<String> toBeDeletedWrittenFieldsInUsedCm = new HashSet<>();
//			for (String n: writtenFieldsInUsedCm) {
//				if (isConstantNamingPattern(n) != afIsConstantNamingPattern)
//					toBeDeletedWrittenFieldsInUsedCm.add(n);
//			}
//			if (shouldCheckNamingPattern)
//				writtenFieldsInUsedCm.removeAll(toBeDeletedWrittenFieldsInUsedCm);
//			
//			FieldNameVisitor fVisitor = new FieldNameVisitor(newAstNode, afClassSig);
//			fVisitor.execute();
//			boolean afIsRead = fVisitor.getReadFields().contains(afName);
//			boolean afIsWritten = fVisitor.getWrittenFields().contains(afName);
//			
//			Set<String> readAndWrittenTargetPeerFields = new HashSet<>();
//			Set<String> onlyReadTargetPeerFields = new HashSet<>();
//			Set<String> onlyWrittenTargetPeerFields = new HashSet<>();
//			if (afIsRead && afIsWritten) {
//				readAndWrittenTargetPeerFields.addAll(readFieldsInUsedCm);
//				readAndWrittenTargetPeerFields.retainAll(writtenFieldsInUsedCm);
//				targetPeerFieldSet = readAndWrittenTargetPeerFields;
//			} else if (afIsRead) {
//				onlyReadTargetPeerFields.addAll(readFieldsInUsedCm);
//				onlyReadTargetPeerFields.removeAll(writtenFieldsInUsedCm);
//				targetPeerFieldSet = onlyReadTargetPeerFields;
//			} else if (afIsWritten) {
//				onlyWrittenTargetPeerFields.addAll(writtenFieldsInUsedCm);
//				onlyWrittenTargetPeerFields.removeAll(readFieldsInUsedCm);
//				targetPeerFieldSet = onlyWrittenTargetPeerFields;
//			} else {
//				targetPeerFieldSet = Collections.emptySet();
//			}
//			
//			
//			
//			
//			
//			if (!shouldCheckAccessMode) { // ignore the access mode
//				if (shouldCheckNamingPattern) {
//					targetPeerFieldSet = new HashSet<>();
//					targetPeerFieldSet.addAll(readFieldsInUsedCm);
//					targetPeerFieldSet.addAll(writtenFieldsInUsedCm);
//				} else
//					targetPeerFieldSet = fieldNameVisitor.getFields();
//			}
			
			Set<MethodReference> predictedCm = new HashSet<>();
			
			// Check every method candidate
			Map<MethodReference, Set<String>> refToFieldsMap = new HashMap<>();
			Map<MethodReference, Set<String>> refToMethodsMap = new HashMap<>();
//			Map<MethodReference, String> refToPredictedAccessMode = new HashMap<>();  // 3 access modes: "r", "w", "rw"
//			Map<MethodReference, Set<String>> methodToAccessFields = new HashMap<>();
			for (MethodReference mRef: methodCandidateSet) {
				if (mRef.equals(usedCmRef))
					continue;
				Set<String> peerFieldSet = null;
//				Set<String> peerMethodSet = null;
				ASTNode ast = oMRefToAST.get(mRef);
				if (ast == null) {
					continue;
				}
//				MethodNameVisitor methodVisitor = new MethodNameVisitor(ast, amClassSig);
//				methodVisitor.execute();
//				peerMethodSet = methodVisitor.getMethods();
//				peerMethodSet.retainAll(targetPeerMethodSet);
//				refToMethodsMap.put(mRef, peerMethodSet);
				FieldNameVisitor fieldVisitor = new FieldNameVisitor(ast, amClassSig);
				fieldVisitor.execute();
//				peerFieldSet = fieldVisitor.getFields();
//				Set<String> readFields = fieldVisitor.getReadFields();
//				Set<String> writtenFields = fieldVisitor.getWrittenFields();
				
//				boolean considerAccessInPotentialCM = false;
				
				
				
//				if (shouldCheckAccessMode) {
//					
//					Set<String> onlyReadPeerSet = new HashSet<>();
//					onlyReadPeerSet.addAll(readFields);
//					onlyReadPeerSet.removeAll(writtenFields);
//					onlyReadPeerSet.retainAll(targetPeerFieldSet);
//					
//					Set<String> onlyWrittenPeerSet = new HashSet<>();
//					onlyWrittenPeerSet.addAll(writtenFields);
//					onlyWrittenPeerSet.removeAll(readFields);
//					onlyWrittenPeerSet.retainAll(targetPeerFieldSet);
//					
//					Set<String> readAndWrittenPeerSet = new HashSet<>();
//					readAndWrittenPeerSet.addAll(readFields);
//					readAndWrittenPeerSet.retainAll(writtenFields);
//					readAndWrittenPeerSet.retainAll(targetPeerFieldSet);
//					
//					if (onlyReadPeerSet.size() == 0
//							&& onlyWrittenPeerSet.size() == 0
//							&& readAndWrittenPeerSet.size() == 0) {
//						peerFieldSet = Collections.emptySet();
//					} else {
//						Comparator<Set<String>> comparator = new Comparator<Set<String>>() {
//							@Override
//							public int compare(Set<String> o1, Set<String> o2) {
//								return o2.size() - o1.size();
//							}};
//						PriorityQueue<Set<String>> queue = new PriorityQueue<>(3, comparator);
//						queue.add(onlyReadPeerSet);
//						queue.add(onlyWrittenPeerSet);
//						queue.add(readAndWrittenPeerSet);
//						peerFieldSet = queue.peek();
//						
//						methodToAccessFields.put(mRef, peerFieldSet);
//						
//						// predict the access mode of AF, which be the same as that of peers
//						if (peerFieldSet == onlyReadPeerSet)
//							refToPredictedAccessMode.put(mRef, "r");
//						else if (peerFieldSet == onlyWrittenPeerSet)
//							refToPredictedAccessMode.put(mRef, "w");
//						else
//							refToPredictedAccessMode.put(mRef, "rw");
//						
//						Set<String> largestPeerSet = queue.poll();
//						Set<String> secondLargestPeerSet = queue.poll();
//						if (largestPeerSet.size() == secondLargestPeerSet.size())
//							refToPredictedAccessMode.put(mRef, "NA");
//					}
//					
//					
//				}
				peerFieldSet = fieldVisitor.getFields();
				peerFieldSet.retainAll(targetPeerFieldSet);
				refToFieldsMap.put(mRef, peerFieldSet);
			}
			
			// Find the method candidate with most or second most peer fields
			int maxPeerFieldsNum = -1, secMax = -1, maxPeerMethodsNum = -1;
			for (Set<String> peerFieldSet: refToFieldsMap.values()) {
				if (peerFieldSet.size() > maxPeerFieldsNum){
					secMax = maxPeerFieldsNum;
					maxPeerFieldsNum = peerFieldSet.size();
				}
				else if(peerFieldSet.size() < maxPeerFieldsNum){
					secMax = Math.max(secMax, peerFieldSet.size());
				}
			}
			
//			for(Set<String> peerMethodSet : refToMethodsMap.values()){
//				if(peerMethodSet.size() > maxPeerMethodsNum) maxPeerMethodsNum = peerMethodSet.size();
//			}
			
			if (maxPeerFieldsNum >= 2) {
				for (MethodReference mRef: refToFieldsMap.keySet()) {
					Set<String> peerFieldSet = refToFieldsMap.get(mRef);
//					Set<String> peerMethodSet = refToMethodsMap.get(mRef);
//					if (peerFieldSet.size() == maxPeerFieldsNum)
//					if (peerFieldSet.size() >= 2)
//					if(peerFieldSet.size() == maxPeerFieldsNum || (secMax >= 2 && peerFieldSet.size() >= secMax) || peerMethodSet.size() > 0 && peerMethodSet.equals(
//							targetPeerMethodSet))
					if (peerFieldSet.size() == maxPeerFieldsNum)
						predictedCm.add(mRef);
				}
			}
			
			// ----- important options-----
//			boolean useRose = false;
//			if (useRose) { // use Tom Zimmerman's tool ROSE
//				predictedCm = new HashSet<>();
//				List<String> evidenceMethods = new ArrayList<>();
//				evidenceMethods.add(oldMethodRefToRose.get(usedCmRef));
//				List<String> roseResult = RosePrediction.execute(evidenceMethods, Application.roseTable, CommitComparator.bugName);
//				Map<String, MethodReference> roseToMethodRef = new HashMap<>();
//				for (MethodReference ref: oldMethodRefToRose.keySet()) {
//					String rose = oldMethodRefToRose.get(ref);
//					roseToMethodRef.put(rose, ref);
//				}
//				for (String rose: roseResult) {
//					MethodReference ref = roseToMethodRef.get(rose);
//					if (ref != null)
//						predictedCm.add(ref);
//				}
//				
//			}

			List<String> predictedCmSigs = new ArrayList<>();
			for (MethodReference m: predictedCm) {
				predictedCmSigs.add(m.getSignature());
			}
			
			Set<String> truePositives = new HashSet<>();
			Set<String> falsePositives = new HashSet<>();
			Set<String> falseNegatives = new HashSet<>();
			Map<String, Set<String>> tpVars = new HashMap<>();
			Map<String, Set<String>> fpVars = new HashMap<>();
			Map<String, Set<String>> fnVars = new HashMap<>();
			Set<String> correctAccessPrediction = new HashSet<>();
			Set<String> predictionWithAccess = new HashSet<>();
			Map<String, Map<String, String>> accessDetail = new HashMap<>();
			
			Map<String, Set<String>> accessFields = new HashMap<>();
			
			// methodToAccessFields
			
			for (MethodReference mRef: cmSet) {
				if (mRef.equals(usedCmRef))
					continue;
				if (predictedCmSigs.contains(mRef.getSignature())) {
					truePositives.add(mRef.getSignature());
					tpVars.put(mRef.getSignature(), refToFieldsMap.get(mRef));
					
					// process predict_access and access_precision
//					String realAccess = refToRealAccessMode.get(mRef);
//					String predictedAccess = refToPredictedAccessMode.get(mRef);
//					if (!predictedAccess.equals("NA")) {
//						Map<String, String> realAndPredictedAccess = new HashMap<>();
//						realAndPredictedAccess.put("real", realAccess);
//						realAndPredictedAccess.put("predicted", predictedAccess);
//						accessDetail.put(mRef.getSignature(), realAndPredictedAccess);
//						if (realAccess.equals(predictedAccess)) {
//							correctAccessPrediction.add(mRef.getSignature());
//						}
//						predictionWithAccess.add(mRef.getSignature());
//						accessFields.put(mRef.getSignature(), methodToAccessFields.get(mRef));
//					}
				
				} else {
					falseNegatives.add(mRef.getSignature());
					fnVars.put(mRef.getSignature(), refToFieldsMap.get(mRef));
				}
			}
//			for (MethodReference mRef: predictedCm) {
//				if (!cmSet.contains(mRef)) {
//					falsePositives.add(mRef.getSignature());
//					fpVars.put(mRef.getSignature(), refToFieldsMap.get(mRef));
//					
//				}
//			}
			
			int recall = 100 * truePositives.size() / (cmSet.size() - 1);
			int precision = -1;
			if (!predictedCmSigs.isEmpty())
				precision = 100 * truePositives.size() / predictedCmSigs.size();
			
			int accessPrecision = -1;
			if (!predictionWithAccess.isEmpty())
				accessPrecision = 100 * correctAccessPrediction.size() / predictionWithAccess.size();
			
			// Insert data into database
			Gson gson = new Gson();
			Connection conn = SqliteManager.getConnection();
			try {
				PreparedStatement ps = conn.prepareStatement("INSERT INTO " + Application.amPredictTable
						+ " (bug_name,am_sig,used_cm,real_other_cm,predicted_cm,precision,recall, ground_truth_size, predicted_size, true_positive_size)"
//						+ "access_precision,access_detail, access_fields)"
						+ " VALUES (?,?,?,?,?,?,?,?,?,?)");
				ps.setString(1, CommitComparator.bugName);
				ps.setString(2, amSig);
				ps.setString(3, usedCmRef.getSignature());
				Set<String> realOtherCms = new HashSet<>(cmSigSet);
				realOtherCms.remove(usedCmRef.getSignature());
				ps.setString(4, gson.toJson(realOtherCms));
				ps.setString(5, gson.toJson(predictedCmSigs));
				if (precision == -1) {
					ps.setNull(6, java.sql.Types.INTEGER);
					ps.setNull(7, java.sql.Types.INTEGER);
				}
				else {
					ps.setInt(6, precision);
					ps.setInt(7, recall);
				}
				ps.setInt(8, cmSet.size() - 1);
				ps.setInt(9, predictedCmSigs.size());
				ps.setInt(10, truePositives.size());
				
//				if (accessPrecision == -1)
//					ps.setNull(8, java.sql.Types.INTEGER);
//				else
//					ps.setInt(8, accessPrecision);
//				ps.setString(9, gson.toJson(accessDetail));
//				ps.setString(10, gson.toJson(accessFields));
					
				
				
				
				ps.executeUpdate();
				ps.close();
				conn.close();
				
			} catch (SQLException e) {
				e.printStackTrace();
			}
			
			//--------------------------------
		}
		
	}
	
	
	private void predictCMPeerMethods(ReferenceNode amNode, Set<String> cmSigSet,
			Graph<ReferenceNode, ReferenceEdge> jgrapht,
			Map<MethodReference, MethodReference> newToOldMethodRefMap,
			Map<MethodReference, MethodReference> oldToNewMethodRefMap,
			DataFlowAnalysisEngine leftEngine, DataFlowAnalysisEngine rightEngine,
			Set<IClass> allFoundClasses, Map<MethodReference, ClientMethod> oldMRefToClient,
			Map<MethodReference, ClientMethod> newMRefToClient,
			Map<MethodReference, HashSet<NodePair>> oldMethodRefToMatch,
			Map<MethodReference, HashSet<NodePair>> newMethodRefToMatch,
			Map<MethodReference, ASTNode> oMRefToAST,
			Map<MethodReference, ASTNode> nMRefToAST,
			Map<MethodReference, String> oldMethodRefToRose) {
		MethodReference amRef = (MethodReference) amNode.ref;
//		String amType = returnTypeOfAm(amRef);
/*
 * Add on Mar. 5 for get a whole name of the return type of the AM, by using ReturnANdParameterVisitor() method.
 */
		ClientMethod amClient = newMRefToClient.get(amRef);
		ASTNode amASTNode = amClient.methodbody;
		ReturnAndParameterVisitor amVisitor = new ReturnAndParameterVisitor(amASTNode);
		amVisitor.execute();
		String amType = amVisitor.getReturnType();
//		These 4 lines may not be right, just try it now.
		
		System.out.println(amType + "123456789123456789");
//		this amArg doesn't have list<type>
//		Set<String> amArg = argumentsTypeOfAm(amRef);
		Set<String> amArg = amVisitor.getParameters();
		System.out.println("what is the size of amArg here? " + amArg.size());
		
		String amSig = amRef.getSignature();
		TypeReference amClass = amRef.getDeclaringClass();
		String amClassName = amClass.getName().getClassName().toString();
		String amName = amRef.getName().toString();
		String amClassSig = amClass.getName().toString().substring(1).replace('/', '.');
		
		// get CM set, old version
		Set<MethodReference> cmSet = new HashSet<>();
		

		for (ReferenceEdge edge: jgrapht.edgesOf(amNode)) {
			if (edge.type != ReferenceEdge.METHOD_INVOKE)
				continue;
			ReferenceNode srcNode = edge.from;
			if (srcNode.type != ReferenceNode.CM)
				continue;
			MethodReference oldCmRef = (MethodReference) srcNode.ref;
			String cmSig = oldCmRef.getSignature();
			if (!cmSigSet.contains(cmSig))
				continue;
			ClientMethod oldClient = oldMRefToClient.get(oldCmRef);
			ASTNode oldAstNode = oldClient.methodbody;
			Set<String> pMSet = null;

			MethodNameVisitor methodNameVisitor = new MethodNameVisitor(oldAstNode, amClassSig);

			methodNameVisitor.execute();
			pMSet = methodNameVisitor.getMethods();

			if(pMSet.size() >= 1) cmSet.add(oldCmRef);

		}
		if(cmSet.size() < 2) 
			return;

		IClassHierarchy leftHierarchy = leftEngine.getClassHierarchy();
		IClassHierarchy rightHierarchy = rightEngine.getClassHierarchy();
		IMethod iMethod = rightHierarchy.resolveMethod(amRef);
		IClass amIClass = leftHierarchy.lookupClass(amClass);
		if (amIClass == null)
			amIClass = rightHierarchy.lookupClass(amClass);
		String methodAccess = null;
		if (iMethod.isPrivate())
			methodAccess = "private";
		else if (iMethod.isProtected())
			methodAccess = "protected";
		else if (iMethod.isPublic() || amIClass.isInterface())
			methodAccess = "public";
		else
			methodAccess = "package";
		
		
		// Build method to class map
		Map<MethodReference, IClass> mRefToIClassMap = new HashMap<>();
		for (IClass iClass: allFoundClasses) {
			Collection<IMethod> declaredMethods = iClass.getDeclaredMethods();
			for (IMethod iOldMethod: declaredMethods) {
				MethodReference ref = iOldMethod.getReference();
				mRefToIClassMap.put(ref, iClass);
			}
		}
		
		// Find classes of methods candidates
		Set<IClass> classesToProcess = new HashSet<>();
		if (methodAccess.equals("private")) {
			classesToProcess.add(amIClass);
		} else if (methodAccess.equals("protected") || methodAccess.equals("package")) {
			// classes in the same package
			String methodPackage = this.getPackageOfClass(amIClass);
			for (IClass klass: allFoundClasses) {
				String packageName = this.getPackageOfClass(klass);
				if (methodPackage.equals(packageName))
					classesToProcess.add(klass);
			}
			if (methodAccess.equals("protected")) {
				// subclasses
				for (IClass klass: allFoundClasses) {
					IClass superClass = klass;
					do {
						superClass = superClass.getSuperclass();
						if (amIClass.equals(superClass)) {
							classesToProcess.add(klass);
							break;
						}
					} while (superClass != null);
				}
			}
		} else if (methodAccess.equals("public")) {
			classesToProcess.addAll(allFoundClasses);
		}
		
		// Find method candidates
		Set<MethodReference> methodCandidateSet = new HashSet<>();
		for (IClass klass: classesToProcess) {
			for (IMethod iOldMethod: klass.getDeclaredMethods()) {
				if (iOldMethod.isClinit())
					continue;
				MethodReference mRef = iOldMethod.getReference();
				methodCandidateSet.add(mRef);
			}
		}		
		boolean useRose = true;
		boolean useTARMAQ = false;
		boolean useTransAR = false;
		
		// iterate over every CM
		if(cmSet.size() >= 2){
			for (MethodReference usedCmRef: cmSet) {
				Set<MethodReference> predictedCm = new HashSet<>();
				if (!useRose){
					MethodReference usedCmRefNew = oldToNewMethodRefMap.get(usedCmRef);
					ClientMethod oldClient = oldMRefToClient.get(usedCmRef);
					ClientMethod newClient = newMRefToClient.get(usedCmRefNew);
					ASTNode oldAstNode = oldClient.methodbody;
					ASTNode newAstNode = newClient.methodbody;
					
		
		
					Set<String> targetPeerMethodSet = null;		
					MethodNameVisitor visitor = new MethodNameVisitor(oldAstNode, amClassSig);
					visitor.execute();
					targetPeerMethodSet = visitor.getMethods();
					
					TypeInTheCm typeInUsedCm = new TypeInTheCm(oldAstNode);
					typeInUsedCm.execute();
					Set<String> typesInUsed = typeInUsedCm.getTypesAll();
	
	//				Set<MethodReference> predictedCm = new HashSet<>();
					
					// Check every method candidate
	
					Map<MethodReference, Set<String>> refToMethodsMap = new HashMap<>();
					for (MethodReference mRef: methodCandidateSet) {
						if (mRef.equals(usedCmRef))
							continue;
	
						Set<String> peerMethodSet = null;
						ASTNode ast = oMRefToAST.get(mRef);
						if (ast == null) {
							continue;
						}
						MethodNameVisitor methodVisitor = new MethodNameVisitor(ast, amClassSig);
	
						methodVisitor.execute();
						peerMethodSet = methodVisitor.getMethods();
						peerMethodSet.retainAll(targetPeerMethodSet);
						refToMethodsMap.put(mRef, peerMethodSet);
					}
					
					// Find the method candidate with most or second most peer methods
					int maxPeerFieldsNum = -1, secMax = -1, maxPeerMethodsNum = -1;
					for (Set<String> peerMethodSet: refToMethodsMap.values()) {
						if (peerMethodSet.size() > maxPeerMethodsNum){
							maxPeerMethodsNum = peerMethodSet.size();
						}
					}
					
					if (maxPeerMethodsNum >= 1){
						for (MethodReference mRef: refToMethodsMap.keySet()) {
							Set<String> peerMethodSet = refToMethodsMap.get(mRef);
							ASTNode mRefAst = oMRefToAST.get(mRef);
							TypeInTheCm typeInmRef = new TypeInTheCm(mRefAst);
							
							typeInmRef.execute();
							Set<String> typesAllHere = typeInmRef.getTypesAll();
							Set<String> parAllHere = typeInmRef.getTypesPar();
							if(typesAllHere.size() > 0) {
								for(String types : typesAllHere)
									System.out.println(types + " 123456");
							}
							Set<String> amArguments = new HashSet<>();
							for(String arg : amArg){
								amArguments.add(arg);
							}
							System.out.println("what the fuck is the size of amArguments? " + amArguments.size());
							int sizeOfAmArg = amArguments.size();
							amArguments.retainAll(parAllHere);
							
//							if (peerMethodSet.size() == maxPeerMethodsNum)
//								predictedCm.add(mRef);
	//						if (peerMethodSet.size() == maxPeerMethodsNum && amArguments.size() >= sizeOfAmArg - 1)
	//						if (peerMethodSet.size() == maxPeerMethodsNum && (amType == null || amType.equals("void") || typesAllHere.contains(amType)))
							/*
							 * real one below
							 */
							if (peerMethodSet.size() == maxPeerMethodsNum && /*amArguments.size() >= sizeOfAmArg - 1*/ amArguments.size() >= sizeOfAmArg - 1 && (amType == null || amType.equals("void") || typesAllHere.contains(amType)))
								predictedCm.add(mRef);
						}
					}
				}

				else{
				 
//				Set<MethodReference> predictedCm = new HashSet<>();
					List<String> evidenceMethods = new ArrayList<>();
					evidenceMethods.add(oldMethodRefToRose.get(usedCmRef));
					List<String> roseResult = TransARPrediction.execute(evidenceMethods, Application.roseTable, CommitComparator.bugName);
					Map<String, MethodReference> roseToMethodRef = new HashMap<>();
					for (MethodReference ref: oldMethodRefToRose.keySet()) {
						String rose = oldMethodRefToRose.get(ref);
						roseToMethodRef.put(rose, ref);
					}
					for (String rose: roseResult) {
						MethodReference ref = roseToMethodRef.get(rose);
						if (ref != null)
							predictedCm.add(ref);
					}
				}
					
				
	
				List<String> predictedCmSigs = new ArrayList<>();
				for (MethodReference m: predictedCm) {
					predictedCmSigs.add(m.getSignature());
				}
				
//				ASTNode usedmRefAst = oMRefToAST.get(mRef);
//				TypeInTheCm typeInmRef = new TypeInTheCm(mRefAst);
//				typeInmRef.execute();
////				Set<String> typesLeftHere = typeInmRef.getTypes();
//				Set<String> typesAllHere = typeInmRef.getTypesAll();
//				if(typesAllHere.size() > 0) {
//					for(String types : typesAllHere)
//						System.out.println(types + " 123456");
//				}
				
				Set<String> truePositives = new HashSet<>();
				Set<String> falsePositives = new HashSet<>();
				Set<String> falseNegatives = new HashSet<>();
				Map<String, Set<String>> tpVars = new HashMap<>();
				Map<String, Set<String>> fpVars = new HashMap<>();
				Map<String, Set<String>> fnVars = new HashMap<>();
				Set<String> correctAccessPrediction = new HashSet<>();
				Set<String> predictionWithAccess = new HashSet<>();
				Map<String, Map<String, String>> accessDetail = new HashMap<>();
				
				Map<String, Set<String>> accessFields = new HashMap<>();
				
				// methodToAccessFields
				Set<String> realOtherCms = new HashSet<>();
//				realOtherCms.remove(usedCmRef.getSignature());
				Set<String> cmSigSet2 = new HashSet<>();
				for (MethodReference mRef: cmSet) {
					cmSigSet2.add(mRef.getSignature());
				}
				
				for (String predicted : predictedCmSigs) {
					if (!cmSigSet2.contains(predicted)) {
						realOtherCms.add(predicted);
					}
				}
				
				for (MethodReference mRef: cmSet) {
					if (mRef.equals(usedCmRef))
						continue;
					if (predictedCmSigs.contains(mRef.getSignature())) {
						truePositives.add(mRef.getSignature());
	//					tpVars.put(mRef.getSignature(), refToFieldsMap.get(mRef));
						
						// process predict_access and access_precision
	//					String realAccess = refToRealAccessMode.get(mRef);
	//					String predictedAccess = refToPredictedAccessMode.get(mRef);
	//					if (!predictedAccess.equals("NA")) {
	//						Map<String, String> realAndPredictedAccess = new HashMap<>();
	//						realAndPredictedAccess.put("real", realAccess);
	//						realAndPredictedAccess.put("predicted", predictedAccess);
	//						accessDetail.put(mRef.getSignature(), realAndPredictedAccess);
	//						if (realAccess.equals(predictedAccess)) {
	//							correctAccessPrediction.add(mRef.getSignature());
	//						}
	//						predictionWithAccess.add(mRef.getSignature());
	//						accessFields.put(mRef.getSignature(), methodToAccessFields.get(mRef));
	//					}
					
					} else {
						falseNegatives.add(mRef.getSignature());
	//					fnVars.put(mRef.getSignature(), refToFieldsMap.get(mRef));
					}
				}
	//			for (MethodReference mRef: predictedCm) {
	//				if (!cmSet.contains(mRef)) {
	//					falsePositives.add(mRef.getSignature());
	//					fpVars.put(mRef.getSignature(), refToFieldsMap.get(mRef));
	//					
	//				}
	//			}
				
				int recall = 100 * truePositives.size() / (cmSet.size() - 1);
				int precision = -1;
				if (!predictedCmSigs.isEmpty())
					precision = 100 * truePositives.size() / predictedCmSigs.size();
				
				int accessPrecision = -1;
				if (!predictionWithAccess.isEmpty())
					accessPrecision = 100 * correctAccessPrediction.size() / predictionWithAccess.size();
				
				// Insert data into database
				Gson gson = new Gson();
				Connection conn = SqliteManager.getConnection();
				try {
					PreparedStatement ps = conn.prepareStatement("INSERT INTO " + Application.amPredictTable
							+ " (bug_name,am_sig,used_cm,real_other_cm,am_par,am_ret,cm_types,predicted_cm,precision,recall, ground_truth_size, predicted_size, true_positive_size)"
	//						+ "access_precision,access_detail, access_fields)"
							+ " VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?)");
					ps.setString(1, CommitComparator.bugName);
					ps.setString(2, amSig);
					ps.setString(3, usedCmRef.getSignature());
//					Set<String> realOtherCms = new HashSet<>(cmSigSet);
//					realOtherCms.remove(usedCmRef.getSignature());
					ps.setString(4, gson.toJson(realOtherCms));
					System.out.println("what is the size of amArg here? " + amArg.size());
					ps.setString(5, gson.toJson(amArg));
					ps.setString(6, amType);
					ps.setString(7, /*gson.toJson(typesInUsed)*/amType);
					ps.setString(8, gson.toJson(predictedCmSigs));
					if (precision == -1) {
						ps.setNull(9, java.sql.Types.INTEGER);
						ps.setNull(10, java.sql.Types.INTEGER);
					}
					else {
						ps.setInt(9, precision);
						ps.setInt(10, recall);
					}
					ps.setInt(11, cmSet.size() - 1);
					ps.setInt(12, predictedCmSigs.size());
					ps.setInt(13, truePositives.size());
					if(!predictedCmSigs.isEmpty()){
						if(Application.amPredictTable.equals("am_predict_aries")){
							Application.tasks[0]++;
							Application.predictTable[0] += 1.0 * truePositives.size()/predictedCmSigs.size();
							Application.recallTable[0] += 1.0 * recall / 100;
						}
						else if(Application.amPredictTable.equals("am_predict_cassandra")){
							Application.tasks[1]++;
							Application.predictTable[1] += 1.0 * truePositives.size()/predictedCmSigs.size();
							Application.recallTable[1] += 1.0 * recall / 100;
						}
						else if(Application.amPredictTable.contains("activemq")){
							Application.tasks[2]++;
							Application.predictTable[2] += 1.0 * truePositives.size()/predictedCmSigs.size();
							Application.recallTable[2] += 1.0 * recall / 100;
						}
						else{
							Application.tasks[3]++;
							Application.predictTable[3] += 1.0 * truePositives.size()/predictedCmSigs.size();
							Application.recallTable[3] += 1.0 * recall / 100;
						}
					}
	//				if (accessPrecision == -1)
	//					ps.setNull(8, java.sql.Types.INTEGER);
	//				else
	//					ps.setInt(8, accessPrecision);
	//				ps.setString(9, gson.toJson(accessDetail));
	//				ps.setString(10, gson.toJson(accessFields));
						
					
					
					
					ps.executeUpdate();
					ps.close();
					conn.close();
					
				} catch (SQLException e) {
					e.printStackTrace();
				}
				
				//--------------------------------
			}
		}
		
	}
	
	String getCmClassSig(MethodReference usedCmRef){
		String cmSig = usedCmRef.getSignature();
		TypeReference cmClass = usedCmRef.getDeclaringClass();
		String cmClassName = cmClass.getName().getClassName().toString();
		String cmName = usedCmRef.getName().toString();
		String cmClassSig = cmClass.getName().toString().substring(1).replace('/', '.');
		return cmClassSig;
	}
	
	private void predictMultiCMPeerMethods(ReferenceNode amNode, Set<String> cmSigSet,
			Graph<ReferenceNode, ReferenceEdge> jgrapht,
			Map<MethodReference, MethodReference> newToOldMethodRefMap,
			Map<MethodReference, MethodReference> oldToNewMethodRefMap,
			DataFlowAnalysisEngine leftEngine, DataFlowAnalysisEngine rightEngine,
			Set<IClass> allFoundClasses, Map<MethodReference, ClientMethod> oldMRefToClient,
			Map<MethodReference, ClientMethod> newMRefToClient,
			Map<MethodReference, HashSet<NodePair>> oldMethodRefToMatch,
			Map<MethodReference, HashSet<NodePair>> newMethodRefToMatch,
			Map<MethodReference, ASTNode> oMRefToAST,
			Map<MethodReference, ASTNode> nMRefToAST,
			Map<MethodReference, String> oldMethodRefToRose) {
		MethodReference amRef = (MethodReference) amNode.ref;
		
		ClientMethod amClient = newMRefToClient.get(amRef);
		ASTNode amASTNode = amClient.methodbody;
		ReturnAndParameterVisitor amVisitor = new ReturnAndParameterVisitor(amASTNode);
		amVisitor.execute();
		String amType = amVisitor.getReturnType();
		System.out.println(amType + "123456789123456789");
		Set<String> amArg = amVisitor.getParameters();
		System.out.println("what is the size of amArg here? " + amArg.size());
		
		
		
		String amSig = amRef.getSignature();
		TypeReference amClass = amRef.getDeclaringClass();
		String amClassName = amClass.getName().getClassName().toString();
		String amName = amRef.getName().toString();
		String amClassSig = amClass.getName().toString().substring(1).replace('/', '.');
		

		
		
		// get CM set, old version
		Set<MethodReference> cmSet = new HashSet<>();
		for (ReferenceEdge edge: jgrapht.edgesOf(amNode)) {
			if (edge.type != ReferenceEdge.METHOD_INVOKE)
				continue;
			ReferenceNode srcNode = edge.from;
			if (srcNode.type != ReferenceNode.CM)
				continue;
			MethodReference oldCmRef = (MethodReference) srcNode.ref;
			String cmSig = oldCmRef.getSignature();
			if (!cmSigSet.contains(cmSig))
				continue;
//			MethodReference newCmRef = oldToNewMethodRefMap.get(oldCmRef);
			ClientMethod oldClient = oldMRefToClient.get(oldCmRef);
			ASTNode oldAstNode = oldClient.methodbody;
			Set<String> targetPeerMethodSet = null;
			String cmClassSig = getCmClassSig(oldCmRef);
			MethodNameVisitor methodNameVisitor = new MethodNameVisitor(oldAstNode, amClassSig);
//			AmCmMethodNameVisitor methodNameVisitor = new AmCmMethodNameVisitor(oldAstNode, amClassSig, cmClassSig);
			methodNameVisitor.execute();
			targetPeerMethodSet = methodNameVisitor.getMethods();
//			if(targetPeerFieldSet.size() == 0) continue;
//			targetPeerMethodSet.addAll(peerAmMethodSet);
			
			if(targetPeerMethodSet.size() >= 1)
				cmSet.add(oldCmRef);
			
			// check AF access mode
//			ClientMethod newClient = newMRefToClient.get(newCmRef);
//			ASTNode newAstNode = newClient.methodbody;
//			FieldNameVisitor fieldNameVisitor = new FieldNameVisitor(newAstNode, afClassSig);
//			fieldNameVisitor.execute();
//			Set<String> readFields = fieldNameVisitor.getReadFields();
//			Set<String> writtenFields = fieldNameVisitor.getWrittenFields();
//			if (readFields.contains(afName) && writtenFields.contains(afName))
//				refToRealAccessMode.put(oldCmRef, "rw");
//			else if (readFields.contains(afName))
//				refToRealAccessMode.put(oldCmRef, "r");
//			else
//				refToRealAccessMode.put(oldCmRef, "w");
			
		}
		if (cmSet.size() < 2)
			return;
		
		// Check accessibility of AM
		IClassHierarchy leftHierarchy = leftEngine.getClassHierarchy();
		IClassHierarchy rightHierarchy = rightEngine.getClassHierarchy();
		IMethod iMethod = rightHierarchy.resolveMethod(amRef);
		IClass amIClass = leftHierarchy.lookupClass(amClass);
		if (amIClass == null)
			amIClass = rightHierarchy.lookupClass(amClass);
		String methodAccess = null;
		if (iMethod.isPrivate())
			methodAccess = "private";
		else if (iMethod.isProtected())
			methodAccess = "protected";
		else if (iMethod.isPublic() || amIClass.isInterface())
			methodAccess = "public";
		else
			methodAccess = "package";
		
		
		// Build method to class map
		Map<MethodReference, IClass> mRefToIClassMap = new HashMap<>();
		for (IClass iClass: allFoundClasses) {
			Collection<IMethod> declaredMethods = iClass.getDeclaredMethods();
			for (IMethod iOldMethod: declaredMethods) {
				MethodReference ref = iOldMethod.getReference();
				mRefToIClassMap.put(ref, iClass);
			}
		}
		
		// Find classes of methods candidates
		Set<IClass> classesToProcess = new HashSet<>();
		if (methodAccess.equals("private")) {
			classesToProcess.add(amIClass);
		} else if (methodAccess.equals("protected") || methodAccess.equals("package")) {
			// classes in the same package
			String methodPackage = this.getPackageOfClass(amIClass);
			for (IClass klass: allFoundClasses) {
				String packageName = this.getPackageOfClass(klass);
				if (methodPackage.equals(packageName))
					classesToProcess.add(klass);
			}
			if (methodAccess.equals("protected")) {
				// subclasses
				for (IClass klass: allFoundClasses) {
					IClass superClass = klass;
					do {
						superClass = superClass.getSuperclass();
						if (amIClass.equals(superClass)) {
							classesToProcess.add(klass);
							break;
						}
					} while (superClass != null);
				}
			}
		} else if (methodAccess.equals("public")) {
			classesToProcess.addAll(allFoundClasses);
		}
		
		// Find method candidates
		Set<MethodReference> methodCandidateSet = new HashSet<>();
		for (IClass klass: classesToProcess) {
			for (IMethod iOldMethod: klass.getDeclaredMethods()) {
				if (iOldMethod.isClinit())
					continue;
				MethodReference mRef = iOldMethod.getReference();
				methodCandidateSet.add(mRef);
			}
		}	
		
		int evidenceSize = 2;
		if(cmSet.size() <= evidenceSize) return;
		
		Map<List<MethodReference>, List<MethodReference>> evidenceToReal = DivisionUtil.divide(cmSet, evidenceSize);
		
		boolean useRose = false;
		boolean useTARMAQ = false;
		boolean useTransAR = true;
		for(List<MethodReference> evidenceCms : evidenceToReal.keySet()) {
			List<MethodReference> realOtherCmRefs = evidenceToReal.get(evidenceCms);
			Set<MethodReference> predictedCm = new HashSet<>();
			if (useRose) { // use Tom Zimmerman's tool ROSE
				List<String> evidenceMethods = new ArrayList<>();
				for (MethodReference m: evidenceCms)
					evidenceMethods.add(oldMethodRefToRose.get(m));
				List<String> roseResult = RosePrediction.execute(evidenceMethods, Application.roseTable, CommitComparator.bugName);
				Map<String, MethodReference> roseToMethodRef = new HashMap<>();
				for (MethodReference ref: oldMethodRefToRose.keySet()) {
					String rose = oldMethodRefToRose.get(ref);
					roseToMethodRef.put(rose, ref);
				}
				for (String rose: roseResult) {
					MethodReference ref = roseToMethodRef.get(rose);
					if (ref != null)
						predictedCm.add(ref);
				}
			} 
			else if (useTARMAQ) {
				List<String> evidenceMethods = new ArrayList<>();
				for (MethodReference m: evidenceCms)
					evidenceMethods.add(oldMethodRefToRose.get(m));
				List<String> TARMAQResult = TARMAQPrediction.execute(evidenceMethods, Application.roseTable, CommitComparator.bugName);
				Map<String, MethodReference> TARToMethodRef = new HashMap<>();
				for (MethodReference ref: oldMethodRefToRose.keySet()) {
					String rose = oldMethodRefToRose.get(ref);
					TARToMethodRef.put(rose, ref);
				}
				for (String TAR: TARMAQResult) {
					MethodReference ref = TARToMethodRef.get(TAR);
					if (ref != null)
						predictedCm.add(ref);
				}
			}
			else if (useTransAR) {
				List<String> evidenceMethods = new ArrayList<>();
				for (MethodReference m: evidenceCms)
					evidenceMethods.add(oldMethodRefToRose.get(m));
				List<String> roseResult = TransARPrediction.execute(evidenceMethods, Application.roseTable, CommitComparator.bugName);
				Map<String, MethodReference> roseToMethodRef = new HashMap<>();
				for (MethodReference ref: oldMethodRefToRose.keySet()) {
					String rose = oldMethodRefToRose.get(ref);
					roseToMethodRef.put(rose, ref);
				}
				for (String rose: roseResult) {
					MethodReference ref = roseToMethodRef.get(rose);
					if (ref != null)
						predictedCm.add(ref);
				}
			}
			else {
				for (MethodReference usedCmRef : evidenceCms) {
					MethodReference usedCmRefNew = oldToNewMethodRefMap.get(usedCmRef);
					ClientMethod oldClient = oldMRefToClient.get(usedCmRef);
					ClientMethod newClient = newMRefToClient.get(usedCmRefNew);
					ASTNode oldAstNode = oldClient.methodbody;
					ASTNode newAstNode = newClient.methodbody;
	//				get the target peer method set
					Set<String> targetPeerMethodSet = null;
					String cmClassSig = getCmClassSig(usedCmRef);
					MethodNameVisitor methodNameVisitor = new MethodNameVisitor(oldAstNode, amClassSig);
	//				AmCmMethodNameVisitor methodNameVisitor = new AmCmMethodNameVisitor(oldAstNode, amClassSig, cmClassSig);
	//				MethodNameVisitor methodNameVisitor = new MethodNameVisitor(oldAstNode, amClassSig);
					methodNameVisitor.execute();
					targetPeerMethodSet = methodNameVisitor.getMethods();
					
					
					Set<MethodReference> currentPredictedCm = new HashSet<>();
					
	//				check every method candidate
					Map<MethodReference, Set<String>> refToMethodsMap = new HashMap<>();
					for (MethodReference mRef: methodCandidateSet) {
						if (mRef.equals(usedCmRef))
							continue;
	//					Set<String> peerFieldSet = null;
						Set<String> peerMethodSet = null;
						ASTNode ast = oMRefToAST.get(mRef);
						if (ast == null) {
							continue;
						}
	
	//					MethodNameVisitor methodNameVisitor = new MethodNameVisitor(oldAstNode, amClassSig);
	//					AmCmMethodNameVisitor methodVisitor = new AmCmMethodNameVisitor(ast, amClassSig, cmClassSig);
						MethodNameVisitor methodVisitor = new MethodNameVisitor(ast, amClassSig);
						methodVisitor.execute();
						peerMethodSet = methodVisitor.getMethods();
						peerMethodSet.retainAll(targetPeerMethodSet);
						refToMethodsMap.put(mRef, peerMethodSet);
					}
					
	//				Find the method candidates with most peer methods
					int maxPeerMethodsNum = -1;
					for (Set<String> peerMethodSet: refToMethodsMap.values()) {
						if (peerMethodSet.size() > maxPeerMethodsNum){
							maxPeerMethodsNum = peerMethodSet.size();
						}
					}
					if (maxPeerMethodsNum >= 1) {
						for (MethodReference mRef: refToMethodsMap.keySet()) {
							Set<String> peerMethodSet = refToMethodsMap.get(mRef);
							ASTNode mRefAst = oMRefToAST.get(mRef);
							TypeInTheCm typeInmRef = new TypeInTheCm(mRefAst);
							typeInmRef.execute();
							Set<String> typesAllHere = typeInmRef.getTypesAll();
							Set<String> parAllHere = typeInmRef.getTypesPar();
							Set<String> amArguments = new HashSet<>();
							for(String arg : amArg){
								amArguments.add(arg);
							}
							int sizeOfAmArg = amArguments.size();
							amArguments.retainAll(parAllHere);
							if (peerMethodSet.size() == maxPeerMethodsNum && amArguments.size() >= sizeOfAmArg - 1 && (amType == null || amType.equals("void") || typesAllHere.contains(amType)))
								currentPredictedCm.add(mRef);
	//						if (peerMethodSet.size() == maxPeerMethodsNum)
	//							currentPredictedCm.add(mRef);
						}
					}
					
					predictedCm.addAll(currentPredictedCm);
				}
			}
			
			List<String> predictedCmSigs = new ArrayList<>();
			for (MethodReference m: predictedCm) {
				predictedCmSigs.add(m.getSignature());
			}
			Set<String> truePositives = new HashSet<>();
			Set<String> falsePositives = new HashSet<>();
			Set<String> falseNegatives = new HashSet<>();
			Map<String, Set<String>> tpVars = new HashMap<>();
			Map<String, Set<String>> fpVars = new HashMap<>();
			Map<String, Set<String>> fnVars = new HashMap<>();
			Set<String> correctAccessPrediction = new HashSet<>();
			Set<String> predictionWithAccess = new HashSet<>();
			Map<String, Map<String, String>> accessDetail = new HashMap<>();
			
			
			for (MethodReference mRef: cmSet) {
				if (evidenceCms.contains(mRef))
					continue;
				if (predictedCmSigs.contains(mRef.getSignature())) {
					truePositives.add(mRef.getSignature());
//					
				} else {
					falseNegatives.add(mRef.getSignature());
//					fnVars.put(mRef.getSignature(), refToFieldsMap.get(mRef));
				}
			}
			
			int recall = 100 * truePositives.size() / (cmSet.size() - evidenceSize);
			int precision = -1;
			if (!predictedCmSigs.isEmpty())
				precision = 100 * truePositives.size() / predictedCmSigs.size();
			
			
			Gson gson = new Gson();
			Connection conn = SqliteManager.getConnection();
			try {
				PreparedStatement ps = conn.prepareStatement("INSERT INTO " + Application.amPredictTable
						+ " (bug_name,am_sig,used_cm,real_other_cm,predicted_cm,precision,recall, ground_truth_size, predicted_size, true_positive_size)"
//						+ "access_precision,access_detail, access_fields)"
						+ " VALUES (?,?,?,?,?,?,?,?,?,?)");
				ps.setString(1, CommitComparator.bugName);
				ps.setString(2, amSig);
				List<String> evidenceCmSigs = new ArrayList<>();
				for (MethodReference m: evidenceCms)
					evidenceCmSigs.add(m.getSignature());
				ps.setString(3, gson.toJson(evidenceCmSigs));
				Set<String> realOtherCms = new HashSet<>();
				for (MethodReference m: realOtherCmRefs)
					realOtherCms.add(m.getSignature());
				ps.setString(4, gson.toJson(realOtherCms));
				ps.setString(5, gson.toJson(predictedCmSigs));
				if (precision == -1) {
					ps.setNull(6, java.sql.Types.INTEGER);
					ps.setNull(7, java.sql.Types.INTEGER);
				}
				else {
					ps.setInt(6, precision);
					ps.setInt(7, recall);
				}
				ps.setInt(8, cmSet.size() - evidenceSize);
				ps.setInt(9, predictedCmSigs.size());
				ps.setInt(10, truePositives.size());
				if(!predictedCmSigs.isEmpty()){
					if(Application.amPredictTable.equals("am_predict_aries")){
						Application.tasks[0]++;
						Application.predictTable[0] += 1.0 * truePositives.size()/predictedCmSigs.size();
						Application.recallTable[0] += 1.0 * truePositives.size()/(cmSet.size() - evidenceSize);
					}
					else if(Application.amPredictTable.equals("am_predict_cassandra")){
						Application.tasks[1]++;
						Application.predictTable[1] += 1.0 * truePositives.size()/predictedCmSigs.size();
						Application.recallTable[1] += 1.0 * truePositives.size()/(cmSet.size() - evidenceSize);
					}
					else if(Application.amPredictTable.contains("activemq")){
						Application.tasks[2]++;
						Application.predictTable[2] += 1.0 * truePositives.size()/predictedCmSigs.size();
						Application.recallTable[2] += 1.0 * truePositives.size()/(cmSet.size() - evidenceSize);
					}
					else{
						Application.tasks[3]++;
						Application.predictTable[3] += 1.0 * truePositives.size()/predictedCmSigs.size();
						Application.recallTable[3] += 1.0 * truePositives.size()/(cmSet.size() - evidenceSize);
					}
				}

				ps.executeUpdate();
				ps.close();
				conn.close();
				
			} catch (SQLException e) {
				e.printStackTrace();
			}
		}
	}
	
	private void checkAmCm(ReferenceNode amNode, Set<String> cmSigSet,
			Graph<ReferenceNode, ReferenceEdge> jgrapht,
			Map<MethodReference, MethodReference> newToOldMethodRefMap,
			Map<MethodReference, MethodReference> oldToNewMethodRefMap,
			DataFlowAnalysisEngine leftEngine, DataFlowAnalysisEngine rightEngine,
			Set<IClass> allFoundClasses, Map<MethodReference, ClientMethod> oldMRefToClient,
			Map<MethodReference, ClientMethod> newMRefToClient,
			Map<MethodReference, HashSet<NodePair>> oldMethodRefToMatch,
			Map<MethodReference, HashSet<NodePair>> newMethodRefToMatch,
			Map<MethodReference, ASTNode> oMRefToAST,
			Map<MethodReference, ASTNode> nMRefToAST,
			Map<MethodReference, String> oldMethodRefToRose) {
		MethodReference amRef = (MethodReference) amNode.ref;
		String amSig = amRef.getSignature();
		TypeReference amClass = amRef.getDeclaringClass();
		String amClassName = amClass.getName().getClassName().toString();
		String amName = amRef.getName().toString();
		String amClassSig = amClass.getName().toString().substring(1).replace('/', '.');
		
		//get all the peerfileds in the AM
//		Set<String> peerAmMethodSet = null;
//		ClientMethod newAmClient = newMRefToClient.get(amRef);
//		ASTNode newAmAstNode = newAmClient.methodbody;
//		MethodNameVisitor fAmVisitor = new MethodNameVisitor(newAmAstNode, amClassSig);
//		fAmVisitor.execute();
//		peerAmMethodSet = fAmVisitor.getMethods();
//		if(peerAmMethodSet == null || peerAmMethodSet.size() == 0) return;
		
		
		// get CM set, old version
		Set<MethodReference> cmSet = new HashSet<>();
//		Map<MethodReference, String> refToRealAccessMode = new HashMap<>();  // old reference to AF access mode
		for (ReferenceEdge edge: jgrapht.edgesOf(amNode)) {
			if (edge.type != ReferenceEdge.METHOD_INVOKE)
				continue;
			ReferenceNode srcNode = edge.from;
			if (srcNode.type != ReferenceNode.CM)
				continue;
			MethodReference oldCmRef = (MethodReference) srcNode.ref;
			String cmSig = oldCmRef.getSignature();
			if (!cmSigSet.contains(cmSig))
				continue;
//			MethodReference newCmRef = oldToNewMethodRefMap.get(oldCmRef);
			ClientMethod oldClient = oldMRefToClient.get(oldCmRef);
			ASTNode oldAstNode = oldClient.methodbody;
			Set<String> targetPeerMethodSet = null;
//			String cmClassSig = getCmClassSig(oldCmRef);
			MethodNameVisitor methodNameVisitor = new MethodNameVisitor(oldAstNode, amClassSig);
//			AmCmMethodNameVisitor methodNameVisitor = new AmCmMethodNameVisitor(oldAstNode, amClassSig, cmClassSig);
			methodNameVisitor.execute();
			targetPeerMethodSet = methodNameVisitor.getMethods();
//			if(targetPeerFieldSet.size() == 0) continue;
//			targetPeerMethodSet.addAll(peerAmMethodSet);
			if(targetPeerMethodSet.size() >= 1){
				Gson gson = new Gson();
				Connection conn = SqliteManager.getConnection();
				try {
					PreparedStatement ps = conn.prepareStatement("INSERT INTO " + Application.amCmTable
							+ " (bug_name,am_sig,used_cm,peermethods)"
	//						+ "access_precision,access_detail, access_fields)"
							+ " VALUES (?,?,?,?)");
					ps.setString(1, CommitComparator.bugName);
					ps.setString(2, amSig);
					ps.setString(3, cmSig);
					ps.setString(4, gson.toJson(targetPeerMethodSet));
	
					ps.executeUpdate();
					ps.close();
					conn.close();
					
				} catch (SQLException e) {
					e.printStackTrace();
				}
			}
		}
	}
	
	
	
	private void predictWithoutAm(ReferenceNode amNode, Set<String> cmSigSet,
			Graph<ReferenceNode, ReferenceEdge> jgrapht,
			Map<MethodReference, MethodReference> newToOldMethodRefMap,
			Map<MethodReference, MethodReference> oldToNewMethodRefMap,
			DataFlowAnalysisEngine leftEngine, DataFlowAnalysisEngine rightEngine,
			Set<IClass> allFoundClasses, Map<MethodReference, ClientMethod> oldMRefToClient,
			Map<MethodReference, ClientMethod> newMRefToClient,
			Map<MethodReference, HashSet<NodePair>> oldMethodRefToMatch,
			Map<MethodReference, HashSet<NodePair>> newMethodRefToMatch,
			Map<MethodReference, ASTNode> oMRefToAST,
			Map<MethodReference, ASTNode> nMRefToAST,
			Map<MethodReference, String> oldMethodRefToRose) {
		MethodReference amRef = (MethodReference) amNode.ref;
		String amSig = amRef.getSignature();
		TypeReference amClass = amRef.getDeclaringClass();
		String amClassName = amClass.getName().getClassName().toString();
		String amName = amRef.getName().toString();
		String amClassSig = amClass.getName().toString().substring(1).replace('/', '.');
		
		//get all the peerfileds in the AM
//		Set<String> peerAmMethodSet = null;
//		ClientMethod newAmClient = newMRefToClient.get(amRef);
//		ASTNode newAmAstNode = newAmClient.methodbody;
//		MethodNameVisitor fAmVisitor = new MethodNameVisitor(newAmAstNode, amClassSig);
//		fAmVisitor.execute();
//		peerAmMethodSet = fAmVisitor.getMethods();
//		if(peerAmMethodSet == null || peerAmMethodSet.size() == 0) return;
		
		// get CM set, old version
		
		Set<MethodReference> cmOtherSet = new HashSet<>();
//		Map<MethodReference, String> refToRealAccessMode = new HashMap<>();  // old reference to AF access mode
		for (ReferenceEdge edge: jgrapht.edgesOf(amNode)) {
			if (edge.type != ReferenceEdge.METHOD_INVOKE)
				continue;
			ReferenceNode srcNode = edge.from;
			if (srcNode.type != ReferenceNode.CM)
				continue;
			MethodReference oldCmRef = (MethodReference) srcNode.ref;
			String cmSig = oldCmRef.getSignature();
			if (!cmSigSet.contains(cmSig))
				continue;
//			MethodReference newCmRef = oldToNewMethodRefMap.get(oldCmRef);
			ClientMethod oldClient = oldMRefToClient.get(oldCmRef);
			ASTNode oldAstNode = oldClient.methodbody;
			Set<String> pMSet = null;
//			String cmClassSig = getCmClassSig(oldCmRef);
			NeoMethodVisitor methodNameVisitor = new NeoMethodVisitor(oldAstNode);
//			AmCmMethodNameVisitor methodNameVisitor = new AmCmMethodNameVisitor(oldAstNode, amClassSig, cmClassSig);
			methodNameVisitor.execute();
			pMSet = methodNameVisitor.getMethods();
//			if(targetPeerFieldSet.size() == 0) continue;
//			targetPeerMethodSet.addAll(peerAmMethodSet);
			if (pMSet.size() >= 4) {
				cmOtherSet.add(oldCmRef);
			}
				
		}
		if(cmOtherSet.size() < 2) 
			return;
		
//		if (cmSet.size() < 2)
//			return;
		
		// Check accessibility of AF
		IClassHierarchy leftHierarchy = leftEngine.getClassHierarchy();
		IClassHierarchy rightHierarchy = rightEngine.getClassHierarchy();
		IMethod iMethod = rightHierarchy.resolveMethod(amRef);
		IClass amIClass = leftHierarchy.lookupClass(amClass);
		if (amIClass == null)
			amIClass = rightHierarchy.lookupClass(amClass);
		String methodAccess = null;
		if (iMethod.isPrivate())
			methodAccess = "private";
		else if (iMethod.isProtected())
			methodAccess = "protected";
		else if (iMethod.isPublic() || amIClass.isInterface())
			methodAccess = "public";
		else
			methodAccess = "package";
		
		
		// Build method to class map
		Map<MethodReference, IClass> mRefToIClassMap = new HashMap<>();
		for (IClass iClass: allFoundClasses) {
			Collection<IMethod> declaredMethods = iClass.getDeclaredMethods();
			for (IMethod iOldMethod: declaredMethods) {
				MethodReference ref = iOldMethod.getReference();
				mRefToIClassMap.put(ref, iClass);
			}
		}
		
		// Find classes of methods candidates
		Set<IClass> classesToProcess = new HashSet<>();
		if (methodAccess.equals("private")) {
			classesToProcess.add(amIClass);
		} else if (methodAccess.equals("protected") || methodAccess.equals("package")) {
			// classes in the same package
			String methodPackage = this.getPackageOfClass(amIClass);
			for (IClass klass: allFoundClasses) {
				String packageName = this.getPackageOfClass(klass);
				if (methodPackage.equals(packageName))
					classesToProcess.add(klass);
			}
			if (methodAccess.equals("protected")) {
				// subclasses
				for (IClass klass: allFoundClasses) {
					IClass superClass = klass;
					do {
						superClass = superClass.getSuperclass();
						if (amIClass.equals(superClass)) {
							classesToProcess.add(klass);
							break;
						}
					} while (superClass != null);
				}
			}
		} else if (methodAccess.equals("public")) {
			classesToProcess.addAll(allFoundClasses);
		}
		
		// Find method candidates
		Set<MethodReference> methodCandidateSet = new HashSet<>();
		for (IClass klass: classesToProcess) {
			for (IMethod iOldMethod: klass.getDeclaredMethods()) {
				if (iOldMethod.isClinit())
					continue;
				MethodReference mRef = iOldMethod.getReference();
				methodCandidateSet.add(mRef);
			}
		}		
		
		
		
		if(cmOtherSet.size() >= 2){
			for (MethodReference usedCmRef: cmOtherSet) {
	//			MethodReference amRef = (MethodReference) amNode.ref;
	//			String cmSig = usedCmRef.getSignature();
	//			TypeReference cmClass = usedCmRef.getDeclaringClass();
	//			String cmClassName = cmClass.getName().getClassName().toString();
	//			String cmName = usedCmRef.getName().toString();
	//			String cmClassSig = cmClass.getName().toString().substring(1).replace('/', '.');
				
	//			String cmClassSig = getCmClassSig(usedCmRef);
				
				MethodReference usedCmRefNew = oldToNewMethodRefMap.get(usedCmRef);
				ClientMethod oldClient = oldMRefToClient.get(usedCmRef);
				ClientMethod newClient = newMRefToClient.get(usedCmRefNew);
				ASTNode oldAstNode = oldClient.methodbody;
				ASTNode newAstNode = newClient.methodbody;
				
	
	
				Set<String> targetPeerMethodSet = null;
	//			
				NeoMethodVisitor visitor = new NeoMethodVisitor(oldAstNode);
	//			AmCmMethodNameVisitor visitor = new AmCmMethodNameVisitor(oldAstNode, amClassSig,cmClassSig);
				visitor.execute();
				targetPeerMethodSet = visitor.getMethods();
	//			targetPeerMethodSet.addAll(peerAmMethodSet);
				
				
				Set<MethodReference> predictedCm = new HashSet<>();
				
				// Check every method candidate
	//			Map<MethodReference, Set<String>> refToFieldsMap = new HashMap<>();
				Map<MethodReference, Set<String>> refToMethodsMap = new HashMap<>();
	//			Map<MethodReference, String> refToPredictedAccessMode = new HashMap<>();  // 3 access modes: "r", "w", "rw"
	//			Map<MethodReference, Set<String>> methodToAccessFields = new HashMap<>();
				for (MethodReference mRef: methodCandidateSet) {
					if (mRef.equals(usedCmRef))
						continue;
	//				Set<String> peerFieldSet = null;
					Set<String> peerMethodSet = null;
					ASTNode ast = oMRefToAST.get(mRef);
					if (ast == null) {
						continue;
					}
					NeoMethodVisitor methodVisitor = new NeoMethodVisitor(ast);
	//				AmCmMethodNameVisitor methodVisitor = new AmCmMethodNameVisitor(ast, amClassSig,cmClassSig);
					methodVisitor.execute();
					peerMethodSet = methodVisitor.getMethods();
					peerMethodSet.retainAll(targetPeerMethodSet);
					refToMethodsMap.put(mRef, peerMethodSet);
	//				FieldNameVisitor fieldVisitor = new FieldNameVisitor(ast, amClassSig);
	//				fieldVisitor.execute();
	//				peerFieldSet = fieldVisitor.getFields();
	//				Set<String> readFields = fieldVisitor.getReadFields();
	//				Set<String> writtenFields = fieldVisitor.getWrittenFields();
					
	//				boolean considerAccessInPotentialCM = false;
					
					
					
	//				if (shouldCheckAccessMode) {
	//					
	//					Set<String> onlyReadPeerSet = new HashSet<>();
	//					onlyReadPeerSet.addAll(readFields);
	//					onlyReadPeerSet.removeAll(writtenFields);
	//					onlyReadPeerSet.retainAll(targetPeerFieldSet);
	//					
	//					Set<String> onlyWrittenPeerSet = new HashSet<>();
	//					onlyWrittenPeerSet.addAll(writtenFields);
	//					onlyWrittenPeerSet.removeAll(readFields);
	//					onlyWrittenPeerSet.retainAll(targetPeerFieldSet);
	//					
	//					Set<String> readAndWrittenPeerSet = new HashSet<>();
	//					readAndWrittenPeerSet.addAll(readFields);
	//					readAndWrittenPeerSet.retainAll(writtenFields);
	//					readAndWrittenPeerSet.retainAll(targetPeerFieldSet);
	//					
	//					if (onlyReadPeerSet.size() == 0
	//							&& onlyWrittenPeerSet.size() == 0
	//							&& readAndWrittenPeerSet.size() == 0) {
	//						peerFieldSet = Collections.emptySet();
	//					} else {
	//						Comparator<Set<String>> comparator = new Comparator<Set<String>>() {
	//							@Override
	//							public int compare(Set<String> o1, Set<String> o2) {
	//								return o2.size() - o1.size();
	//							}};
	//						PriorityQueue<Set<String>> queue = new PriorityQueue<>(3, comparator);
	//						queue.add(onlyReadPeerSet);
	//						queue.add(onlyWrittenPeerSet);
	//						queue.add(readAndWrittenPeerSet);
	//						peerFieldSet = queue.peek();
	//						
	//						methodToAccessFields.put(mRef, peerFieldSet);
	//						
	//						// predict the access mode of AF, which be the same as that of peers
	//						if (peerFieldSet == onlyReadPeerSet)
	//							refToPredictedAccessMode.put(mRef, "r");
	//						else if (peerFieldSet == onlyWrittenPeerSet)
	//							refToPredictedAccessMode.put(mRef, "w");
	//						else
	//							refToPredictedAccessMode.put(mRef, "rw");
	//						
	//						Set<String> largestPeerSet = queue.poll();
	//						Set<String> secondLargestPeerSet = queue.poll();
	//						if (largestPeerSet.size() == secondLargestPeerSet.size())
	//							refToPredictedAccessMode.put(mRef, "NA");
	//					}
	//					
	//					
	//				}
	//				peerFieldSet = fieldVisitor.getFields();
	//				peerFieldSet.retainAll(targetPeerFieldSet);
	//				refToFieldsMap.put(mRef, peerFieldSet);
				}
				
				// Find the method candidate with most or second most peer methods
				int maxPeerFieldsNum = -1, secMax = -1, maxPeerMethodsNum = -1;
				for (Set<String> peerMethodSet: refToMethodsMap.values()) {
					if (peerMethodSet.size() > maxPeerMethodsNum){
	//					secMax = maxPeerMethodsNum;
						maxPeerMethodsNum = peerMethodSet.size();
					}
	//				else if(peerMethodSet.size() < maxPeerMethodsNum){
	//					secMax = Math.max(secMax, peerMethodSet.size());
	//				}
				}
				
	//			for(Set<String> peerMethodSet : refToMethodsMap.values()){
	//				if(peerMethodSet.size() > maxPeerMethodsNum) maxPeerMethodsNum = peerMethodSet.size();
	//			}
				
				if (maxPeerMethodsNum >= 4) {
					for (MethodReference mRef: refToMethodsMap.keySet()) {
	//					Set<String> peerSet = refToFieldsMap.get(mRef);
						Set<String> peerMethodSet = refToMethodsMap.get(mRef);
	//					if (peerFieldSet.size() == maxPeerFieldsNum)
						if (peerMethodSet.size() == maxPeerMethodsNum)
	//					if(peerMethodSet.size() == maxPeerMethodsNum || (secMax >= 1 && peerMethodSet.size() >= secMax))
							predictedCm.add(mRef);
					}
				}
				
				// ----- important options-----
	//			boolean useRose = false;
	//			if (useRose) { // use Tom Zimmerman's tool ROSE
	//				predictedCm = new HashSet<>();
	//				List<String> evidenceMethods = new ArrayList<>();
	//				evidenceMethods.add(oldMethodRefToRose.get(usedCmRef));
	//				List<String> roseResult = RosePrediction.execute(evidenceMethods, Application.roseTable, CommitComparator.bugName);
	//				Map<String, MethodReference> roseToMethodRef = new HashMap<>();
	//				for (MethodReference ref: oldMethodRefToRose.keySet()) {
	//					String rose = oldMethodRefToRose.get(ref);
	//					roseToMethodRef.put(rose, ref);
	//				}
	//				for (String rose: roseResult) {
	//					MethodReference ref = roseToMethodRef.get(rose);
	//					if (ref != null)
	//						predictedCm.add(ref);
	//				}
	//				
	//			}
	
				List<String> predictedCmSigs = new ArrayList<>();
				for (MethodReference m: predictedCm) {
					predictedCmSigs.add(m.getSignature());
				}
				
				Set<String> truePositives = new HashSet<>();
				Set<String> falsePositives = new HashSet<>();
				Set<String> falseNegatives = new HashSet<>();
				Map<String, Set<String>> tpVars = new HashMap<>();
				Map<String, Set<String>> fpVars = new HashMap<>();
				Map<String, Set<String>> fnVars = new HashMap<>();
				Set<String> correctAccessPrediction = new HashSet<>();
				Set<String> predictionWithAccess = new HashSet<>();
				Map<String, Map<String, String>> accessDetail = new HashMap<>();
				
				Map<String, Set<String>> accessFields = new HashMap<>();
				
				// methodToAccessFields
				
				for (MethodReference mRef: cmOtherSet) {
					if (mRef.equals(usedCmRef))
						continue;
					if (predictedCmSigs.contains(mRef.getSignature())) {
						truePositives.add(mRef.getSignature());
	//					tpVars.put(mRef.getSignature(), refToFieldsMap.get(mRef));
						
						// process predict_access and access_precision
	//					String realAccess = refToRealAccessMode.get(mRef);
	//					String predictedAccess = refToPredictedAccessMode.get(mRef);
	//					if (!predictedAccess.equals("NA")) {
	//						Map<String, String> realAndPredictedAccess = new HashMap<>();
	//						realAndPredictedAccess.put("real", realAccess);
	//						realAndPredictedAccess.put("predicted", predictedAccess);
	//						accessDetail.put(mRef.getSignature(), realAndPredictedAccess);
	//						if (realAccess.equals(predictedAccess)) {
	//							correctAccessPrediction.add(mRef.getSignature());
	//						}
	//						predictionWithAccess.add(mRef.getSignature());
	//						accessFields.put(mRef.getSignature(), methodToAccessFields.get(mRef));
	//					}
					
					} else {
						falseNegatives.add(mRef.getSignature());
	//					fnVars.put(mRef.getSignature(), refToFieldsMap.get(mRef));
					}
				}
	//			for (MethodReference mRef: predictedCm) {
	//				if (!cmSet.contains(mRef)) {
	//					falsePositives.add(mRef.getSignature());
	//					fpVars.put(mRef.getSignature(), refToFieldsMap.get(mRef));
	//					
	//				}
	//			}
				
				int recall = 100 * truePositives.size() / (cmOtherSet.size() - 1);
				int precision = -1;
				if (!predictedCmSigs.isEmpty())
					precision = 100 * truePositives.size() / predictedCmSigs.size();
				
				int accessPrecision = -1;
				if (!predictionWithAccess.isEmpty())
					accessPrecision = 100 * correctAccessPrediction.size() / predictionWithAccess.size();
				
				// Insert data into database
				Gson gson = new Gson();
				Connection conn = SqliteManager.getConnection();
				try {
					PreparedStatement ps = conn.prepareStatement("INSERT INTO " + Application.amPredictTable
							+ " (bug_name,am_sig,used_cm,real_other_cm,predicted_cm,precision,recall, ground_truth_size, predicted_size, true_positive_size)"
	//						+ "access_precision,access_detail, access_fields)"
							+ " VALUES (?,?,?,?,?,?,?,?,?,?)");
					ps.setString(1, CommitComparator.bugName);
					ps.setString(2, amSig);
					ps.setString(3, usedCmRef.getSignature());
					Set<String> realOtherCms = new HashSet<>(cmSigSet);
					realOtherCms.remove(usedCmRef.getSignature());
					ps.setString(4, gson.toJson(realOtherCms));
					ps.setString(5, gson.toJson(predictedCmSigs));
					if (precision == -1) {
						ps.setNull(6, java.sql.Types.INTEGER);
						ps.setNull(7, java.sql.Types.INTEGER);
					}
					else {
						ps.setInt(6, precision);
						ps.setInt(7, recall);
					}
					ps.setInt(8, cmOtherSet.size() - 1);
					ps.setInt(9, predictedCmSigs.size());
					ps.setInt(10, truePositives.size());
					if(!predictedCmSigs.isEmpty()){
						if(Application.amPredictTable.equals("am_predict_aries")){
							Application.tasks[0]++;
							Application.predictTable[0] += 1.0 * truePositives.size()/predictedCmSigs.size();
							Application.recallTable[0] += 1.0 * recall / 100;
						}
						else if(Application.amPredictTable.equals("am_predict_cassandra")){
							Application.tasks[1]++;
							Application.predictTable[1] += 1.0 * truePositives.size()/predictedCmSigs.size();
							Application.recallTable[1] += 1.0 * recall / 100;
						}
						else if(Application.amPredictTable.equals("am_predict_derby")){
							Application.tasks[2]++;
							Application.predictTable[2] += 1.0 * truePositives.size()/predictedCmSigs.size();
							Application.recallTable[2] += 1.0 * recall / 100;
						}
						else{
							Application.tasks[3]++;
							Application.predictTable[3] += 1.0 * truePositives.size()/predictedCmSigs.size();
							Application.recallTable[3] += 1.0 * recall / 100;
						}
					}
	//				if (accessPrecision == -1)
	//					ps.setNull(8, java.sql.Types.INTEGER);
	//				else
	//					ps.setInt(8, accessPrecision);
	//				ps.setString(9, gson.toJson(accessDetail));
	//				ps.setString(10, gson.toJson(accessFields));
						
					
					
					
					ps.executeUpdate();
					ps.close();
					conn.close();
					
				} catch (SQLException e) {
					e.printStackTrace();
				}
				
				//--------------------------------
			}
		}
		
		
	}
	
	
	boolean compareName(MethodReference m1, MethodReference m2){
		String m1Name = "" + m1.getName(), m2Name = "" + m2.getName();
		if(m1Name.equals(m2Name) || m1Name.contains(m2Name) || m2Name.contains(m1Name)) return true;
		int pre = m2Name.length();
		while (pre > 0 && !m1Name.contains(m2Name.substring(0, pre))) pre--;
		int post = 0;
		while (post < m2Name.length() && !m1Name.contains(m2Name.substring(post))) post++;
		if(pre > 3 || post < m2Name.length() - 3) return true;
		return false;
	}
	
	boolean hasSameReturnType(MethodReference m1, MethodReference m2){
		String sig1 = m1.getSignature(), sig2 = m2.getSignature();
		int index1 = sig1.indexOf(')'), index2 = sig2.indexOf(')');
		return sig1.substring(index1 + 1).equals(sig2.substring(index2 + 1));
	}
	
	String returnTypeOfAm(MethodReference am){
		String res =  ("" + am.getReturnType().getName()).replace('/', '.');
		return dealWithType(res);
	}
	
	Set<String> argumentsTypeOfAm(MethodReference am){
		Set<String> set = new HashSet<>();
		int number = am.getNumberOfParameters();
		for (int i = 0; i < number ; i++){
			String res = ("" + am.getParameterType(i).getName()).replace('/', '.');
			set.add(dealWithType(res));
		}
		return set;
	}
	
	String dealWithType(String res){
		boolean isArray = false;
		if (res.charAt(0) == '[') {
			isArray = true;
			res = res.substring(1);
		}
//		if (res.contains("Ljava")){
//			res = res.replace("Ljava", "java");
//		}
//		if (res.contains("Lorg")) {
//			res = res.replace("Lorg", "org");
//		}
//		if (res.contains("LUNKNOWN")) {
//			res = res.replace("LUNKNOWNP", "UNKNOWNP");
//		}
//		  
		if (res.charAt(0) == 'L' && !res.contains("UNKNOWN")) {
			res = res.substring(1);
		}

		if(res.equals("V"))  res = "void";
		else if(res.equals("I")) res = "int";
		else if(res.equals("Z")) res = "boolean";
		else if(res.equals("J")) res = "long";
		else if(res.equals("F")) res = "float";
		else if(res.equals("D")) res = "double";
		else if(res.equals("B")) res = "byte";
		else if(res.equals("C")) res = "char";
		else if(res.equals("S")) res = "short";
		return isArray? res + "[]" : res;
	}
	
}
