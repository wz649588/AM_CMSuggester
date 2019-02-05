package edu.vt.cs.changes;

import java.lang.reflect.Field;
import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.SQLException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.PriorityQueue;
import java.util.Set;

import org.eclipse.jdt.core.dom.ASTNode;
import org.jgrapht.Graph;

import partial.code.grapa.commit.CommitComparator;
import partial.code.grapa.dependency.graph.DataFlowAnalysisEngine;
import partial.code.grapa.mapping.ClientMethod;
import ch.uzh.ifi.seal.changedistiller.treedifferencing.NodePair;

import com.google.gson.Gson;
import com.ibm.wala.classLoader.IClass;
import com.ibm.wala.classLoader.IField;
import com.ibm.wala.classLoader.IMethod;
import com.ibm.wala.ipa.cha.IClassHierarchy;
import com.ibm.wala.types.FieldReference;
import com.ibm.wala.types.MethodReference;
import com.ibm.wala.types.TypeReference;

import consolegsydit.Application;
import edu.vt.cs.graph.ReferenceEdge;
import edu.vt.cs.graph.ReferenceNode;
import edu.vt.cs.prediction.neo.FieldNameVisitor;
import edu.vt.cs.sql.SqliteManager;

/**
 * 
 * @author Ye Wang
 * @since 05/01/2018
 */
public class ApproachComparison {
	private static Object getPrivateFieldValue(Object c, String fieldName) throws NoSuchFieldException {
		Class<?> klass = c.getClass();
		Field field = null;
		try {
			field = klass.getDeclaredField(fieldName);
		} catch (SecurityException e) {
			e.printStackTrace();
		}
		
		field.setAccessible(true);
		Object fieldObject = null;
		try {
			fieldObject = field.get(c);
		} catch (IllegalArgumentException | IllegalAccessException e) {
			e.printStackTrace();
		}
		return fieldObject;
	}
	
	private static String getPackageOfClass(IClass klass) {
		com.ibm.wala.types.TypeName typeName = klass.getName();
		String packageName = null;
		try {
			Object typeNameKey = getPrivateFieldValue(typeName, "key");
			Object packageNameAtom = getPrivateFieldValue(typeNameKey, "packageName");
			if (packageNameAtom == null)
				return null;
			else
				packageName = packageNameAtom.toString();
		} catch (NoSuchFieldException e) {
			e.printStackTrace();
		}
		return packageName;
	}
	
	private static boolean isConstantNamingPattern(String name) {
		for (char c: name.toCharArray()) {
			if (!Character.isUpperCase(c) && !Character.isDigit(c) && c != '_')
				return false;
		}
		return true;
	}
	
	public static void compare(ReferenceNode afNode, Set<String> cmSigSet,
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
			String fieldPackage = getPackageOfClass(afIClass);
			for (IClass klass: allFoundClasses) {
				String packageName = getPackageOfClass(klass);
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
			
			Set<MethodReference> predictedCm = new HashSet<>();
			
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
//				peerFieldSet = fieldVisitor.getFields();
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
						predictedCm.add(mRef);
				}
			}
			
			// ----- important options-----
			boolean useRose = true;
			Set<MethodReference> predictedCmRose = new HashSet<>();
			if (useRose) { // use Tom Zimmerman's tool ROSE
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
						predictedCmRose.add(ref);
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
			
			for (MethodReference mRef: predictedCm) {
				if (mRef.equals(usedCmRef))
					continue;
				if (cmSet.contains(mRef))
					truePositives.add(mRef.getSignature());
				else
					falsePositives.add(mRef.getSignature());
			}
			
			Set<String> truePositivesRose = new HashSet<>();
			Set<String> falsePositivesRose = new HashSet<>();
			for (MethodReference mRef: predictedCmRose) {
				if (mRef.equals(usedCmRef))
					continue;
				if (cmSet.contains(mRef))
					truePositivesRose.add(mRef.getSignature());
				else
					falsePositivesRose.add(mRef.getSignature());
			}
			
			

			/*
			 * + " (bug_name TEXT,af_sig TEXT,truth_size INTEGER,"
				+ "used_cm TEXT,used_cm_peer TEXT,"
				+ "real_other_cm TEXT,"
				+ "predicted_cm_ours TEXT,predicted_size_ours INTEGER,predicted_vars_ours TEXT,"
				+ "tp_ours TEXT,tp_num_ours INTEGER,fp_ours TEXT,fp_num_ours INTEGER,"
				+ "extra_tp_ours TEXT, extra_tp_num_ours INTEGER,"
				+ "predicted_cm_rose TEXT,predicted_size_rose INTEGER,predicted_vars_rose TEXT,"
				+ "tp_rose TEXT,tp_num_rose INTEGER,fp_rose TEXT,fp_num_rose INTEGER,"
				+ "extra_tp_rose TEXT, extra_tp_num_rose INTEGER)");
			 */
			
			// Insert data into database
			Gson gson = new Gson();
			Connection conn = SqliteManager.getConnection();
			try {
				PreparedStatement ps = conn.prepareStatement("INSERT INTO " + Application.afPredictTable
						+ " (bug_name,af_sig,truth_size,"
						+ "used_cm,used_cm_peer,"
						+ "real_other_cm,"
						+ "predicted_cm_ours,predicted_size_ours,predicted_vars_ours,"
						+ "tp_ours,tp_num_ours,fp_ours,fp_num_ours,"
						+ "extra_tp_ours,extra_tp_num_ours,"
						+ "predicted_cm_rose,predicted_size_rose,predicted_vars_rose,"
						+ "tp_rose,tp_num_rose,fp_rose,fp_num_rose,"
						+ "extra_tp_rose,extra_tp_num_rose)"
						+ " VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)");
				
				
				ps.setString(1, CommitComparator.bugName);
				ps.setString(2, afSig);
				ps.setInt(3, cmSet.size());
				ps.setString(4, usedCmRef.getSignature());
				ps.setString(5, gson.toJson(targetPeerFieldSet)); // used_cm_peer
				
				Set<String> realOtherCms = new HashSet<>(cmSigSet);
				realOtherCms.remove(usedCmRef.getSignature());
				ps.setString(6, gson.toJson(realOtherCms)); // real_other_cm
				
				
				ps.setString(7, gson.toJson(predictedCmSigs)); // predicted_cm_ours
				ps.setInt(8, predictedCmSigs.size()); // predicted_size_ours
				
				//refToFieldsMap
				Map<String, Set<String>> predictedVarsOurs = new HashMap<>();
				for (MethodReference m: predictedCm) {
					Set<String> peers = refToFieldsMap.get(m);
					predictedVarsOurs.put(m.getSignature(), peers);
				}
				ps.setString(9, gson.toJson(predictedVarsOurs));
				ps.setString(10, gson.toJson(truePositives));
				ps.setInt(11, truePositives.size());
				ps.setString(12, gson.toJson(falsePositives));
				ps.setInt(13, falsePositives.size());
				
				Set<String> extraTpOurs = new HashSet<>(truePositives);
				extraTpOurs.removeAll(truePositivesRose);
				ps.setString(14, gson.toJson(extraTpOurs));
				ps.setInt(15, extraTpOurs.size());
				
				Set<String> predictedCmSigRose = new HashSet<>();
				for (MethodReference m: predictedCmRose) {
					predictedCmSigRose.add(m.getSignature());
				}
				ps.setString(16, gson.toJson(predictedCmSigRose));
				ps.setInt(17, predictedCmSigRose.size());
				
				Map<String, String> refToRose = new HashMap<>();
				for (MethodReference m: predictedCmRose) {
					String rose = oldMethodRefToRose.get(m);
					refToRose.put(m.getSignature(), rose);
				}
				ps.setString(18, gson.toJson(refToRose));
				
				ps.setString(19, gson.toJson(truePositivesRose));
				ps.setInt(20, truePositivesRose.size());
				ps.setString(21, gson.toJson(falsePositivesRose));
				ps.setInt(22, falsePositivesRose.size());
				
				Set<String> extraTpRose = new HashSet<>(truePositivesRose);
				extraTpRose.removeAll(truePositives);
				ps.setString(23, gson.toJson(extraTpRose));
				ps.setInt(24, extraTpRose.size());
				
				
				
				
				
				ps.executeUpdate();
				ps.close();
				conn.close();
				
			} catch (SQLException e) {
				e.printStackTrace();
			}
			
			//--------------------------------
		}
		
	}
	
	// multi-predict
	private static void multiPredict(List<MethodReference> evidenceCms,
			Map<MethodReference, MethodReference> oldToNewMethodRefMap,
			Map<MethodReference, ClientMethod> oldMRefToClient,
			Map<MethodReference, ClientMethod> newMRefToClient,
			String afName, String afClassSig,
			boolean shouldCheckNamingPattern,
			boolean shouldCheckAccessMode,
			Set<MethodReference> methodCandidateSet,
			Map<MethodReference, ASTNode> oMRefToAST,
			Set<MethodReference> predictedCm,
			Map<MethodReference, Set<String>> evidencePeerMap,
			Map<MethodReference, Map<MethodReference, Set<String>>> evidenceToPredictionPeerMap) {
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
			
			Map<MethodReference, Set<String>> currentPredictionMap = new HashMap<>();
			for (MethodReference m: currentPredictedCm) {
				Set<String> peers = refToFieldsMap.get(m);
				currentPredictionMap.put(m, peers);
			}
			
			evidenceToPredictionPeerMap.put(usedCmRef, currentPredictionMap);
			predictedCm.addAll(currentPredictedCm);
		}
	}

	public static void execute(ReferenceNode afNode, Set<String> cmSigSet,
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
			String fieldPackage = getPackageOfClass(afIClass);
			for (IClass klass: allFoundClasses) {
				String packageName = getPackageOfClass(klass);
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
		int evidenceSize = 2;
		// -------------- END important options --------------
		
		if (cmSet.size() <= 4)
			return;
		
		// divide CM set into evidence and to-be-predicted
		Map<List<MethodReference>, List<MethodReference>> evidenceToReal =
				DivisionUtil.divide(cmSet, evidenceSize);
		
		for (List<MethodReference> evidenceCms: evidenceToReal.keySet()) {
			List<MethodReference> realOtherCmRefs = evidenceToReal.get(evidenceCms);
			Set<MethodReference> predictedCmFor2cm = new HashSet<>();
			
			Map<MethodReference, Set<String>> evidencePeerMap = new HashMap<>();
			Map<MethodReference, Map<MethodReference, Set<String>>> evidenceToPredictionPeerMap = new HashMap<>();
			
			multiPredict(evidenceCms, oldToNewMethodRefMap, oldMRefToClient, newMRefToClient,
					afName, afClassSig, shouldCheckNamingPattern, shouldCheckAccessMode,
					methodCandidateSet, oMRefToAST,
					predictedCmFor2cm, evidencePeerMap, evidenceToPredictionPeerMap);
			
			List<String> predictedCmSigsFor2cm = new ArrayList<>();
			for (MethodReference m: predictedCmFor2cm) {
				predictedCmSigsFor2cm.add(m.getSignature());
			}
			
			Set<String> truePositivesFor2cm = new HashSet<>();
			Set<String> falsePositivesFor2cm = new HashSet<>();
			
			for (MethodReference mRef: predictedCmFor2cm) {
				if (evidenceCms.contains(mRef))
					continue;
				if (realOtherCmRefs.contains(mRef))
					truePositivesFor2cm.add(mRef.getSignature());
				else
					falsePositivesFor2cm.add(mRef.getSignature());
			}
			
			Map<String, Set<String>> used2cmPeer = new HashMap<>();
			for (MethodReference m: evidencePeerMap.keySet()) {
				Set<String> peers = evidencePeerMap.get(m);
				used2cmPeer.put(m.getSignature(), peers);
			}
			
//			evidenceToPredictionPeerMap
			Map<String, Map<String, Set<String>>> predictedVars2cm = new HashMap<>();
			for (MethodReference m: evidenceToPredictionPeerMap.keySet()) {
				Map<MethodReference, Set<String>> map = evidenceToPredictionPeerMap.get(m);
				Map<String, Set<String>> sigMap = new HashMap<>();
				for (MethodReference mm: map.keySet()) {
					Set<String> peers = map.get(mm);
					sigMap.put(mm.getSignature(), peers);
				}
				predictedVars2cm.put(m.getSignature(), sigMap);
			}
			
			
			
			// construct 3CM data set
			for (MethodReference extraEvidence: realOtherCmRefs) {
				List<MethodReference> evidenceCmsFor3cm = new ArrayList<>(evidenceCms);
				evidenceCmsFor3cm.add(extraEvidence);
				List<MethodReference> realOtherCmRefsFor3cm = new ArrayList<>(realOtherCmRefs);
				realOtherCmRefsFor3cm.remove(extraEvidence);
				
				Set<MethodReference> predictedCmFor3cm = new HashSet<>();
				
				Map<MethodReference, Set<String>> evidencePeerMapFor3cm = new HashMap<>();
				Map<MethodReference, Map<MethodReference, Set<String>>> evidenceToPredictionPeerMapFor3cm = new HashMap<>();
				
				multiPredict(evidenceCmsFor3cm, oldToNewMethodRefMap, oldMRefToClient, newMRefToClient,
						afName, afClassSig, shouldCheckNamingPattern, shouldCheckAccessMode,
						methodCandidateSet, oMRefToAST,
						predictedCmFor3cm, evidencePeerMapFor3cm, evidenceToPredictionPeerMapFor3cm);
				
				Map<String, Set<String>> used3cmPeer = new HashMap<>();
				for (MethodReference m: evidencePeerMapFor3cm.keySet()) {
					Set<String> peers = evidencePeerMapFor3cm.get(m);
					used3cmPeer.put(m.getSignature(), peers);
				}
				
				Set<MethodReference> extraTp = new HashSet<>(predictedCmFor3cm);
				extraTp.removeAll(predictedCmFor2cm);
				extraTp.removeAll(evidenceCmsFor3cm);
				
				if (extraTp.isEmpty())
					continue;
				
				
				/*
				+ " (bug_name TEXT,af_sig TEXT,truth_size INTEGER,"
				+ "used_2cm TEXT,used_2cm_peer TEXT,"
				+ "used_3cm TEXT,used_3cm_peer TEXT,"
				+ "real_other_2cm TEXT,real_other_3cm,"
				+ "predicted_2cm TEXT,predicted_size_2cm INTEGER,predicted_vars_2cm TEXT,"
				+ "tp_2cm TEXT,tp_num_2cm INTEGER,fp_2cm TEXT,fp_num_2cm INTEGER,"
				+ "predicted_3cm TEXT,predicted_size_3cm INTEGER,predicted_vars_3cm TEXT,extra_tp TEXT,"
				+ "tp_3cm TEXT,tp_num_3cm INTEGER,fp_3cm TEXT,fp_num_3cm INTEGER)");
				*/
				
				Gson gson = new Gson();
				Connection conn = SqliteManager.getConnection();
				try {
					PreparedStatement ps = conn.prepareStatement("INSERT INTO " + Application.afPredictTable
							+ " (bug_name,af_sig,truth_size,used_2cm,used_2cm_peer,"
							+ "used_3cm,used_3cm_peer,"
							+ "real_other_2cm,real_other_3cm,"
							+ "predicted_2cm,predicted_size_2cm,predicted_vars_2cm,"
							+ "tp_2cm,tp_num_2cm,fp_2cm,fp_num_2cm,"
							+ "predicted_3cm,predicted_size_3cm,predicted_vars_3cm,extra_tp,"
							+ "tp_3cm,tp_num_3cm,fp_3cm,fp_num_3cm)"
							+ " VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)");
					ps.setString(1, CommitComparator.bugName); // bug_name
					ps.setString(2, afSig); // af_sig
					ps.setInt(3, cmSet.size()); // truth_size
					List<String> evidenceCmSigs = new ArrayList<>();
					for (MethodReference m: evidenceCms)
						evidenceCmSigs.add(m.getSignature());
					ps.setString(4, gson.toJson(evidenceCmSigs)); // used_2cm
					ps.setString(5, gson.toJson(used2cmPeer)); // used_2cm_peer
					List<String> evidenceCmSigsFor3cm = new ArrayList<>();
					for (MethodReference m: evidenceCmsFor3cm)
						evidenceCmSigsFor3cm.add(m.getSignature());
					ps.setString(6, gson.toJson(evidenceCmSigsFor3cm)); // used_3cm
					ps.setString(7, gson.toJson(used3cmPeer)); // used_3cm_peer
					
					Set<String> realOtherCms = new HashSet<>();
					for (MethodReference m: realOtherCmRefs)
						realOtherCms.add(m.getSignature());
					ps.setString(8, gson.toJson(realOtherCms)); // real_other_2cm
					
					Set<String> realOtherCmsFor3cm = new HashSet<>();
					for (MethodReference m: realOtherCmRefsFor3cm)
						realOtherCmsFor3cm.add(m.getSignature());
					ps.setString(9, gson.toJson(realOtherCmsFor3cm)); // real_other_3cm
					
					ps.setString(10, gson.toJson(predictedCmSigsFor2cm)); // predicted_2cm
					ps.setInt(11, predictedCmSigsFor2cm.size()); // predicted_size_2cm
					ps.setString(12, gson.toJson(predictedVars2cm)); // // predicted_vars_2cm
					
					ps.setString(13, gson.toJson(truePositivesFor2cm)); // tp_2cm
					ps.setInt(14, truePositivesFor2cm.size()); // tp_num_2cm
					ps.setString(15, gson.toJson(falsePositivesFor2cm)); // fp_2cm
					ps.setInt(16, falsePositivesFor2cm.size()); // fp_num_2cm
					
					List<String> predictedCmSigsFor3cm = new ArrayList<>();
					for (MethodReference m: predictedCmFor3cm) {
						predictedCmSigsFor3cm.add(m.getSignature());
					}
					ps.setString(17, gson.toJson(predictedCmSigsFor3cm)); // predicted_size_2cm
					ps.setInt(18, predictedCmSigsFor3cm.size()); // predicted_size_2cm
					
					Map<String, Map<String, Set<String>>> predictedVars3cm = new HashMap<>();
					for (MethodReference m: evidenceToPredictionPeerMapFor3cm.keySet()) {
						Map<MethodReference, Set<String>> map = evidenceToPredictionPeerMapFor3cm.get(m);
						Map<String, Set<String>> sigMap = new HashMap<>();
						for (MethodReference mm: map.keySet()) {
							Set<String> peers = map.get(mm);
							sigMap.put(mm.getSignature(), peers);
						}
						predictedVars3cm.put(m.getSignature(), sigMap);
					}
					ps.setString(19, gson.toJson(predictedVars3cm)); // predicted_vars_3cm
					
					List<String> extraTpSigs = new LinkedList<>();
					for (MethodReference m: extraTp)
						extraTpSigs.add(m.getSignature());
					ps.setString(20, gson.toJson(extraTpSigs)); // extra_tp
					
					Set<String> truePositivesFor3cm = new HashSet<>();
					Set<String> falsePositivesFor3cm = new HashSet<>();
					
					for (MethodReference mRef: predictedCmFor3cm) {
						if (evidenceCmsFor3cm.contains(mRef))
							continue;
						if (realOtherCmRefsFor3cm.contains(mRef))
							truePositivesFor3cm.add(mRef.getSignature());
						else
							falsePositivesFor3cm.add(mRef.getSignature());
					}
					
					ps.setString(21, gson.toJson(truePositivesFor3cm)); // tp_3cm
					ps.setInt(22, truePositivesFor3cm.size()); // tp_num_3cm
					ps.setString(23, gson.toJson(falsePositivesFor3cm)); // fp_3cm
					ps.setInt(24, falsePositivesFor3cm.size()); // fp_num_3cm
						
					ps.executeUpdate();
					ps.close();
					conn.close();
					
				} catch (SQLException e) {
					e.printStackTrace();
				}
				
			}
			
		}
	}
}
