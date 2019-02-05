package edu.vt.cs.changes;

import java.io.File;
import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.CompilationUnit;

import com.ibm.wala.util.collections.Pair;

import consolegsydit.Application;
import partial.code.grapa.mapping.ClientMethod;
import ch.uzh.ifi.seal.changedistiller.model.classifiers.ChangeType;
import ch.uzh.ifi.seal.changedistiller.model.classifiers.EntityType;
import ch.uzh.ifi.seal.changedistiller.model.classifiers.SourceRange;
import ch.uzh.ifi.seal.changedistiller.model.classifiers.java.JavaEntityType;
import ch.uzh.ifi.seal.changedistiller.model.entities.SourceCodeChange;
import ch.uzh.ifi.seal.changedistiller.model.entities.SourceCodeEntity;
import ch.uzh.ifi.seal.changedistiller.treedifferencing.NodePair;
import ch.uzh.ifi.seal.changedistiller.treedifferencing.TreeEditOperation;
import edu.vt.cs.append.CompositeEntity;
import edu.vt.cs.append.FineChangesInMethod;
import edu.vt.cs.diffparser.util.SourceCodeRange;
import edu.vt.cs.editscript.EditScriptRecorder;
import edu.vt.cs.editscript.TreeMatchRecorder;
import edu.vt.cs.grapa.extension.ClientContainingMapper;
import edu.vt.cs.grapa.extension.ClientEntityFinder;
import edu.vt.cs.grapa.extension.ClientFieldFinder;
import edu.vt.cs.grapa.extension.ClientMethodFinder;
import edu.vt.cs.graph.ClientClass;
import edu.vt.cs.graph.ClientField;
import edu.vt.cs.sql.SqliteManager;

public class ChangeFact {

	File left = null;
	File right = null;
	Map<SourceCodeEntity, SourceCodeChange> entityChanges = null;
	
	List<Pair<ClientMethod, ClientMethod>> changedMethods = null;
	public List<ChangeMethodData> changedMethodData = null;
	List<ClientMethod> insertedMethods = null;
	List<ClientMethod> deletedMethods = null;
	List<Pair<ClientField, ClientField>> changedFields = null;
	List<ClientField> insertedFields = null;
	List<ClientField> deletedFields = null;
	List<ClientClass> insertedClasses = null;
	List<ClientClass> deletedClasses = null;
	List<Pair<ClientClass, ClientClass>> changedClasses = null;
	Map<SourceCodeRange, SourceCodeEntity> rangeToEntity = null;
	
	// Added by Ye Wang, to record edit scripts for method
	Map<ClientMethod, List<TreeEditOperation>> oldMethodToScript = new HashMap<>();
	Map<ClientMethod, List<TreeEditOperation>> newMethodToScript = new HashMap<>();
	
	// Ye Wang since 06/05/2017, record tree matches for method
	Map<ClientMethod, HashSet<NodePair>> oldMethodToMatch = new HashMap<>();
	Map<ClientMethod, HashSet<NodePair>> newMethodToMatch = new HashMap<>();
	
	// Ye Wang, 06/29/2017
	public Collection<ClientMethod> lMethods;
	public Collection<ClientMethod> rMethods;
	
	public Collection<ClientClass> lClasses;
	public Collection<ClientClass> rClasses;
	
	// added by Ye Wang, 03/08/2018
	public Map<ClientClass, List<ClientMethod>> acToAms = new HashMap<>();
	public Map<ClientClass, List<ClientMethod>> dcToDms = new HashMap<>();
	public Map<ClientClass, List<ClientField>> acToAfs = new HashMap<>();
	public Map<ClientClass, List<ClientField>> dcToDfs = new HashMap<>();
	
	// added by Ye Wang, 04/13/2018
//	public Map<ClientMethod, String> oldClientMethodToRose = new HashMap<>();
	
	// added by Ye Wang, 04/15/2018
	public Map<String, ClientMethod> leftRoseToClientMethod = new HashMap<>();
	
	
	public ChangeFact(File l, File r, List<SourceCodeChange> changes) {
		
		left = l;
		right = r;		
		entityChanges = new HashMap<SourceCodeEntity, SourceCodeChange>();
		rangeToEntity = new HashMap<SourceCodeRange, SourceCodeEntity>();
		EntityType et = null;
		SourceCodeEntity sc = null;
		SourceCodeChange c = null;		
		
		int i = 0;
		int size = changes.size();
		
			while (i < size) {
				c = changes.get(i);
				sc = c.getChangedEntity();
				if (sc == null) {
					// do not process deleted or added files
				} else {
					et = sc.getType();
					try{
						if (et.isClass() || et.isField() || et.isMethod()) {
							entityChanges.put(sc, c);
							SourceCodeRange range = null;
							if (et.isMethod()) {							
								SourceCodeEntity old = ((CompositeEntity)sc).getOldEntity();								
								range = SourceCodeRange.convert(old);
							} else{
								range = SourceCodeRange.convert(sc);
							}							
							rangeToEntity.put(range, sc);
						} else {
							System.err.println("Need more process");				
						}	
					} catch(Exception e) {
						entityChanges.put(sc, c);
					}		
				}				
				i++;
			}		
	}
	
	public int countChangedEntities() {
		return entityChanges.size();
	}
	
	public SourceCodeChange getChange(SourceCodeEntity e) {
		return entityChanges.get(e);
	}
	
	public static ClientClass getClass(Map<String, ClientClass> map, String name) {
		ClientClass c = map.get(name);
		return c;
	}
	
	public SourceCodeEntity getEntity(SourceCodeRange r) {		
		return rangeToEntity.get(r);
	}
	
	public static ClientField getField(Map<String, ClientField> map, String name) {
		ClientField f = map.get(name);
		if (f == null) {
			name = name.substring(0, name.indexOf(":"));
			String key = null;
			ClientField value = null;
			String keySub = null;
			for (Entry<String, ClientField> entry : map.entrySet()) {
				key = entry.getKey();
				value = entry.getValue();
				keySub = key.substring(0, key.indexOf(":"));
				if (keySub.equals(name)) { 
					f = value;
					break;
				}
			}
		}	
		return f;
	}
	
	public static void extractChangesForRose(String commitName, List<ChangeFact> cfList) throws SQLException {
		for (ChangeFact cf: cfList) {
			File oFile = cf.left;
			File nFile = cf.right;
			
			if (oFile == null && nFile == null)
				continue;
			
			for (SourceCodeEntity entity: cf.entityChanges.keySet()) {
//				SourceCodeChange sc = cf.entityChanges.get(entity);
				EntityType et = entity.getType();
				if (entity instanceof CompositeEntity) {	
					CompositeEntity cEntity = (CompositeEntity)entity;
					SourceCodeEntity oEntity = cEntity.getOldEntity();
					SourceCodeEntity nEntity = cEntity.getNewEntity();
					String oName = oEntity.getUniqueName();
					String nName = nEntity.getUniqueName();
					if (et.equals(JavaEntityType.METHOD)) {
						Connection conn = SqliteManager.getConnection();
						PreparedStatement ps = conn.prepareStatement("INSERT INTO "+ Application.roseTable
								+ " (bug_name,old_name,new_name) VALUES (?,?,?)");
						ps.setString(1, commitName);
						ps.setString(2, oName);
						ps.setString(3, nName);
						ps.executeUpdate();
						ps.close();
						conn.close();
					}
				}
			}
		}
	}
	
	
	public static void refineChanges(List<ChangeFact> cfList, List<File> oldFiles, List<File> newFiles,
			List<ASTNode> leftTrees, List<ASTNode> rightTrees) {
		Map<String, ASTNode> leftTreeMap = convertToMap(leftTrees);
		Map<String, ASTNode> rightTreeMap = convertToMap(rightTrees);
		SourceCodeEntity entity = null;
		SourceCodeChange sc = null;
		CompositeEntity cEntity = null;
		File oFile = null, nFile = null;
		SourceCodeEntity oEntity = null, nEntity = null;
		ASTNode lTree = null, rTree = null;		
		Set<ChangeFact> toRemove = new HashSet<ChangeFact>();
		for (ChangeFact cf : cfList) {
			oFile = cf.left;
			nFile = cf.right;
//			ClientMethodFinder oFinder = new ClientMethodFinder();
//			ClientMethodFinder nFinder = new ClientMethodFinder();
//			ClientFieldFinder ofFinder = new ClientFieldFinder();
//			ClientFieldFinder nfFinder = new ClientFieldFinder();
			ClientEntityFinder oFinder = new ClientEntityFinder();
			ClientEntityFinder nFinder = new ClientEntityFinder();
			
			lTree = findTree(oFile, leftTreeMap);
			rTree = findTree(nFile, rightTreeMap);
			
			// Ye Wang, 02/25/2018
			if (lTree == null && rTree == null) { // the file is a test file
				toRemove.add(cf);
				continue;
			}
			
			if (oFile != null && lTree == null || nFile != null && rTree == null) { // Ye Wang, parsing failed
				toRemove.add(cf);
				continue;
			}
			
			if (lTree != null) // added by Ye Wang, 02/25/2018
				lTree.accept(oFinder);
			Map<String, ClientMethod> lmap = oFinder.methods;
			Map<String, ClientField> lfmap = oFinder.fields;
			Map<String, ClientClass> lcmap = oFinder.classes;
//			lTree.accept(ofFinder);
//			Map<String, ClientField> lfmap = ofFinder.fields;
			cf.lMethods = lmap.values();
			cf.lClasses = lcmap.values();
			
			cf.leftRoseToClientMethod = lmap;
			
			
			if (rTree != null) // added by Ye Wang, 02/25/2018
				rTree.accept(nFinder);
			Map<String, ClientMethod> rmap = nFinder.methods;
			Map<String, ClientField> rfmap = nFinder.fields;
			Map<String, ClientClass> rcmap = nFinder.classes;
//			rTree.accept(nfFinder);
//			Map<String, ClientField> rfmap = nfFinder.fields;
			cf.rMethods = rmap.values();
			cf.rClasses = rcmap.values();
			
			ClientMethod lMethod = null, rMethod = null;
			ClientField lField = null, rField = null;
			ClientClass lClass = null, rClass = null;
			
			List<Pair<ClientMethod, ClientMethod>> changedMethods = new ArrayList<Pair<ClientMethod, ClientMethod>>();
			List<ChangeMethodData> changedMethodData = new ArrayList<ChangeMethodData>();
			
			List<ClientMethod> deletedMethods = new ArrayList<ClientMethod>();
			List<ClientMethod> addedMethods = new ArrayList<ClientMethod>();
			List<Pair<ClientField, ClientField>> changedFields = new ArrayList<Pair<ClientField, ClientField>>();
			List<ClientField> deletedFields = new ArrayList<ClientField>();
			List<ClientField> addedFields = new ArrayList<ClientField>();
			List<ClientClass> addedClasses = new ArrayList<ClientClass>();
			List<ClientClass> deletedClasses = new ArrayList<ClientClass>();
			List<Pair<ClientClass, ClientClass>> changedClasses = new ArrayList<Pair<ClientClass, ClientClass>>();
			
			EditScriptRecorder scriptRecorder = EditScriptRecorder.recorder;
			
			if (oFile == null) { // file is added
				addedMethods.addAll(rmap.values());
				addedFields.addAll(rfmap.values());
				ClientContainingMapper mapper = new ClientContainingMapper();
				rTree.accept(mapper);
				cf.acToAms = mapper.classToMethodList;
				cf.acToAfs = mapper.classToFieldList;
			}
			if (nFile == null) { // file is deleted
				deletedMethods.addAll(lmap.values());
				deletedFields.addAll(lfmap.values());
				ClientContainingMapper mapper = new ClientContainingMapper();
				lTree.accept(mapper);
				cf.dcToDms = mapper.classToMethodList;
				cf.dcToDfs = mapper.classToFieldList;
			}
			
			for(Entry<SourceCodeEntity, SourceCodeChange> entry : cf.entityChanges.entrySet()) {
				entity = entry.getKey();
				sc = entry.getValue();
				EntityType et = entity.getType();
				if (entity instanceof CompositeEntity) {	
					cEntity = (CompositeEntity)entity;
					oEntity = cEntity.getOldEntity();
					nEntity = cEntity.getNewEntity();					
					String oName = oEntity.getUniqueName();
					String nName = nEntity.getUniqueName();	
					
					if (et.equals(JavaEntityType.METHOD)) {
						lMethod = lmap.get(oName);
						if (lMethod != null) {
							lMethod.ast = lTree;
							
							// Added by Ye Wang, 03/23/2017
							List<TreeEditOperation> ops = scriptRecorder.findEditScriptByLeftEntity(oEntity);
							if (ops != null) {
								cf.oldMethodToScript.put(lMethod, ops);
							}
							// End
							
							// Ye Wang, 06/05/2017
							HashSet<NodePair> match = TreeMatchRecorder.recorder.findMatchByLeftEntity(oEntity);
							if (match != null) {
								cf.oldMethodToMatch.put(lMethod, match);
							}
							// END	
							
						}
						rMethod = rmap.get(nName);
						if (rMethod != null) {
							rMethod.ast = rTree;
							
							// Added by Ye Wang, 03/23/2017
							List<TreeEditOperation> ops = scriptRecorder.findEditScriptByRightEntity(nEntity);
							if (ops != null) {
								cf.newMethodToScript.put(rMethod, ops);
							}
							// End
							
							// Ye Wang, 06/05/2017
							HashSet<NodePair> match = TreeMatchRecorder.recorder.findMatchByRightEntity(nEntity);
							if (match != null) {
								cf.newMethodToMatch.put(rMethod, match);
							}
							// END
							
						}
						if (lMethod == null && rMethod != null) {
							addedMethods.add(rMethod);
						} else if (rMethod == null && lMethod != null) {						
							deletedMethods.add(lMethod);
						} else if (lMethod != null && rMethod != null){
							List<SourceCodeChange> changes = ((FineChangesInMethod)sc).getChanges();
							List<SourceCodeRange> oRanges = ClientMethodMarker.getChangeRanges(ClientMethodMarker.OLD, changes, lMethod);
							List<SourceCodeRange> nRanges = ClientMethodMarker.getChangeRanges(ClientMethodMarker.NEW, changes, rMethod);
							changedMethodData.add(new ChangeMethodData(lMethod, rMethod, oRanges, nRanges));
							
							// Added by Ye Wang, since 10/12/2016, 
							// Put data into changedMethods [
							changedMethods.add(new Pair<ClientMethod, ClientMethod>(lMethod, rMethod));
							// ] Ye
							
							// added by Ye Wang, 04/13/2018
//							cf.oldClientMethodToRose.put(lMethod, oName);
							
						}
					} else if (et.equals(JavaEntityType.FIELD)) {
						lField = lfmap.get(oName);
						rField = rfmap.get(nName);
						if (lField != null && rField != null) { // Ye Wang, 08/05/2017
						lField.ast = lTree;
						rField.ast = rTree;
						changedFields.add(new Pair<ClientField, ClientField>(lField, rField));
						} // Ye Wang, 08/05/2017
					} else {
						System.err.println("Need more process");
					}
				} else {	
					ChangeType ct = sc.getChangeType();
					if (et.isMethod()) {						
						switch(ct) {
						case ADDITIONAL_FUNCTIONALITY:			
							rMethod = rmap.get(entity.getUniqueName());		
							if (rMethod != null) {  // Ye Wang, 08/05/2017
							rMethod.ast = rTree;
							addedMethods.add(rMethod);
							} // Ye Wang, 08/05/2017
							
							// Added by Ye Wang, 03/23/2017
							List<TreeEditOperation> ops1 = scriptRecorder.findEditScriptByRightEntity(entity);
							if (ops1 != null) {
								cf.newMethodToScript.put(rMethod, ops1);
							}
							// End
							
							break;
						case REMOVED_FUNCTIONALITY:
							lMethod = lmap.get(entity.getUniqueName());
							if (lMethod != null) {  // Ye Wang, 08/05/2017
							lMethod.ast = lTree;
							deletedMethods.add(lMethod);
							}  // Ye Wang, 08/05/2017
							
							// Added by Ye Wang, 03/23/2017
							List<TreeEditOperation> ops2 = scriptRecorder.findEditScriptByLeftEntity(entity);
							if (ops2 != null) {
								cf.oldMethodToScript.put(lMethod, ops2);
							}
							// End
							
							break;
						default: 
							System.out.println("Need more process");
							break;
						}						
					} else if (et.isField()) {
						switch(ct) {		
						case ADDITIONAL_OBJECT_STATE:
							rField = getField(rfmap, entity.getUniqueName());
							rField.ast = rTree;
							addedFields.add(rField);
							break;
						case REMOVED_OBJECT_STATE:
							lField = getField(lfmap, entity.getUniqueName());
							lField.ast = lTree;
							deletedFields.add(lField);
							break;
						default: 
							System.out.println("Need more process");
							break;
						}
					} else if (et.isClass()) {						
						switch(ct) {
						case ADDITIONAL_CLASS:
							rClass = getClass(rcmap, entity.getUniqueName());
							if (rClass != null) { // Ye Wang 08/06/2017
							rClass.ast = rTree;
							addedClasses.add(rClass);
							}  // Ye Wang 08/06/2017
							break;
						default: 
							System.out.println("need more process");	
						}						
					}
				}
			}
			cf.changedMethods = changedMethods;
			cf.changedMethodData = changedMethodData;
			cf.insertedMethods = addedMethods;
			cf.deletedMethods = deletedMethods;
			cf.insertedFields = addedFields;
			cf.deletedFields = deletedFields;
			cf.changedFields = changedFields;
			cf.insertedClasses = addedClasses;
			cf.deletedClasses = deletedClasses;
			cf.changedClasses = changedClasses;
		}
		if (!toRemove.isEmpty()) {
			cfList.removeAll(toRemove);
		}
	}
	
	private static Map<String, ASTNode> convertToMap(List<ASTNode> trees) {
		Map<String, ASTNode> map = new HashMap<String, ASTNode>();
		for (ASTNode t : trees) {
			CompilationUnit cu = (CompilationUnit)t;
			map.put(cu.getJavaElement().getElementName(), cu);
		}
		return map;
	}
	
	private static ASTNode findTree(File f, Map<String, ASTNode> treeMap) {
		if (f == null)
			return null;
		return treeMap.get(f.getName());
	}
	
	@Override
	public String toString() {
		String leftName = left == null ? "" : left.getName();
		String rightName = right == null ? "" : right.getName();
		return leftName + "--" + rightName;
//		return left.getName() + "--" + right.getName();
	}
}
