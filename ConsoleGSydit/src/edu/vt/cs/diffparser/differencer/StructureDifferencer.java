package edu.vt.cs.diffparser.differencer;

import java.util.ArrayList;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.MethodDeclaration;

import edu.vt.cs.diffparser.astdiff.BestLeafTreeMatcher;
import edu.vt.cs.diffparser.astdiff.CommonADT;
import edu.vt.cs.diffparser.astdiff.edits.AbstractTreeEditOperation;
import edu.vt.cs.diffparser.astdiff.edits.DeleteOperation;
import edu.vt.cs.diffparser.astdiff.edits.EditGroup;
import edu.vt.cs.diffparser.astdiff.edits.HighlevelEditscript;
import edu.vt.cs.diffparser.astdiff.edits.ITreeEditOperation;
import edu.vt.cs.diffparser.astdiff.edits.ITreeEditOperation.CONTENT_TYPE;
import edu.vt.cs.diffparser.astdiff.edits.InsertOperation;
import edu.vt.cs.diffparser.astdiff.edits.UpdateOperation;
import edu.vt.cs.diffparser.tree.GeneralNode;
import edu.vt.cs.diffparser.tree.JavaCUNode;
import edu.vt.cs.diffparser.tree.JavaFieldDeclarationNode;
import edu.vt.cs.diffparser.tree.JavaMethodDeclarationNode;
import edu.vt.cs.diffparser.tree.JavaTypeDeclarationNode;

public class StructureDifferencer extends AbstractTreeDifferencer{	
	private EditGroup curEditGroup;

	@Override
	protected void computeEditScript (final GeneralNode l, final GeneralNode r){
		JavaCUNode left = (JavaCUNode)l;
		JavaCUNode right = (JavaCUNode)r;
		fEditscript = new HighlevelEditscript();		
		computePackageAndImportEdits(left, right);
		compareStructures(left, right);
	}
	
	private void computePackageAndImportEdits(JavaCUNode left, JavaCUNode right) {
		comparePackageName(left.getPackageName(), right.getPackageName());	
		compareImports(left.getImports(), right.getImports());
	}
	
	private void compareImports(List<String> lImports, List<String> rImports) {
		EditGroup<String> editGroup = new EditGroup<String>(CONTENT_TYPE.IMPORT);
		fEditscript.add(editGroup);
		Set<String> set = new HashSet<String>(lImports);
		set.retainAll(rImports);
		List<String> list = new ArrayList<String>(lImports);
		list.removeAll(set);
		for (String l : list) {			
			editGroup.add(new DeleteOperation<String>(l, CONTENT_TYPE.IMPORT));
		}
		list = new ArrayList<String>(rImports);
		list.removeAll(set);
		for (String r : list) {			
			editGroup.add(new InsertOperation<String>(r, CONTENT_TYPE.IMPORT));
		}
	}
	
	private void comparePackageName(String lName, String rName) {
		if (lName == null && rName == null || lName != null && lName.equals(rName))
			return;
		if (lName == null && rName != null) {
			fEditscript.add(new InsertOperation<String>(rName, CONTENT_TYPE.PACKAGE));
		} else if (lName != null) {
			if (rName == null)
				fEditscript.add(new DeleteOperation<String>(lName, CONTENT_TYPE.PACKAGE));
			else
				fEditscript.add(new UpdateOperation<String>(lName, rName, CONTENT_TYPE.PACKAGE));
		} 
	}

	private void compareStructures(JavaCUNode left, JavaCUNode right) {		
		EditGroup<JavaTypeDeclarationNode> editGroup = new EditGroup<JavaTypeDeclarationNode>(CONTENT_TYPE.DECLARATION);	
		editGroup.setStrValue(left.getStrValue());
		Enumeration<GeneralNode> enumeration = left.children();
		GeneralNode lNode = null, rNode = null;
		// generate all delete first
		AbstractTreeEditOperation<JavaTypeDeclarationNode> edit = null;
		while(enumeration.hasMoreElements()) {
			lNode = enumeration.nextElement();
			if (!lNode.isMatched()) {
				edit = new DeleteOperation<JavaTypeDeclarationNode>((JavaTypeDeclarationNode)lNode, CONTENT_TYPE.TYPE_DECLARATION);
				editGroup.add(edit);
			}
		}
		// generate all insert then
		enumeration = right.children();
		while(enumeration.hasMoreElements()) {
			rNode = enumeration.nextElement();
			if (!rNode.isMatched()) {
				edit = new InsertOperation<JavaTypeDeclarationNode>((JavaTypeDeclarationNode)rNode, CONTENT_TYPE.TYPE_DECLARATION);
				editGroup.add(edit);
			}
		}
		// general all update finally
		enumeration = left.children();
		while (enumeration.hasMoreElements()) {
			lNode = enumeration.nextElement();
			if (lNode.isMatched()) {
				curEditGroup = new EditGroup(CONTENT_TYPE.DECLARATION);
				curEditGroup.setStrValue(lNode.getStrValue());
				rNode = fLeftToRightMatch.get(lNode);
				compare((JavaTypeDeclarationNode)lNode, (JavaTypeDeclarationNode)rNode);
				if (!curEditGroup.isEmpty()) {
					editGroup.add(curEditGroup);
				}
			}
		}
		if (!editGroup.isEmpty()) {
			fEditscript.add(editGroup);
		}
	}
	
	private void compare(JavaTypeDeclarationNode left, JavaTypeDeclarationNode right) {
		AbstractTreeEditOperation edit = null;
		// class/interface declaration of the type
		if (left.isInterface != right.isInterface) {
			if (left.isInterface) {
				edit = new UpdateOperation<String>("interface", "class", CONTENT_TYPE.TYPE_DECLARATION);
			} else {
				edit = new UpdateOperation<String>("class", "interface", CONTENT_TYPE.TYPE_DECLARATION);
			}
			curEditGroup.add(edit);
		}
		// implemented interfaces
		List<String> interfaces1 = new ArrayList<String>(left.interfaces);
		List<String> interfaces2 = new ArrayList<String>(right.interfaces);
		interfaces1.removeAll(right.interfaces);
		interfaces2.removeAll(left.interfaces);
		if (interfaces1.size() != 0 || interfaces2.size() != 0) {
			EditGroup<String> subEditGroup = new EditGroup<String>(CONTENT_TYPE.INTERFACE);
			curEditGroup.add(subEditGroup);
			for (String i : interfaces1) {
				subEditGroup.add(new DeleteOperation<String>(i));
			}
			for (String i : interfaces2) {
				subEditGroup.add(new InsertOperation<String>(i));
			}
		}
		// inherited super
		String superName1 = left.superName;
		String superName2 = right.superName;
		edit = null;
		if (superName1 == null) {
			if (superName2 != null) {
				edit = new InsertOperation<String>(superName2, CONTENT_TYPE.SUPER);
			}
		} else {
			if (superName2 == null) {
				edit = new DeleteOperation<String>(superName1, CONTENT_TYPE.SUPER);
			} else if (!superName2.equals(superName1)) {
				edit = new UpdateOperation<String>(superName1, superName2, CONTENT_TYPE.SUPER);
			}
		}
		if (edit != null) {
			curEditGroup.add(edit);
		}
	    // structure difference
		compareStructures(left, right);
	}
	
	private void compareStructures(JavaTypeDeclarationNode left, JavaTypeDeclarationNode right) {		
		GeneralNode lNode = null, rNode = null;
		AbstractTreeEditOperation edit = null;
		EditGroup<JavaFieldDeclarationNode> fieldEdits = new EditGroup<JavaFieldDeclarationNode>(CONTENT_TYPE.FIELD_DECLARATION);
		
		EditGroup<JavaMethodDeclarationNode> methodEdits = new EditGroup<JavaMethodDeclarationNode>(CONTENT_TYPE.METHOD_DECLARATION);
		
		EditGroup typeEdits = new EditGroup(CONTENT_TYPE.TYPE_DECLARATION);
		
		Enumeration<GeneralNode> enumeration = left.children();
		while(enumeration.hasMoreElements()) {
			lNode = enumeration.nextElement();
			if (lNode.isMatched())
				continue;		
			switch(lNode.getNodeType()) {
			case ASTNode.FIELD_DECLARATION:
				JavaFieldDeclarationNode lField = (JavaFieldDeclarationNode)lNode;
				edit = new DeleteOperation<JavaFieldDeclarationNode>(
						lField, 
						CONTENT_TYPE.FIELD_DECLARATION);
				edit.setParentNode(left);
				fieldEdits.add(edit);		
				break;
			case ASTNode.METHOD_DECLARATION:
				JavaMethodDeclarationNode lMethod = (JavaMethodDeclarationNode)lNode;
				edit = new DeleteOperation<JavaMethodDeclarationNode>(
						lMethod, 
						CONTENT_TYPE.METHOD_DECLARATION);
				edit.setParentNode(left);
				methodEdits.add(edit);
				break;
			case ASTNode.TYPE_DECLARATION:
				JavaTypeDeclarationNode lType = (JavaTypeDeclarationNode)lNode;
				edit = new DeleteOperation<JavaTypeDeclarationNode>(
						lType, 
						CONTENT_TYPE.TYPE_DECLARATION);
				edit.setParentNode(left);
				typeEdits.add(edit);
				break;
			}				
		}	
		enumeration = right.children();
		while(enumeration.hasMoreElements()) {
			rNode = enumeration.nextElement();
			if (rNode.isMatched()) 
				continue;
			switch(rNode.getNodeType()) {
			case ASTNode.FIELD_DECLARATION:
				JavaFieldDeclarationNode rField = (JavaFieldDeclarationNode)rNode;
				edit = new InsertOperation<JavaFieldDeclarationNode>(
						rField, 
						CONTENT_TYPE.FIELD_DECLARATION);
				edit.setParentNode(right);
				fieldEdits.add(edit);		
				break;
			case ASTNode.METHOD_DECLARATION:
				JavaMethodDeclarationNode rMethod = (JavaMethodDeclarationNode)rNode;
				edit = new InsertOperation<JavaMethodDeclarationNode>(
						rMethod, 
						CONTENT_TYPE.METHOD_DECLARATION);
				edit.setParentNode(right);
				methodEdits.add(edit);
				break;
			case ASTNode.TYPE_DECLARATION:
				JavaTypeDeclarationNode rType = (JavaTypeDeclarationNode)rNode;
				edit = new InsertOperation<JavaTypeDeclarationNode>(
						rType, 
						CONTENT_TYPE.TYPE_DECLARATION);
				edit.setParentNode(right);
				typeEdits.add(edit);
				break;
			}				
		}	
		enumeration = left.children();
		while (enumeration.hasMoreElements()) {
			lNode = enumeration.nextElement();
			if (lNode.isMatched()) {
				rNode = fLeftToRightMatch.get(lNode);
			} else {
				continue;
			}
			switch(lNode.getNodeType()) {
			case ASTNode.FIELD_DECLARATION:
				if (lNode.getStrValue().equals(rNode.getStrValue())) {
					continue;
				}
				edit = new UpdateOperation<JavaFieldDeclarationNode>(
						(JavaFieldDeclarationNode)lNode,
						(JavaFieldDeclarationNode)rNode, 
						CONTENT_TYPE.FIELD_DECLARATION);
				edit.setParentNode(left);
				fieldEdits.add(edit);	
				break;
			case ASTNode.METHOD_DECLARATION:
				JavaMethodDeclarationNode lMethod = (JavaMethodDeclarationNode)lNode;
				JavaMethodDeclarationNode rMethod = (JavaMethodDeclarationNode)rNode;
				if (!lMethod.getStrValue().equals(rMethod.getStrValue()) ||
						lMethod.getContentHashcode() != rMethod.getContentHashcode()) {
					edit = new UpdateOperation<JavaMethodDeclarationNode>(
							lMethod, 
							rMethod, 
							CONTENT_TYPE.METHOD_DECLARATION);
					edit.setParentNode(left);
					methodEdits.add(edit);
				}
				break;
			case ASTNode.TYPE_DECLARATION:
				JavaTypeDeclarationNode lType = (JavaTypeDeclarationNode)lNode;
				JavaTypeDeclarationNode rType = (JavaTypeDeclarationNode)rNode;
				EditGroup curBackup = curEditGroup;
				curEditGroup = new EditGroup(CONTENT_TYPE.DECLARATION);					
				compare(lType, rType);
				if (!curEditGroup.isEmpty()) {
					typeEdits.add(curEditGroup);				
					curEditGroup.setStrValue(lNode.getStrValue());
				}
				curEditGroup = curBackup;
				break;
			}
		}
		
		if (!fieldEdits.isEmpty())
			curEditGroup.add(fieldEdits);
		if (!methodEdits.isEmpty())			
			curEditGroup.add(methodEdits);
		if (!typeEdits.isEmpty())
			curEditGroup.add(typeEdits);	
	}
}
