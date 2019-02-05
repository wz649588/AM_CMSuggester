package edu.vt.cs.prediction.neo;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.Block;
import org.eclipse.jdt.core.dom.StructuralPropertyDescriptor;

/**
 * This class compares two AST to 
 * 
 * This class will not be used. Delete it later.
 * 
 * @author Ye Wang
 * @since 06/02/2017
 *
 */
public class AstComparer {
	private ASTNode oldRoot;
	private ASTNode newRoot;
	
	private ASTNode oldBody;
	private ASTNode newBody;
	
	public AstComparer(ASTNode oldRoot, ASTNode newRoot) {
		this.oldRoot = oldRoot;
		this.newRoot = newRoot;
	}
	
	public void checkFieldReplacement() {
		List<ASTNode> oldChildren = getChildren(oldRoot);
		List<ASTNode> newChildren = getChildren(newRoot);
	}
	
	@SuppressWarnings({ "unchecked", "rawtypes" })
	public static List<ASTNode> getChildren(ASTNode root) {
		List<ASTNode> children = new ArrayList<>();
		List list = root.structuralPropertiesForType();
		for (int i = 0; i < list.size(); i++) {
			Object child = root.getStructuralProperty((StructuralPropertyDescriptor) list.get(i));
			if (child instanceof ASTNode)
				children.add((ASTNode) child);
			if (child instanceof List)
				children.addAll((List) child);
		}
		return children;
	}
	
	private static ASTNode getMethodBody(ASTNode methodDeclaration) {
		List<ASTNode> children = getChildren(methodDeclaration);
		for (ASTNode n: children) {
			if (n instanceof Block) {
				return n;
			}
		}
		return null;
	}
}
