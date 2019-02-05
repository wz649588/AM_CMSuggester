package edu.vt.cs.diffparser.util;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTVisitor;

public class ASTAnonymousClassDeclarationFinder extends ASTVisitor {

	private List<ASTNode> result = null;

	public List<ASTNode> findACD(ASTNode node) {
		result = null;
		node.accept(this);
		return result;
	}

	@Override
	public void preVisit(ASTNode node) {
		if (node.getNodeType() == ASTNode.ANONYMOUS_CLASS_DECLARATION) {
			if (result == null) {
				result = new ArrayList<ASTNode>();
			}
			result.add(node);
		}
	}
}
