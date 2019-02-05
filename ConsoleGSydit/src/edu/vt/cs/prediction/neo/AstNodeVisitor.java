package edu.vt.cs.prediction.neo;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTVisitor;

import edu.vt.cs.diffparser.util.SourceCodeRange;

public class AstNodeVisitor extends ASTVisitor {

	private ASTNode node;
	private SourceCodeRange range;
	
	@Override
	public void preVisit(ASTNode n) {
		if (node == null
				&& range.startPosition == n.getStartPosition()
				&& range.length == n.getLength()) {
			node = n;
		}
	}
	
	public ASTNode lookForNode(ASTNode root, SourceCodeRange scr) {
		node = null;
		range = scr;
		root.accept(this);
		return node;
	}
}
