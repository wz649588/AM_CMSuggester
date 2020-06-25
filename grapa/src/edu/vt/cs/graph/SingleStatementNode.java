package edu.vt.cs.graph;

import org.eclipse.jdt.core.dom.ASTNode;

import partial.code.grapa.delta.graph.data.AbstractNode;
import partial.code.grapa.dependency.graph.StatementNode;

public class SingleStatementNode extends ASTStatementNode {
	
	private int astNodeType;
	
	public SingleStatementNode(ASTNode n, int side) {
		this.side = side;
		this.astNodeType = n.getNodeType();
		this.label2 = n.toString().trim();
		this.label = astNodeType + "(" + n.getStartPosition() + ", " + n.getLength() + ")";
	}
}
