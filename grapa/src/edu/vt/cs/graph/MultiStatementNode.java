package edu.vt.cs.graph;

import java.util.List;

import org.eclipse.jdt.core.dom.ASTNode;

import partial.code.grapa.delta.graph.data.AbstractNode;

public class MultiStatementNode extends AbstractNode{

	public MultiStatementNode(List<ASTNode> stmts, int side) {
		this.side = side;
		this.label2 = stmts.get(0).toString();
		ASTNode stmt1 = stmts.get(0);
		ASTNode stmt2 = stmts.get(stmts.size() - 1);
		this.label = stmt1.getNodeType() + "(" + stmt1.getStartPosition() + ", " + stmt1.getLength() + ")" 
				+ "-" + stmt2.getNodeType() + "(" + stmt2.getStartPosition() + ", " + stmt2.getLength() + ")";		
	}
	
}
