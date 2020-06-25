package edu.vt.cs.graph;

import partial.code.grapa.delta.graph.data.AbstractNode;

public abstract class ASTStatementNode extends AbstractNode {
	// added by nameng
	public enum NodeType {
		SINGLE,
		MULTI
	}
	protected NodeType t;
	
}
