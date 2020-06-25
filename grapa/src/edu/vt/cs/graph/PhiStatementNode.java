package edu.vt.cs.graph;

import com.ibm.wala.ipa.slicer.PhiStatement;

import partial.code.grapa.dependency.graph.StatementNode;

public class PhiStatementNode extends ASTStatementNode{

	// This is for phi statement
	public PhiStatementNode(StatementNode sn) {
		this.side = sn.side;		
		this.label = ((PhiStatement)sn.statement).getPhi().toString();
		this.label2 = label;
	}
}
