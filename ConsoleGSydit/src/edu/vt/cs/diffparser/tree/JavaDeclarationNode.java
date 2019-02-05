package edu.vt.cs.diffparser.tree;

import edu.vt.cs.diffparser.util.SourceCodeRange;

public class JavaDeclarationNode extends GeneralNode {
	private static final long serialVersionUID = 1L;

	public JavaDeclarationNode(int astNodeType, String defaultValue, SourceCodeRange range) {
		super(astNodeType, defaultValue, range);
	}

}
