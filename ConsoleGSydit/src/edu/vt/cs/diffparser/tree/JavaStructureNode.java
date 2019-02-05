package edu.vt.cs.diffparser.tree;

import edu.vt.cs.diffparser.util.SourceCodeRange;

public class JavaStructureNode extends GeneralNode{
	private static final long serialVersionUID = -6408214092113931365L;

	public JavaStructureNode(int astNodeType, String defaultValue, SourceCodeRange range) {
		super(astNodeType, defaultValue, range);		
	}
}
