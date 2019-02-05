package edu.vt.cs.diffparser.tree;

import edu.vt.cs.diffparser.util.SourceCodeRange;

public class JavaFieldDeclarationNode extends JavaStructureNode {
	private static final long serialVersionUID = 1L;
	private String typeName;

	public JavaFieldDeclarationNode(int astNodeType, String typeName, String fieldName, SourceCodeRange range) {
		super(astNodeType, fieldName, range);
		this.typeName = typeName;
	}

	@Override
	public String getStrValue() {
		return typeName + "." + strValue;
	}
}
