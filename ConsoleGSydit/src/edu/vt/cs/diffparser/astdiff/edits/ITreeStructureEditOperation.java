package edu.vt.cs.diffparser.astdiff.edits;

import edu.vt.cs.diffparser.tree.JavaStructureNode;

public interface ITreeStructureEditOperation extends ITreeEditOperation<JavaStructureNode> {
	
	public JavaStructureNode getParentNode();
	
	public JavaStructureNode getNode();
}
