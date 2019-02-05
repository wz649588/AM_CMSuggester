package edu.vt.cs.diffparser.tree;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import org.eclipse.jdt.core.dom.ASTNode;

import edu.vt.cs.diffparser.util.SourceCodeRange;

public class JavaImplementationNode extends GeneralNode{

	private static final long serialVersionUID = 3021150755818825401L;
	public static final String SEPARATOR = " ";
	public static final String COLON = ":";	
	
	List<SourceCodeRange> astExpressions = null;
	
	public JavaImplementationNode(int astNodeType, String value, SourceCodeRange range) {
		super(astNodeType, value, range);
	}

}
