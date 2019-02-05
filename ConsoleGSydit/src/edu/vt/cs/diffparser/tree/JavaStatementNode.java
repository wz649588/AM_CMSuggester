package edu.vt.cs.diffparser.tree;

import java.util.ArrayList;
import java.util.Collections;

import org.eclipse.jdt.core.dom.ASTNode;

import edu.vt.cs.diffparser.util.SourceCodeRange;

public class JavaStatementNode extends JavaImplementationNode{

	private static final long serialVersionUID = 6916186311954837315L;

	public JavaStatementNode(int astNodeType, String value, SourceCodeRange range,
			ASTNode[] expressions) {
		super(astNodeType, value, range);
		
		if (expressions != null) {			
			astExpressions = new ArrayList<SourceCodeRange>();
			StringBuffer buffer = new StringBuffer(value + COLON);
			for (ASTNode n : expressions) {
				astExpressions.add(new SourceCodeRange(n.getStartPosition(), n.getLength()));
				buffer.append(n.toString()).append(SEPARATOR);
			}
			astExpressions = Collections.unmodifiableList(astExpressions);
			this.strValue = buffer.toString();
		}
	}

}
