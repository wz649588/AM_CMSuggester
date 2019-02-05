package edu.vt.cs.diffparser.tree;

import java.util.Collections;
import java.util.List;

import edu.vt.cs.diffparser.util.SourceCodeRange;

/**
 * By default, the layout of fields, methods, and types declared inside the type is:
 * [field, methods, types] 
 * @author nm8247
 *
 */
public class JavaTypeDeclarationNode extends JavaStructureNode{
	private static final long serialVersionUID = 1L;

	public boolean isInterface;
	
	public String superName;
	
	public List<String> interfaces;
	
	private int fieldAnchor;
	private int methodAnchor;
	
	public JavaTypeDeclarationNode(int astNodeType, String defaultValue, SourceCodeRange range) {
		super(astNodeType, defaultValue, range);
		interfaces = Collections.emptyList();
		fieldAnchor = 0;
		methodAnchor = 0;
	}
	
	public void addField(JavaFieldDeclarationNode n) {
		this.insert(n, fieldAnchor);
		fieldAnchor++;
		methodAnchor++;
	}
	
	public void addMethod(JavaMethodDeclarationNode n) {
		this.insert(n, methodAnchor);
		methodAnchor++;
	}
	
	

}
