package edu.vt.cs.graph;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.TypeDeclaration;

import com.ibm.wala.types.TypeReference;

public class ClientClass {

	public String key;
	public String className;
	public ASTNode ast;
	public TypeReference tRef;
	public String sig;
	
	public TypeDeclaration node;
	
	public ClientClass(String key, String className, TypeDeclaration node) {
		this.key = key;
		this.className = className;
		this.node = node;
		resolveSig();
	}
	
	public void resolveSig() {
		sig = key;
	}
}
