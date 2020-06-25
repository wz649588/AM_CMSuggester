package edu.vt.cs.graph;

import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.FieldDeclaration;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.eclipse.jdt.core.dom.VariableDeclaration;

import com.ibm.wala.types.FieldReference;

public class ClientField {

	public String key;
	public String fieldName;
	public ASTNode ast;
	public FieldReference fRef;
	public String sig;
	
	public VariableDeclaration field;
	
	public ClientField(String key, String fieldName, VariableDeclaration node) {
		this.key = key;
		this.fieldName = fieldName;
		this.field = node;
		resolveSig();
	}

	public void resolveSig() {
		IVariableBinding fb = field.resolveBinding();
		String key = fb.getKey();
		sig = key.substring(key.indexOf(")") + 1);
		if (sig != null && sig.endsWith(";")) {
			sig = sig.substring(0, sig.length() - 1);
		}
	}
	
	// added by Ye Wang, 02/25/2018
	@Override
	public String toString() {
		return fieldName;
	}
}
