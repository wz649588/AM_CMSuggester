package edu.vt.cs.grapa.extension;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.FieldDeclaration;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.eclipse.jdt.core.dom.VariableDeclaration;

import edu.vt.cs.graph.ClientField;

public class ClientFieldFinder extends ASTVisitor{
	
	public Map<String, ClientField> fields = new HashMap<String, ClientField>();
	private CompilationUnit cu = null;
	
	@Override
	public boolean visit(CompilationUnit cu) {
		this.cu = cu;
		return true;
	}
	
	@Override
	public boolean visit(FieldDeclaration node) {
		String typeName = node.getType().toString();
		List<VariableDeclaration> frags = node.fragments();

		for (VariableDeclaration d : frags) {
			IVariableBinding fb = d.resolveBinding();
			if (fb != null) {
				String key = fb.getDeclaringClass().getKey();
				key = key.substring(0, key.length() - 1);
				int mark = key.indexOf("~");
				if (mark > 0) {
					String shortname = key.substring(mark + 1);
					mark = key.lastIndexOf("/");
					String longname = key.substring(0, mark + 1);
					key = longname + shortname;
				}
				key = key.replaceAll("<[a-z;A-z]+>", "");
				key = key.replace(".", "$");
				
				String fieldName = d.getName().getFullyQualifiedName();
				ClientField cf = new ClientField(key, fieldName, d);
				
				StringBuffer buf = new StringBuffer(fb.getDeclaringClass().getQualifiedName()
						+ "." + d.getName().getIdentifier() + " : " + typeName);
				fields.put(buf.toString(), cf);
			}
		}
		return false;
	}
	
}
