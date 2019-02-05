package edu.vt.cs.grapa.extension;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.FieldDeclaration;
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.TypeDeclaration;
import org.eclipse.jdt.core.dom.VariableDeclaration;

import partial.code.grapa.mapping.ClientMethod;
import partial.code.grapa.mapping.ClientMethodVisitor;
import edu.vt.cs.graph.ClientClass;
import edu.vt.cs.graph.ClientField;

/**
 * Find the mapping between a class and contained methods and fields
 * @author Ye Wang
 * @since 03/08/2018
 *
 */
public class ClientContainingMapper extends ASTVisitor {
	
	public Map<ClientClass, List<ClientMethod>> classToMethodList = new HashMap<>();
	
	public Map<ClientClass, List<ClientField>> classToFieldList = new HashMap<>();

	@Override
	public boolean visit(TypeDeclaration node) {
		ITypeBinding tb = node.resolveBinding();
		String key = tb.getKey();
		String className = key.replace('/', '.');
		className = className.replace('$', '.');
		className = className.substring(1);
		className = className.substring(0, className.length() - 1);
		
		ClientClass cc = new ClientClass(key.substring(0, key.length() - 1), className, node);
		
		MethodAndFieldVisitor visitor = new MethodAndFieldVisitor();
		node.accept(visitor);
		classToMethodList.put(cc, visitor.methodList);
		classToFieldList.put(cc, visitor.fieldList);
		return false; // don't visit its children
	}
}

/**
 * Helper class for ClientContainingMapper
 * @author Ye Wang
 * @since 03/08/2018
 *
 */
class MethodAndFieldVisitor extends ASTVisitor {
	
	List<ClientMethod> methodList = new ArrayList<>();
	List<ClientField> fieldList = new ArrayList<>();
	
	@Override
	public boolean visit(FieldDeclaration node) {
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
				fieldList.add(cf);
			}
		}
		return false;
	}
	
	@Override
	public boolean visit(MethodDeclaration node) {
		IMethodBinding mdb = node.resolveBinding();
		String key = ClientMethodVisitor.getTypeKey(mdb);
		if (key != null) {
			String methodName = ClientMethodVisitor.getName(mdb);
			
			ClientMethod cm = new ClientMethod(key, methodName, node);				
			String qualifiedClassName = key.substring(1);
			qualifiedClassName = qualifiedClassName.replaceAll("/", ".");
			qualifiedClassName = qualifiedClassName.replaceAll("\\$", ".");
			StringBuffer buf = new StringBuffer(qualifiedClassName
					+ "." + node.getName().getIdentifier());
			buf.append("(");
			methodList.add(cm);
		}
		return false;
	}
}
