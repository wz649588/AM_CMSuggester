package edu.vt.cs.grapa.extension;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.FieldDeclaration;
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.SingleVariableDeclaration;
import org.eclipse.jdt.core.dom.TypeDeclaration;
import org.eclipse.jdt.core.dom.VariableDeclaration;

import edu.vt.cs.graph.ClientClass;
import edu.vt.cs.graph.ClientField;
import partial.code.grapa.mapping.ClientMethod;
import partial.code.grapa.mapping.ClientMethodVisitor;

public class ClientEntityFinder extends ASTVisitor{

	public Map<String, ClientMethod> methods = new HashMap<String, ClientMethod>();
	public Map<String, ClientField> fields = new HashMap<String, ClientField>();
	public Map<String, ClientClass> classes = new HashMap<String, ClientClass>();
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
	
	@Override
	public boolean visit(MethodDeclaration node) {
		// TODO Auto-generated method stub
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
					List<VariableDeclaration> params = node.parameters();
					int i = 0;				
					for (VariableDeclaration p : params) {
						SingleVariableDeclaration d = (SingleVariableDeclaration)p;	
						if (i > 0) {
							buf.append(",");							
						}			
						buf.append(d.getType().toString());
						for (Object extra : d.extraDimensions()) {
							buf.append(extra.toString());
						}
						i++;
					}
					buf.append(")");
					methods.put(buf.toString(), cm);
				}
				return super.visit(node);
	}

	public boolean visit(TypeDeclaration node) {
		ITypeBinding tb = node.resolveBinding();
		String key = tb.getKey();
		String className = key.replace('/', '.');
		className = className.replace('$', '.');
		className = className.substring(1);
		className = className.substring(0, className.length() - 1);
		classes.put(className, new ClientClass(key.substring(0, key.length() - 1), className, node));
		return super.visit(node);
	}

}
