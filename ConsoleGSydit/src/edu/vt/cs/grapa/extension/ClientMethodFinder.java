package edu.vt.cs.grapa.extension;

import java.lang.reflect.Modifier;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.SingleVariableDeclaration;
import org.eclipse.jdt.core.dom.TypeDeclaration;
import org.eclipse.jdt.core.dom.VariableDeclaration;

import partial.code.grapa.mapping.ClientMethod;
import partial.code.grapa.mapping.ClientMethodVisitor;


/**
 * Define ClientMethodFinder based on JavaStructureTreeBuilder
 * The result Map<String, ClientMethod> connects results of ChangeDistiller and Grapa
 * @author nm8247
 *
 */
public class ClientMethodFinder extends ASTVisitor {

	public Map<String, ClientMethod> methods = new HashMap<String, ClientMethod>();
	
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
	
	public void clear() {
		// TODO Auto-generated method stub
		this.methods.clear();
	}
}
