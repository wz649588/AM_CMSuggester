package org.eclipse.jdt.core.dom;

import java.util.Hashtable;

import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.internal.compiler.lookup.PPATypeBindingOptions;

import ca.mcgill.cs.swevo.ppa.PPAASTUtil;

public class ImportVisitor extends ASTVisitor {
	public Hashtable<String, ITypeBinding> typeTable = new Hashtable<String, ITypeBinding>();
	private PPATypeRegistry typeRegistry;
	private PPADefaultBindingResolver resolver;
	private PPATypeBindingOptions options;
	
	@Override
	public boolean visit(TypeDeclaration node) {
		// TODO Auto-generated method stub
		ITypeBinding nodeB = node.resolveBinding();
		if(typeTable.get("thisType")==null){
			typeTable.put("thisType", nodeB);
		}
		return super.visit(node);
	}

	public ImportVisitor(PPATypeRegistry typeRegistry,
			PPADefaultBindingResolver resolver,
			PPATypeBindingOptions options) {
		// TODO Auto-generated constructor stub
		this.typeRegistry = typeRegistry;
		this.resolver = resolver;
		this.options = options;
	}

	@Override
	public boolean visit(ImportDeclaration node) {
		// TODO Auto-generated method stub
		Name name = node.getName();
		String fullname = name.toString();
		int mark = fullname.lastIndexOf(".");
		String shortname = fullname.substring(mark+1);
		if(shortname.compareTo("*")!=0){
			ITypeBinding nameB = name.resolveTypeBinding();
			if(nameB == null){
				ITypeBinding typeB = typeRegistry.createTypeBinding(shortname, fullname, resolver, null, options);
				typeTable.put(shortname, typeB);
			}else{
				CompilationUnit cu =(CompilationUnit) PPAASTUtil.getSpecificParentType(
						name, ASTNode.COMPILATION_UNIT);
				ITypeBinding typeB = typeRegistry.createTypeBinding(shortname, fullname, resolver, cu, options);
				typeTable.put(shortname, typeB);
			}
		}
		return super.visit(node);
	}

}
