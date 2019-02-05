package edu.vt.cs.changes;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.IBinding;
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.MethodInvocation;

import partial.code.grapa.dependency.graph.DataFlowAnalysisEngine;

public class LibAPIParser extends ASTVisitor {

	DataFlowAnalysisEngine engine = null;
	String libStr = null;
	List<IBinding> bindings = null;
	
	public LibAPIParser(DataFlowAnalysisEngine engine, String libStr) {
		this.engine = engine;
		this.libStr = libStr;		
	}
	
	public void init() {
		bindings = new ArrayList<IBinding>();
	}
	
	@Override
	public boolean visit(MethodInvocation node) {
		IMethodBinding mb = node.resolveMethodBinding();
		String typeName = mb.getDeclaringClass().getQualifiedName();
		if (typeName.contains(libStr)) {
			bindings.add(mb);
		}
		return super.visit(node);
	}
	
	public List<IBinding> getBindings() {
		return bindings;
	}
}
