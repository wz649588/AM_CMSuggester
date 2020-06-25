package ca.mcgill.cs.swevo.ppa.inference;

import java.util.ArrayList;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.IBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.eclipse.jdt.core.dom.PPABindingsUtil;
import org.eclipse.jdt.core.dom.SimpleName;

public class VariableCollector extends ASTVisitor {
	private ArrayList<String> vars;
	private ArrayList<ITypeBinding> types = new ArrayList<ITypeBinding>();
	private ArrayList<SimpleName> names = new ArrayList<SimpleName>();
	
	public VariableCollector(ArrayList<String> vars) {
		// TODO Auto-generated constructor stub
		this.vars = vars;
	}

	public ArrayList<ITypeBinding> getTypes() {
		return types;
	}

	@Override
	public boolean visit(SimpleName node) {
		// TODO Auto-generated method stub
		String name = node.getFullyQualifiedName();
		
		if(vars.contains(name)){
			ITypeBinding type = node.resolveTypeBinding();	
			if (type != null) {//added by nameng: to avoid including labeled variable such as "Label: statement"
				types.add(type);
				names.add(node);
			}			
		}
		return super.visit(node);
	}

	public ArrayList<SimpleName> getNames() {
		return names;
	}
}
