package edu.vt.cs.diffparser.tree;

import java.util.ArrayList;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Stack;

import org.eclipse.jdt.core.dom.CompilationUnit;

import edu.vt.cs.diffparser.util.SourceCodeRange;

public class JavaCUNode extends JavaStructureNode{

	private static final long serialVersionUID = 1L;

	private CompilationUnit cu;
	
	private List<String> imports;
	
	private String packageName;
	
	public JavaCUNode(int astNodeType, String defaultValue, SourceCodeRange range, CompilationUnit cu) {
		super(astNodeType, defaultValue, range);
		this.cu = cu;
		imports = new ArrayList<String>();
	}

	public String getPackageName() {
		return packageName;
	}
	
	public void setPackageName(String s) {
		packageName = s;
	}
	
	public void addImport(String s) {
		imports.add(s);
	}
	
	public List<String> getImports() {
		return imports;
	}
	
	public CompilationUnit getCU() {
		return cu;
	}
	
	@Override
	public Object clone() {
		Object obj = super.clone();
		JavaCUNode cuNode = (JavaCUNode)obj;
		cuNode.imports = new ArrayList<String>(this.imports);
		cuNode.packageName = this.packageName;
		return obj;
	}
}
