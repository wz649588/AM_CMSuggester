package edu.vt.cs.diffparser.tree;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.SingleVariableDeclaration;

import edu.vt.cs.diffparser.util.Pair;
import edu.vt.cs.diffparser.util.SourceCodeRange;

public class JavaMethodHeaderNode extends JavaImplementationNode{

	private static final long serialVersionUID = 1507380196920774318L;
	private MethodDeclaration md;
	private List<Pair<String, String>> parameterList;

	public JavaMethodHeaderNode(int astNodeType, String value, SourceCodeRange range,
			List parameters) {
		super(astNodeType, value, range);
		parameterList = new ArrayList<Pair<String, String>>();
		SingleVariableDeclaration n = null;
		for (int i = 0; i < parameters.size(); i++) {
			n = (SingleVariableDeclaration) parameters.get(i);
			parameterList.add(new Pair<String, String>(n.getType().toString(), n.getName().getIdentifier()));
		}
	}
	
	public List<Pair<String, String>> getParameterList() {
		return parameterList;
	}
	
	public MethodDeclaration getMethodDeclaration() {
		return md;
	}
	
	public void setMethodDeclaration(MethodDeclaration md) {
		this.md = md;
	}
}
