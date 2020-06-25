package partial.code.grapa.version.detect;

import java.util.ArrayList;

import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.IBinding;
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.eclipse.jdt.core.dom.ImportDeclaration;
import org.eclipse.jdt.core.dom.MethodInvocation;
import org.eclipse.jdt.core.dom.Name;
import org.eclipse.jdt.core.dom.PackageDeclaration;
import org.eclipse.jdt.core.dom.QualifiedName;
import org.eclipse.jdt.core.dom.SimpleName;
import org.eclipse.jdt.core.dom.SuperMethodInvocation;

public class CodeElementVisitor extends ASTVisitor {
	public ArrayList<String> typeElements = new ArrayList<String>();
	public ArrayList<String> shortTypes = new ArrayList<String>();
	
	public ArrayList<String> methodElements = new ArrayList<String>();
	public ArrayList<String> shortMethods = new ArrayList<String>();
	
	public ArrayList<String> fieldElements = new ArrayList<String>();
	public ArrayList<String> shortFields = new ArrayList<String>();
	private String pName;
	public boolean bUnit = false;
	
	public CodeElementVisitor(String pName) {
		// TODO Auto-generated constructor stub
		this.pName = pName;
	} 
	
	public CodeElementVisitor() {
		
	}

	@Override
	public boolean visit(PackageDeclaration node) {
		// TODO Auto-generated method stub
		String name = node.getName().toString();
		if(name.indexOf("test")>0||name.indexOf("Test")>0){
			bUnit = true;
		}
		return super.visit(node);
	}

	@Override
	public boolean visit(ImportDeclaration node) {
		// TODO Auto-generated method stub
		Name name = node.getName();
		String fullname = name.toString();
		if(fullname.indexOf("junit")>=0){
			bUnit = true;
		}
		if(isValidName(this.typeElements, fullname)){
			typeElements.add(fullname);
		}
		return super.visit(node);
	}
	
	@Override
	public boolean visit(MethodInvocation node) {
		// TODO Auto-generated method stub
		IMethodBinding nodeB = node.resolveMethodBinding();
		if(nodeB!=null&&nodeB.getDeclaringClass()!=null){
			String name = nodeB.getDeclaringClass().getQualifiedName();				
			if(isValidName(this.typeElements, name)){
				typeElements.add(name);
			}else{
				shortTypes.add(getValidShortName(name));
			}
			name = nodeB.getDeclaringClass().getQualifiedName()+"."+nodeB.getName();
			if(isValidName(this.methodElements, name)){
				methodElements.add(name);
			}else{
				shortMethods.add(node.getName().getIdentifier());
			}
		}else{
			shortMethods.add(node.getName().getIdentifier());
		}
		
		return super.visit(node);
	}
	
	@Override
	public boolean visit(SuperMethodInvocation node) {//added by nameng
		IMethodBinding nodeB = node.resolveMethodBinding();
		if(nodeB!=null&&nodeB.getDeclaringClass()!=null){
			String name = nodeB.getDeclaringClass().getQualifiedName();				
			if(isValidName(this.typeElements, name)){
				typeElements.add(name);
			}else{
				shortTypes.add(getValidShortName(name));
			}
			name = nodeB.getDeclaringClass().getQualifiedName()+"."+nodeB.getName();
			if(isValidName(this.methodElements, name)){
				methodElements.add(name);
			}else{
				shortMethods.add(node.getName().getIdentifier());
			}
		}else{
			shortMethods.add(node.getName().getIdentifier());
		}
		return super.visit(node);
	}

	private String getValidShortName(String name) {
		// TODO Auto-generated method stub
		int mark = name.indexOf("UNKNOWN");
		if(mark>0){
			name = name.substring(mark+9);
		}
		mark = name.indexOf("UNKNOWNP");
		if(mark>0){
			name = name.substring(mark+9);
		}
		mark = name.indexOf("<");
		if(mark>0){
			name = name.substring(mark+1, name.length()-1);
		}
		mark = name.indexOf(">");
		if(mark>0){
			name = name.substring(0, mark);
		}
		name = name.replace(".", "$");
		return name;
	}

	@Override
	public boolean visit(QualifiedName node) {
		// TODO Auto-generated method stub
		analyzeName(node);
		return super.visit(node);
	}

	@Override
	public boolean visit(SimpleName node) {
		// TODO Auto-generated method stub

		analyzeName(node);
		return super.visit(node);
	}

	private void analyzeName(Name node) {
		try{
			IBinding nodeB = node.resolveBinding();
			if(nodeB instanceof ITypeBinding){
				ITypeBinding typeB = (ITypeBinding)nodeB;
				String name = typeB.getQualifiedName();
				if(isValidName(this.typeElements, name)){
					typeElements.add(name);
				}else{
					shortTypes.add(getValidShortName(name));
				}
			}else if(nodeB instanceof IVariableBinding){
				IVariableBinding varB = (IVariableBinding)nodeB;
				if(varB.getDeclaringClass()!=null){
					String name = varB.getDeclaringClass().getQualifiedName();				
					if(isValidName(this.typeElements, name)){
						typeElements.add(name);
					}else{
						shortTypes.add(getValidShortName(name));
					}
					name = varB.getDeclaringClass().getQualifiedName()+"."+varB.getName();
					if(isValidName(this.fieldElements, name)){
						fieldElements.add(name);
					}else{
						shortFields.add(node.getFullyQualifiedName());
					}
				}else{
					shortFields.add(node.getFullyQualifiedName());
				}
			}
		}catch(Exception e){
			System.out.println("Error in sName.resolveBinding();");
			exdist.ExceptionHandler.process(e, "Error in sName.resolveBinding();");
		}
	}

	private boolean isValidName(ArrayList<String> list, String name) {
		return !list.contains(name)&&name.indexOf("<")<0&&name.indexOf("UNKOWN")<0;
	}
}
