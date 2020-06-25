package partial.code.grapa.mapping;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.SingleVariableDeclaration;
import org.eclipse.jdt.core.dom.Type;
import org.eclipse.jdt.core.dom.VariableDeclaration;

import com.ibm.wala.types.MethodReference;

import partial.code.grapa.tool.JdtUtil;



public class ClientMethod {
	public String key;
	public String methodName;
	public String sig;
	public ASTNode ast; //CompilationUnit
	public MethodReference mRef;
	
	public MethodDeclaration methodbody;
	
	public ClientMethod(String key, String methodName, String sig) {
		// TODO Auto-generated constructor stub
		this.key = key;
		this.methodName = methodName;
		this.sig = sig;
	}

	public ClientMethod(String key, String methodName, MethodDeclaration node) {
		// TODO Auto-generated constructor stub
		this.key = key;
		this.methodName = methodName;
		methodbody = node;
		resolveSig();
	}

	public String getSignature() {
		// TODO Auto-generated method stub
		String line = getTypeName();
		return line+"."+methodName+sig;
	}

	public String getTypeName() {
		// TODO Auto-generated method stub
		String line = key.substring(1);
		line = line.replaceAll("/", ".");
		return line;
	}

	public void resolveSig() {
		// TODO Auto-generated method stub
		IMethodBinding mdb = methodbody.resolveBinding();
		StringBuffer buf = new StringBuffer("(");
		int i = 0;
		if (mdb != null) {
			for (ITypeBinding tb : mdb.getParameterTypes()) {
				if (i > 0) {
					buf.append(",");							
				}						
				buf.append(tb.getName());
				i++;
			}
		} else {
			List<VariableDeclaration> params = methodbody.parameters();
			for (VariableDeclaration p : params) {
				if (i > 0)
					buf.append(",");
				IVariableBinding vb = p.resolveBinding();
				if (vb == null) {
					SingleVariableDeclaration d = (SingleVariableDeclaration)p;							
					buf.append("L" + d.getType().toString());
				} else {
					buf.append(vb.getType().getName());
				}
			}
		}				
		buf.append(")");	
		if (mdb != null) {
			buf.append(mdb.getReturnType().getName());
		} else {
			Type t = methodbody.getReturnType2();
			ITypeBinding tb = t.resolveBinding();
			if (tb == null) {
				buf.append("L" + t.toString());
			} else {
				buf.append(tb.getName());
			}
		}
		sig = buf.toString();
	}
	
	@Override
	public String toString() {
		return methodName;
	}
}
