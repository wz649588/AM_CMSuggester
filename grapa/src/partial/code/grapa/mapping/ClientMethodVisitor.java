package partial.code.grapa.mapping;

import java.lang.reflect.Modifier;
import java.util.ArrayList;

import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.MethodDeclaration;


public class ClientMethodVisitor extends ASTVisitor {

	public ArrayList<ClientMethod> methods = new ArrayList<ClientMethod>();
	private CompilationUnit cu = null;
	
	@Override
	public boolean visit(CompilationUnit cu) {
		this.cu = cu;
		return true;
	}
	
	public static String getTypeKey(ITypeBinding tb) {
		String key = tb.getKey();
		key = key.replaceAll("<>", "");
		return key;
	}
	
	public static String getTypeKey(IMethodBinding mdb) {
		String key = null;
		if(mdb!=null/*&&!Modifier.isAbstract(mdb.getModifiers())--removed by nameng*/&&!Modifier.isInterface(mdb.getModifiers())&&!mdb.getDeclaringClass().isAnonymous()){
			key = mdb.getDeclaringClass().getKey();
			key = key.substring(0, key.length()-1);
			int mark = key.indexOf("~");
			if(mark>0){
				String shortname = key.substring(mark+1);
				mark = key.lastIndexOf("/");
				String longname = key.substring(0, mark+1);
				key = longname+shortname;					
			}
			key = key.replaceAll("<[a-z;A-z]+>", "");
			key = key.replace(".", "$");
		}
		return key;
	}
	
	public static String getName(IMethodBinding mdb) {
		String methodName;
		if(mdb.isConstructor()){
			methodName = "<init>";
		}else{
			methodName = mdb.getName();
		}
		return methodName;
	}
	
	@Override
	public boolean visit(MethodDeclaration node) {		
		IMethodBinding mdb = node.resolveBinding();
		String key = getTypeKey(mdb);
		String methodName = getName(mdb);		
		ClientMethod cm = new ClientMethod(key, methodName, node);
		cm.ast = cu;// added by nameng to add compilationUnit info to each clientMethod
		cm.methodbody = node;
		methods.add(cm);
		return super.visit(node);
	}

	public void clear() {
		// TODO Auto-generated method stub
		this.methods.clear();
	}

}
