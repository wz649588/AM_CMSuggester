package partial.code.grapa.delta.graph.data;

import java.util.ArrayList;

import com.ibm.wala.cast.java.ssa.AstJavaInvokeInstruction;
import com.ibm.wala.classLoader.CallSiteReference;
import com.ibm.wala.shrikeBT.IInvokeInstruction;
import com.ibm.wala.types.MethodReference;
import com.ibm.wala.types.TypeName;
import com.ibm.wala.types.TypeReference;

public class MethodInvoc extends AbstractNode{
	public boolean bStatic;
	public String name;
	public ArrayList<String> paras = new ArrayList<String>();
	public String sig;
	public String typeName;
	
	public MethodInvoc(AstJavaInvokeInstruction ins, int side) {
		// TODO Auto-generated constructor stub
		CallSiteReference site = ins.getCallSite();
		label = "invoke "+site.getInvocationString() + " "+ site.getDeclaredTarget().toString();
		if(site.getInvocationCode()==IInvokeInstruction.Dispatch.STATIC){
			bStatic = true;
		}else{
			bStatic = false;
		}
		MethodReference mf = site.getDeclaredTarget();
		name = mf.getName().toString();
		sig = mf.getSignature();
		typeName = mf.getDeclaringClass().getName().toString();
		for(int i=0; i<mf.getNumberOfParameters(); i++){
			TypeReference p = mf.getParameterType(i);			
			paras.add(p.getName().toString());
		}
		this.side = side;
	}

	@Override
	public String toString() {
		// TODO Auto-generated method stub
		String line = "invoke ";
		if (bStatic) {
			line = "invokestatic ";
		} else {
			line = "invoke ";
		}		
		line += sig;
		return line;
	}
}
