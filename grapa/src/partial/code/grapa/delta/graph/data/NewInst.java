package partial.code.grapa.delta.graph.data;

import java.util.ArrayList;

import com.ibm.wala.classLoader.NewSiteReference;
import com.ibm.wala.ssa.SSANewInstruction;
import com.ibm.wala.types.MethodReference;
import com.ibm.wala.types.TypeReference;

public class NewInst extends AbstractNode{
	public String typeName;
	
	public NewInst(SSANewInstruction ins, int side) {
		// TODO Auto-generated constructor stub
		NewSiteReference site = ins.getNewSite();
		label = "new " + site.getDeclaredType();
		TypeReference tf = site.getDeclaredType();
		typeName = tf.getName().toString();
		this.side = side;
	}

	@Override
	public String toString() {
		// TODO Auto-generated method stub
		String line = "new "+typeName;
		return line;
	}
}
