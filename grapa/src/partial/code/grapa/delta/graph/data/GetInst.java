package partial.code.grapa.delta.graph.data;

import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.SSAGetInstruction;
import com.ibm.wala.types.FieldReference;

public class GetInst extends AbstractNode {
	
	public boolean bStatic;
	public String name;
	public String typeName;
	public String value;
	
	public GetInst(SSAGetInstruction ins, IR ir, int side) {
		// TODO Auto-generated constructor stub
		label = "";
		if (ins.isStatic()) {
			bStatic = true;
		    label = "getstatic ";
		} else {
		    label = "getfield ";
		    bStatic = false;
		}
		label += ins.getDeclaredField() + "=" + ins.getValueString(ir.getSymbolTable(), ins.getRef());
		FieldReference df = ins.getDeclaredField();
		name = df.getName().toString();
		typeName = df.getDeclaringClass().getName().toString();
		value = ins.getValueString(ir.getSymbolTable(), ins.getRef());
		this.side = side;
	}

	@Override
	public String toString() {
		// TODO Auto-generated method stub
		String line = "";
		if (bStatic) {
			line = "getstatic ";
		} else {
			line = "getfield ";
		}
		line += " "+typeName+"."+name;
		return line;
	}
}
