package partial.code.grapa.delta.graph.data;

import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.SSAPutInstruction;
import com.ibm.wala.types.FieldReference;

public class PutInst extends AbstractNode {
	public boolean bStatic;
	public String name;
	public String typeName;
	public String value;
	
	public PutInst(SSAPutInstruction ins, IR ir, int side) {
		// TODO Auto-generated constructor stub
		label = "";
		if (ins.isStatic()) {
			bStatic = true;
		    label = "putstatic ";
		} else {
		    label =  "putfield ";
		    bStatic = false;
		}
		label += ins.getDeclaredField() + "=" + ins.getValueString(ir.getSymbolTable(), ins.getVal());
		FieldReference df = ins.getDeclaredField();
		name = df.getName().toString();
		typeName = df.getDeclaringClass().getName().toString();
		value = ins.getValueString(ir.getSymbolTable(), ins.getVal());
		this.side = side;
	}
	
	@Override
	public String toString() {
		// TODO Auto-generated method stub
		String line = "";
		if (bStatic) {
			line = "putstatic ";
		} else {
			line = "putfield ";
		}
		line += " "+typeName+"."+name;
		return line;
	}
}
