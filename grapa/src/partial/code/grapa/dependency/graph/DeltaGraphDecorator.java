package partial.code.grapa.dependency.graph;

import partial.code.grapa.delta.graph.GraphComparator;

import com.ibm.wala.ipa.slicer.HeapStatement;
import com.ibm.wala.ipa.slicer.NormalStatement;
import com.ibm.wala.ipa.slicer.ParamCallee;
import com.ibm.wala.ipa.slicer.ParamCaller;
import com.ibm.wala.ipa.slicer.Statement;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.util.WalaException;
import com.ibm.wala.viz.NodeDecorator;

public class DeltaGraphDecorator implements NodeDecorator<StatementNode>{

	private IR lir;
	private IR rir;

	public DeltaGraphDecorator(IR lir, IR rir) {
		// TODO Auto-generated constructor stub
		this.lir = lir;
		this.rir = rir;
	}

	public String getLabel(StatementNode sn) {
		// TODO Auto-generated method stub
		Statement s = sn.statement;
		
		if(sn.side == StatementNode.LEFT){
			return "l: "+GraphComparator.getVisualLabel(lir, s);
		}else if(sn.side == StatementNode.RIGHT){
			return "r: "+GraphComparator.getVisualLabel(rir, s);
		}else{
			return null;
		}
		
	}


}
