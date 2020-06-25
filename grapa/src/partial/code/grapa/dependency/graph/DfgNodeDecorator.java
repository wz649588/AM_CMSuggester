package partial.code.grapa.dependency.graph;

import partial.code.grapa.delta.graph.GraphComparator;

import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.slicer.HeapStatement;
import com.ibm.wala.ipa.slicer.NormalStatement;
import com.ibm.wala.ipa.slicer.ParamCallee;
import com.ibm.wala.ipa.slicer.ParamCaller;
import com.ibm.wala.ipa.slicer.Statement;
import com.ibm.wala.ssa.DefUse;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SymbolTable;
import com.ibm.wala.util.WalaException;
import com.ibm.wala.viz.NodeDecorator;


public class DfgNodeDecorator implements NodeDecorator<StatementNode>{

	private IR ir;

	public DfgNodeDecorator(IR ir) {
		// TODO Auto-generated constructor stub
		this.ir = ir;
	}

	public String getLabel(StatementNode sn) throws WalaException {
		return GraphComparator.getVisualLabel(ir, sn.statement);
		// TODO Auto-generated method stub
//		Statement s = sn.statement;
//		switch (s.getKind()) {
//        case HEAP_PARAM_CALLEE:
//        case HEAP_PARAM_CALLER:
//        case HEAP_RET_CALLEE:
//        case HEAP_RET_CALLER:
//          HeapStatement h = (HeapStatement) s;
//          return s.getKind() + "\\n" + h.getNode() + "\\n" + h.getLocation();
//        case NORMAL:
//          NormalStatement n = (NormalStatement) s;
////          return n.getInstruction() + "\\n" + n.getNode().getMethod().getSignature();
////          String line = n.toString();
////          if(line.indexOf("putfield")>=0){
////        	  SymbolTable t = ir.getSymbolTable();
////        	  System.out.println();
////          }
//          return n.getInstruction().toString(ir.getSymbolTable());
//        case PARAM_CALLEE:
//          ParamCallee paramCallee = (ParamCallee) s;
//          return s.getKind() + " " + paramCallee.getValueNumber();
////          return s.getKind() + " " + paramCallee.getValueNumber() + "\\n" + s.getNode().getMethod().getName();
//        case PARAM_CALLER:
//          ParamCaller paramCaller = (ParamCaller) s;
//          return s.getKind() + " " + paramCaller.getValueNumber() + "\\n" + s.getNode().getMethod().getName() + "\\n";
////          return s.getKind() + " " + paramCaller.getValueNumber() + "\\n" + s.getNode().getMethod().getName();
//        case EXC_RET_CALLEE:
//        case EXC_RET_CALLER:
//        case NORMAL_RET_CALLEE:
//        case NORMAL_RET_CALLER:
//        case PHI:
//        default:
//          return s.toString();
//        }
	}

}
