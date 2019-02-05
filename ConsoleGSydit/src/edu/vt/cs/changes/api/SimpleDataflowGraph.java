package edu.vt.cs.changes.api;

import com.ibm.wala.ipa.slicer.PDG;
import com.ibm.wala.ipa.slicer.SDG;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.ISSABasicBlock;
import com.ibm.wala.ssa.SSAInstruction;

import edu.uci.ics.jung.graph.DirectedSparseGraph;

public class SimpleDataflowGraph extends DirectedSparseGraph<SNode, SEdge>{

	public SimpleDataflowGraph(SDG g) {
		
	}
	
	public SimpleDataflowGraph(SDG g, IR ir, int firstIndex, int lastIndex) {
		SSAInstruction[] insts = ir.getInstructions();
		for (int i = firstIndex; i <= lastIndex; i++) {			
		}
	}
}
