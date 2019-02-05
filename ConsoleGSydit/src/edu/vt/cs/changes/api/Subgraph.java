package edu.vt.cs.changes.api;

import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import com.ibm.wala.ipa.slicer.SDG;
import com.ibm.wala.ssa.ISSABasicBlock;

import partial.code.grapa.dependency.graph.StatementEdge;
import partial.code.grapa.dependency.graph.StatementNode;
import edu.uci.ics.jung.graph.DirectedSparseGraph;
import edu.vt.cs.graph.GraphConvertor;

public class Subgraph extends DirectedSparseGraph<SNode, SEdge>{
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	
	private Set<SNode> markedSources = null;
	private Set<SNode> markedDests = null;

	public Set<SNode> getMarkedSources() {
		return markedSources;
	}
	
	public Set<SNode> getMarkedDests() {
		return markedDests;
	}
	
	public void mark(Set<Integer> instIndexes) {
		Iterator<SEdge> iter = this.getEdges().iterator();
		SEdge e = null;
		markedSources = new HashSet<SNode>();
		markedDests = new HashSet<SNode>();
		SNode source = null;
		SNode dest = null;
		Set<SNode> markedNodes = new HashSet<SNode>();
		while (iter.hasNext()) {
			e = iter.next();
			if (instIndexes.contains(e.insn)) {
				e.enableMark();
				source = getSource(e);
				source.enableMark();
				markedNodes.add(source);
				dest = getDest(e);
				dest.enableMark();				
				markedNodes.add(dest);
			}
		}
		for (SNode sn : markedNodes) {
			Collection<SEdge> edges = this.getInEdges(sn);
			boolean containMarked = false;
			for (SEdge edge : edges) {
				if (edge.mark) {
					containMarked = true;
					break;
				}
			}
			if (!containMarked) {
				markedSources.add(sn);
			}
			containMarked = false;
			edges = this.getOutEdges(sn);
			for (SEdge edge : edges) {
				if (edge.mark) {
					containMarked = true;
					break;
				}
			}
			if (!containMarked) {
				markedSources.add(sn);
			}
		}
		
	}	
}
