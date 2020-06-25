package partial.code.grapa.commit;

import com.ibm.wala.ipa.slicer.SDG;

import partial.code.grapa.delta.graph.data.AbstractNode;
import partial.code.grapa.delta.graph.data.Edge;
import edu.uci.ics.jung.graph.DirectedSparseGraph;

public class DependenceGraph {
	
	public DirectedSparseGraph<AbstractNode, Edge> g = null;
	public SDG sdg = null;
	
	public DependenceGraph(
			SDG sdg,
			DirectedSparseGraph<AbstractNode, Edge> g) {
		this.sdg = sdg;
		this.g = g;
	}
}
