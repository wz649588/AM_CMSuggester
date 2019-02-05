package edu.vt.cs.extraction;

import java.util.Comparator;

import edu.vt.cs.graph.ReferenceEdge;

/**
 * For VF2 isomorphism inspector to compare ReferenceEdge
 * @author Ye Wang
 * @since 10/26/2016
 */
class EdgeComparator implements Comparator<ReferenceEdge> {

	/**
	 * Check whether two ReferenceEdges are of the same type
	 * @param e1 first ReferenceEdge
	 * @param e2 second ReferenceEdge
	 * @return 0 if two edges are of the same type, otherwise a non-zero value 
	 */
	@Override
	public int compare(ReferenceEdge e1, ReferenceEdge e2) {
		return ((e1.type == e2.type) && (e1.dep == e2.dep)) ? 0 : 1;
	}

}
