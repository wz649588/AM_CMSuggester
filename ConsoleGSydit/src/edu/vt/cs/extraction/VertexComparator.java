package edu.vt.cs.extraction;

import java.util.Comparator;

import edu.vt.cs.graph.ReferenceNode;

/**
 * For VF2 isomorphism inspector to compare ReferenceNode
 * @author Ye Wang
 * @since 10/26/2016
 */
class VertexComparator implements Comparator<ReferenceNode> {

	/**
	 * Check whether two ReferenceNodes are of the same type
	 * @param v1 first ReferenceNode
	 * @param v2 second ReferenceNode
	 * @return 0 if two nodes are of the same type, otherwise a non-zero value
	 */
	@Override
	public int compare(ReferenceNode v1, ReferenceNode v2) {
		return v1.type - v2.type;
	}

}
