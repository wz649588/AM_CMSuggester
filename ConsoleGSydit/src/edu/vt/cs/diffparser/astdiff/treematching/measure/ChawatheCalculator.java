package edu.vt.cs.diffparser.astdiff.treematching.measure;


import java.util.Set;

import edu.vt.cs.diffparser.tree.GeneralNode;
import edu.vt.cs.diffparser.util.Pair;

public class ChawatheCalculator implements INodeSimilarityCalculator {
	
	private Set<Pair<GeneralNode, GeneralNode>> leafMatches = null;
	
	public void setLeafMatches(Set<Pair<GeneralNode, GeneralNode>> match) {
		leafMatches = match;
	}
	
	
	@Override
	public double calculateSimilarity(GeneralNode left, GeneralNode right) {
		int common = 0;
		GeneralNode l = null, r = null;
		for (Pair<GeneralNode, GeneralNode> p : leafMatches) {
			l = p.getLeft();
			r = p.getRight();
			if (left.isNodeDescendant(l) && right.isNodeDescendant(r)) {
				common++;
			}			
		}
		int max = Math.max(left.getLeafCount(), right.getLeafCount());
        return (double) common / (double) max;
	}
}
