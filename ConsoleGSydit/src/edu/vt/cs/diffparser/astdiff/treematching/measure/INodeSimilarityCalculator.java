package edu.vt.cs.diffparser.astdiff.treematching.measure;

import java.util.Set;

import edu.vt.cs.diffparser.tree.GeneralNode;

public interface INodeSimilarityCalculator {

	double calculateSimilarity(GeneralNode left, GeneralNode right);
}
