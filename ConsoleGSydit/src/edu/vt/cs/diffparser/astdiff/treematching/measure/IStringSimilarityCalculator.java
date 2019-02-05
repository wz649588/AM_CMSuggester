package edu.vt.cs.diffparser.astdiff.treematching.measure;

public interface IStringSimilarityCalculator {

	double calculateSimilarity(String left, String right);
}
