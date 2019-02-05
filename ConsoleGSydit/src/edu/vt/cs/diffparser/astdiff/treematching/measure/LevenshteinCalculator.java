package edu.vt.cs.diffparser.astdiff.treematching.measure;

import simpack.accessor.string.StringAccessor;
import simpack.measure.sequence.Levenshtein;

public class LevenshteinCalculator implements IStringSimilarityCalculator {
    /**
     * {@inheritDoc}
     */
    public double calculateSimilarity(String left, String right) {
        if (left.equals("") && right.equals("")) {
            return 1.0;
        }
        Levenshtein<String> lm = new Levenshtein<String>(new StringAccessor(left), new StringAccessor(right));
        return lm.getSimilarity();
    }
}
