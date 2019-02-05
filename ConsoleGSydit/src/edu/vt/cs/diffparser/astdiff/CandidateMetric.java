package edu.vt.cs.diffparser.astdiff;

import edu.vt.cs.diffparser.tree.GeneralNode;
import edu.vt.cs.diffparser.util.Pair;

public class CandidateMetric extends Pair<GeneralNode, Double> implements Comparable<CandidateMetric> {

	public CandidateMetric(GeneralNode l) {
		this(l, 0.0);
	}
	
	public CandidateMetric(GeneralNode l, Double r) {
		super(l, r);
	}
	
	@Override
	public int compareTo(CandidateMetric o) {
		// TODO Auto-generated method stub
		return Double.compare(o.getRight(), this.getRight());
	}

}
