package edu.vt.cs.diffparser.astdiff;

import edu.vt.cs.diffparser.tree.GeneralNode;
import edu.vt.cs.diffparser.util.Pair;

public class InnerPair extends Pair<GeneralNode, GeneralNode> implements Comparable<InnerPair>{

	public InnerPair(GeneralNode l, GeneralNode r) {
		super(l, r);
		// TODO Auto-generated constructor stub
	}

	@Override
	public int compareTo(InnerPair o) {
		// TODO Auto-generated method stub
		return 0;
	}

}
