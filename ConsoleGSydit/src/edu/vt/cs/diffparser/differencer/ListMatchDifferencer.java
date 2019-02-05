package edu.vt.cs.diffparser.differencer;

import java.util.HashMap;
import java.util.Set;

import edu.vt.cs.diffparser.tree.GeneralNode;
import edu.vt.cs.diffparser.util.Pair;

public class ListMatchDifferencer extends ListDifferencer<GeneralNode> {

	protected Set<Pair<GeneralNode, GeneralNode>> fMatch;
	protected HashMap<GeneralNode, GeneralNode> fLeftToRightMatch;
	protected HashMap<GeneralNode, GeneralNode> fRightToLeftMatch;
	
	public ListMatchDifferencer(Set<Pair<GeneralNode, GeneralNode>> match,
			HashMap<GeneralNode, GeneralNode> leftToRightMatch,
			HashMap<GeneralNode, GeneralNode> rightToLeftMatch) {
		fMatch = match;
		fLeftToRightMatch = leftToRightMatch;
		fRightToLeftMatch = rightToLeftMatch;
	}
	
	
	@Override
	protected boolean isMatched(GeneralNode left, GeneralNode right) {
		GeneralNode rMatch = fLeftToRightMatch.get(left);
		if (rMatch == null || !rMatch.equals(right))
			return false;
		return true;
	}

}
