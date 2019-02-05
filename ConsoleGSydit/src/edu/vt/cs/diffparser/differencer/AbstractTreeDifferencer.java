package edu.vt.cs.diffparser.differencer;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import edu.vt.cs.diffparser.astdiff.BestLeafTreeMatcher;
import edu.vt.cs.diffparser.astdiff.edits.Editscript;
import edu.vt.cs.diffparser.tree.GeneralNode;
import edu.vt.cs.diffparser.tree.JavaCUNode;
import edu.vt.cs.diffparser.util.Pair;

public abstract class AbstractTreeDifferencer {
	protected Set<Pair<GeneralNode, GeneralNode>> fMatch;
	protected HashMap<GeneralNode, GeneralNode> fLeftToRightMatch;
	protected HashMap<GeneralNode, GeneralNode> fRightToLeftMatch;
	protected Editscript fEditscript;
	
	public void calculateEditScript(final GeneralNode left, final GeneralNode right) {
		fMatch = new HashSet<Pair<GeneralNode, GeneralNode>>();
		BestLeafTreeMatcher matcher = new BestLeafTreeMatcher(fMatch);
		matcher.match(left, right);
		initMatch();
		computeEditScript(left, right);
	}
	
	public Editscript getEditscript() {
		return fEditscript;
	}
	
	protected void initMatch() {
		fLeftToRightMatch = new HashMap<GeneralNode, GeneralNode>();
		fRightToLeftMatch = new HashMap<GeneralNode, GeneralNode>();
		GeneralNode l = null, r = null;
		for(Pair<GeneralNode, GeneralNode> pair : fMatch) {
			l = pair.getLeft();
			r = pair.getRight();
			fLeftToRightMatch.put(l, r);
			fRightToLeftMatch.put(r, l);
		}
	}
	
	abstract protected void computeEditScript(final GeneralNode left, final GeneralNode right);
}
