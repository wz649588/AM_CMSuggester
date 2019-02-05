package edu.vt.cs.diffparser.astdiff;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Enumeration;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.eclipse.jdt.core.dom.ASTNode;

import edu.vt.cs.diffparser.astdiff.treematching.measure.ChawatheCalculator;
import edu.vt.cs.diffparser.astdiff.treematching.measure.NGramsCalculator;
import edu.vt.cs.diffparser.tree.GeneralNode;
import edu.vt.cs.diffparser.util.Pair;

public class BestLeafTreeMatcher {
	private static NGramsCalculator STRING_SIM_CALC = new NGramsCalculator();
	private static final int N = 2;
	
	private static ChawatheCalculator STRUCT_SIM_CALC = new ChawatheCalculator();
	private static final double STRUCT_SIM_THRES;
	
	private static final int DYNAMIC_DEPTH = 4;
	private static final double DYNAMIC_THRES = 0.4;
	private static final double STRUCT_WEIGHT_THRES = 0.8; 
	private static final double STRING_WEIGHT_THRES = 0.8;
	
	private static final List<Integer> INCOMP_TYPES = Arrays.asList(new Integer[]{
			ASTNode.FIELD_DECLARATION,
			ASTNode.METHOD_DECLARATION,
			ASTNode.TYPE_DECLARATION,
			ASTNode.CATCH_CLAUSE,
			ASTNode.IF_STATEMENT,
			ASTNode.SWITCH_CASE,
			ASTNode.SWITCH_STATEMENT,
			ASTNode.SYNCHRONIZED_STATEMENT,
			ASTNode.THROW_STATEMENT,
			ASTNode.TRY_STATEMENT,
			ASTNode.WHILE_STATEMENT,
	});
	
	static {
		((NGramsCalculator)STRING_SIM_CALC).setN(N);		
		STRUCT_SIM_THRES = 0.6;
	}
	
	private Set<Pair<GeneralNode, GeneralNode>> fMatch;
	
	private List<GeneralNode> leftLeaves = null;
	private List<GeneralNode> rightLeaves = null;
	
	private List<GeneralNode> leftInners = null;
	private List<GeneralNode> rightInners = null;
	
	public BestLeafTreeMatcher(Set<Pair<GeneralNode, GeneralNode>> match) {
		fMatch = match;
	}
	
	public void match(GeneralNode left, GeneralNode right) {
		leftLeaves = new ArrayList<GeneralNode>();
		rightLeaves = new ArrayList<GeneralNode>();
		
		leftInners = new ArrayList<GeneralNode>();
		rightInners = new ArrayList<GeneralNode>();
		
		Enumeration<GeneralNode> nodes = left.postorderEnumeration();
		GeneralNode tmp = null;
		while(nodes.hasMoreElements()) {
			tmp = nodes.nextElement();
			if (tmp.isLeaf()) {
				leftLeaves.add(tmp);
			} else {
				leftInners.add(tmp);
			}
		}
		
		nodes = right.postorderEnumeration();
		while (nodes.hasMoreElements()) {
			tmp = nodes.nextElement();
			if (tmp.isLeaf()) {
				rightLeaves.add(tmp);
			} else {
				rightInners.add(tmp);
			}
		}
		leftInners.remove(leftInners.size() - 1); //remove the compilationUnit node
 		rightInners.remove(rightInners.size() - 1); // remove the compilationUnit node 		
 		addMatch(left, right);
 		
		matchLeaves();
		
		matchInnerNodes();
		
		matchInnerAndLeaf();
	}
	
	private void addMatch(GeneralNode l, GeneralNode r) {
		fMatch.add(new Pair<GeneralNode, GeneralNode>(l, r));
		l.setMatched();
		r.setMatched();
	}
	
	private void addMatch(GeneralNode l, GeneralNode r, List<GeneralNode> rNodes, Set<GeneralNode> lNodesToRemove) {
		addMatch(l, r);
		rNodes.remove(r);
		lNodesToRemove.add(l);
	}
	
	private void addMatch(GeneralNode l, GeneralNode r, List<GeneralNode> rNodes, 
			Set<GeneralNode> lNodesToRemove, List<CandidateMetric> candidates) {
		addMatch(l, r, rNodes, lNodesToRemove);
		candidates.clear();	
	}
	
	private void matchLeaves() {
		List<CandidateMetric> candidates = new ArrayList<CandidateMetric>(); 
		GeneralNode l = null, r = null;
		int lNodeType = 0;
		double similarity = 0;
		Set<GeneralNode> lNodesToRemove = new HashSet<GeneralNode>();
		for (int i = 0; i < leftLeaves.size(); i++) {
			l = leftLeaves.get(i);
			lNodeType = l.getNodeType();
			for (int j = 0; j < rightLeaves.size(); j++) {
				r = rightLeaves.get(j);
				if (!r.isMatched()) {
					if (r.getNodeType() == lNodeType) {
						similarity = STRING_SIM_CALC.calculateSimilarity(l.getStrValue(), r.getStrValue());
						if (Math.abs(similarity - 1.0) < 1e-6) {
							candidates.add(new CandidateMetric(r, similarity));
							break;
						} else if (similarity >= STRING_SIM_CALC.STRING_SIM_THRES) {
							candidates.add(new CandidateMetric(r, similarity));
						}
					}
				}				
			}
			int tmpSize = candidates.size();
			if (tmpSize == 0)
				continue;
			if (tmpSize > 1)
				Collections.sort(candidates);	
			r = candidates.get(0).getLeft();
			addMatch(l, r, rightLeaves, lNodesToRemove, candidates);		
		}
		leftLeaves.removeAll(lNodesToRemove);		
	}
	
	private void matchInnerNodes() {
		GeneralNode l = null, r = null;
		STRUCT_SIM_CALC.setLeafMatches(new HashSet<Pair<GeneralNode, GeneralNode>>(fMatch));
		List<CandidateMetric> candidates = new ArrayList<CandidateMetric>();
		CandidateMetric c = null;
		Set<GeneralNode> lNodesToRemove = new HashSet<GeneralNode>();
		for (int i = 0; i < leftInners.size(); i++) {
			l = leftInners.get(i);
			if (!l.isSpecialForMatch()) {
				for (int j = 0; j < rightInners.size(); j++) {
					r = rightInners.get(j);
					c = new CandidateMetric(r, 0.0);					
					if (!r.isSpecialForMatch() && (equalsInner(l, r, c))) {
						candidates.add(c);
					}
				}
			}
			int tmpSize = candidates.size();
			if (tmpSize == 0)
				continue;
			//if there is more than one candidate
			GeneralNode best = candidates.get(0).getLeft();
			if (tmpSize > 1) {
				List<Integer> refinedList = new ArrayList<Integer>();
				double percent = countMatchedChild(l, best);	
				double maxPercent = percent;
				refinedList.add(0);
				// find the best match based on the percentage of matched children
				for (int j = 1; j < candidates.size(); j++) {
					r = candidates.get(j).getLeft();
					percent = countMatchedChild(l, r);
					if (percent - maxPercent > 1e-6) {
						maxPercent = percent;
						refinedList.clear();
						refinedList.add(j);
					} else if (Math.abs(percent - maxPercent) < 1e-6) {
						refinedList.add(j);//there may be multiple nodes have the same percentage
					}
				}
				c = candidates.get(refinedList.get(0));
				best = c.getLeft();
				if (refinedList.size() > 1) {
					double sim = c.getRight();
					double maxSim = sim;
					// find the best match based on similarity metric formula
					for (int j = 1; j < refinedList.size(); j++) {
						c = candidates.get(refinedList.get(j));
						sim = c.getRight();
						if (sim > maxSim) {
							maxSim = sim;
							best = c.getLeft();
						}
					}
				}
			}	
			addMatch(l, best, rightInners, lNodesToRemove, candidates);				
		}	
		leftInners.removeAll(lNodesToRemove);
	}
	
	private void matchInnerAndLeaf() {//focus on special nodes
		GeneralNode l = null, r = null;
		Set<GeneralNode> lNodesToRemove = new HashSet<GeneralNode>();
		List<GeneralNode> leftNodes = new ArrayList<GeneralNode>(leftLeaves);
		leftNodes.addAll(leftInners);
		List<GeneralNode> rightNodes = new ArrayList<GeneralNode>(rightLeaves);
		rightNodes.addAll(rightInners);
		for (int i = 0; i < leftNodes.size(); i++ ){
			l = leftNodes.get(i);
			if (!l.isSpecialForMatch())
				continue;
			for (int j = 0; j < rightNodes.size(); j++) {
				r = rightNodes.get(j);
				if (!r.isSpecialForMatch())
					continue;
				if (equalsSpecial(l, r)) {
					addMatch(l, r, rightNodes, lNodesToRemove);
				}
			}
		}
		leftLeaves.removeAll(lNodesToRemove);
		leftInners.removeAll(lNodesToRemove);
		rightLeaves.retainAll(rightNodes);
		rightInners.retainAll(rightNodes);
	}
	
	private boolean areNodesComparable(int lNodeType, int rNodeType, String lStrValue, String rStrValue) {
		if (lNodeType == ASTNode.IF_STATEMENT
				&& (rStrValue.equals("then:") || rStrValue.equals("else:"))
	    || (lStrValue.equals("then:") || lStrValue.equals("else:"))
				&& rNodeType == ASTNode.IF_STATEMENT) {
			return false;
		}
		return true;
	}
	
	private boolean areTypesCompatible(int lNodeType, int rNodeType) {
		if (lNodeType == rNodeType)
			return true;
		return !(INCOMP_TYPES.contains(lNodeType) && INCOMP_TYPES.contains(rNodeType));
	}
	
	private double countMatchedChild(GeneralNode x, GeneralNode y) {
		int totalCounter = 0;
		int counter = 0;
		Enumeration<GeneralNode> enumeration = y.postorderEnumeration();
		GeneralNode l = null, r = null;
		while (enumeration.hasMoreElements()) {
			totalCounter++;
			r = enumeration.nextElement();
			if (r.isMatched()) {
				l = getMatchedLeftNode(r);
				if (l != null && l.isNodeAncestor(x)) {
					counter++;
				}
			}
		}
		return counter * 1.0/totalCounter;
	}
	
	public boolean equalsInner(GeneralNode l, GeneralNode r, CandidateMetric c) {
		int lNodeType = l.getNodeType();
		int rNodeType = r.getNodeType();
		String lStrValue = l.getStrValue();
		String rStrValue = r.getStrValue();
		if (!areNodesComparable(lNodeType, rNodeType, lStrValue, rStrValue))
			return false;
		
		if (!areTypesCompatible(lNodeType, rNodeType))
			return false;
		
		// leverage dynamic metric
		double t = STRUCT_SIM_THRES, t2 = t;
		if (l.getLeafCount() < DYNAMIC_DEPTH || r.getLeafCount() < DYNAMIC_DEPTH) {
			t = DYNAMIC_THRES;
			t2 = t/2;
		}
		double simStruct = STRUCT_SIM_CALC.calculateSimilarity(l, r);
		double simString = STRING_SIM_CALC.calculateSimilarity(l.getStrValue(), r.getStrValue());
		
		boolean ret = simStruct >= STRUCT_WEIGHT_THRES
			|| simStruct >= t && simString >= STRING_SIM_CALC.STRING_SIM_THRES
			|| simStruct >= t2 && simString >= STRING_WEIGHT_THRES
			|| lNodeType == rNodeType && simString >= STRING_SIM_CALC.STRING_SIM_THRES;
		c.setRight(simStruct * 3 + simString);				
		return ret;
	}
	
	public boolean equalsSpecial(GeneralNode l, GeneralNode r) {
		if (!l.getStrValue().equals(r.getStrValue()))
			return false;
		GeneralNode lParent = (GeneralNode) l.getParent();
		GeneralNode rParent = (GeneralNode) r.getParent();
		GeneralNode matchedLeft = getMatchedLeftNode(rParent);
		if (matchedLeft == null || !matchedLeft.equals(lParent))
			return false;
		return true;
	}
	
	private GeneralNode getMatchedLeftNode(GeneralNode n) {
		for (Pair<GeneralNode, GeneralNode> p : fMatch) {
			if (p.getRight().equals(n))
				return p.getLeft();
		}
		return null;
 	}
	
}
