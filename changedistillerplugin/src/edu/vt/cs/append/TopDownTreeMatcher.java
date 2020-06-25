package edu.vt.cs.append;

import java.util.ArrayList;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Queue;
import java.util.Set;

import ch.uzh.ifi.seal.changedistiller.model.classifiers.java.JavaEntityType;
import ch.uzh.ifi.seal.changedistiller.treedifferencing.Node;
import ch.uzh.ifi.seal.changedistiller.treedifferencing.NodePair;
import ch.uzh.ifi.seal.changedistiller.treedifferencing.TreeMatcher;
import ch.uzh.ifi.seal.changedistiller.treedifferencing.matching.measure.NodeSimilarityCalculator;
import ch.uzh.ifi.seal.changedistiller.treedifferencing.matching.measure.StringSimilarityCalculator;

public class TopDownTreeMatcher implements TreeMatcher {

	Map<Node, Node> leftToRightUnmatched = null;
	Map<Node, Node> rightToLeftUnmatched = null;
	
	// Ye Wang
	private String afName;
	private String afClass;
	
	// Ye Wang
	public TopDownTreeMatcher(String afName, String afClass) {
		this.afName = afName;
		this.afClass = afClass;
	}
	
	public TopDownTreeMatcher() {}

	@Override
	public void init(StringSimilarityCalculator leafStringSimilarityCalculator,
			double leafStringSimilarityThreshold,
			NodeSimilarityCalculator nodeSimilarityCalculator,
			double nodeSimilarityThreshold) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void init(StringSimilarityCalculator leafStringSimilarityCalculator,
			double leafStringSimilarityThreshold,
			StringSimilarityCalculator nodeStringSimilarityCalculator,
			double nodeStringSimilarityThreshold,
			NodeSimilarityCalculator nodeSimilarityCalculator,
			double nodeSimilarityThreshold) {
		// TODO Auto-generated method stub
		
	}
	
	public Map<Node, Node> getUnmatchedLeftToRight() {
		return leftToRightUnmatched;
	}
	
	public Map<Node, Node> getUnmatchedRightToLeft() {
		return rightToLeftUnmatched;
	}

	/**
	 * Match trees in a top-down manner
	 */
	@Override
	public void match(Node left, Node right) {
		leftToRightUnmatched = new HashMap<Node, Node>();
		rightToLeftUnmatched = new HashMap<Node, Node>();
		Queue<Node> lQueue = new LinkedList<Node>();
		Queue<Node> rQueue = new LinkedList<Node>();
		lQueue.add(left);
		rQueue.add(right);
		Node lTmp = null, rTmp = null;		
		while(!lQueue.isEmpty() && !rQueue.isEmpty()) {
			lTmp = lQueue.remove();
			rTmp = rQueue.remove();				
			if (lTmp.getLabel().equals(rTmp.getLabel())
					&& lTmp.getChildCount() == rTmp.getChildCount()) {
				if (lTmp.getLabel().equals(JavaEntityType.METHOD) ||
						lTmp.getLabel().equals(JavaEntityType.TYPE_PARAMETER)) {// the invoked methods are different, so the parent nodes (MethodInvocation) are considered unmatched
					if (!lTmp.getValue().equals(rTmp.getValue())) {
						Node lParent = (Node)lTmp.getParent(); 
						Node rParent = (Node)rTmp.getParent();
						leftToRightUnmatched.put(lParent, rParent);
						rightToLeftUnmatched.put(rParent, lParent);
					}
				} 
				Enumeration<Node> lEnum = lTmp.children();
				Enumeration<Node> rEnum = rTmp.children();
				while(lEnum.hasMoreElements()) {
					lQueue.add(lEnum.nextElement());
					rQueue.add(rEnum.nextElement());
				}							
			} else {
				leftToRightUnmatched.put(lTmp, rTmp);
				rightToLeftUnmatched.put(rTmp, lTmp);
			}
		}	
		
		if (leftToRightUnmatched.size() > 1) {//refine the data
			Set<Node> covered = new HashSet<Node>();
			Set<Node> knownNodes = new HashSet<Node>(leftToRightUnmatched.keySet());
			for (Node tmp : knownNodes) {							
				Set<Node> ancestors = new HashSet<Node>();
				Node parent = (Node) tmp.getParent();
				while (parent != null) {
					ancestors.add(parent);
					parent = (Node) parent.getParent();
				}
				ancestors.retainAll(knownNodes);
				if (!ancestors.isEmpty()) {
					covered.add(tmp);
				}
			}
			for (Node tmp : covered) {
				Node tmpRight = leftToRightUnmatched.get(tmp);
				leftToRightUnmatched.remove(tmp);
				rightToLeftUnmatched.remove(tmpRight);
			}
		}
	}
	
	public Map<Node, Node> leftToRightOtherClassField = null;
	public Map<Node, Node> rightToLeftOtherClassField = null;
	
	public Map<Node, Node> leftToRightSameClassField = null;
	public Map<Node, Node> rightToLeftSameClassField = null;
	
	public Map<Node, Node> leftToRightStringLiteral = null;
	public Map<Node, Node> rightToLeftStringLiteral = null;
	
	public Map<Node, Node> leftToRightNumberLiteral = null;
	public Map<Node, Node> rightToLeftNumberLiteral = null;
	
	public Map<Node, Node> leftToRightNullLiteral = null;
	public Map<Node, Node> rightToLeftNullLiteral = null;
	
	public Map<Node, Node> leftToRightBooleanLiteral = null;
	public Map<Node, Node> rightToLeftBooleanLiteral = null;
	
	public Map<Node, Node> leftToRightCharacterLiteral = null;
	public Map<Node, Node> rightToLeftCharacterLiteral = null;
	
	
	// Ye Wang
	public void match2(Node left, Node right) {
		leftToRightOtherClassField = new HashMap<Node, Node>();
		rightToLeftOtherClassField = new HashMap<Node, Node>();
		leftToRightSameClassField = new HashMap<Node, Node>();
		rightToLeftSameClassField = new HashMap<Node, Node>();
		leftToRightStringLiteral = new HashMap<Node, Node>();
		rightToLeftStringLiteral = new HashMap<Node, Node>();
		leftToRightNumberLiteral = new HashMap<Node, Node>();
		rightToLeftNumberLiteral = new HashMap<Node, Node>();
		leftToRightNullLiteral = new HashMap<Node, Node>();
		rightToLeftNullLiteral = new HashMap<Node, Node>();
		leftToRightBooleanLiteral = new HashMap<Node, Node>();
		rightToLeftBooleanLiteral = new HashMap<Node, Node>();
		leftToRightCharacterLiteral = new HashMap<Node, Node>();
		rightToLeftCharacterLiteral = new HashMap<Node, Node>();
		
		Queue<Node> lQueue = new LinkedList<Node>();
		Queue<Node> rQueue = new LinkedList<Node>();
		lQueue.add(left);
		rQueue.add(right);
		Node lTmp = null, rTmp = null;		
		while(!lQueue.isEmpty() && !rQueue.isEmpty()) {
			lTmp = lQueue.remove();
			rTmp = rQueue.remove();				
			if (lTmp.getLabel().equals(rTmp.getLabel())
					&& lTmp.getChildCount() == rTmp.getChildCount()) {
				
				Enumeration<Node> lEnum = lTmp.children();
				Enumeration<Node> rEnum = rTmp.children();
				while(lEnum.hasMoreElements()) {
					lQueue.add(lEnum.nextElement());
					rQueue.add(rEnum.nextElement());
				}
			}
			
			// (c1.f1 or f1) ==> c2.f
			if (rTmp.getLabel().equals(JavaEntityType.QUALIFIED_NAME)
					&& rTmp.getChildCount() == 3) {
				Node rFirstChild = (Node) rTmp.getChildAt(0);
				Node rSecondChild = (Node) rTmp.getChildAt(1);
				Node rThirdChild = (Node) rTmp.getChildAt(2);
				if (rFirstChild.getValue().equals(this.afClass)
						&& rSecondChild.getValue().equals(".")
						&& rThirdChild.getValue().equals(this.afName)) {
					
					// c1.f1 ==> c2.f
					if (lTmp.getLabel().equals(JavaEntityType.QUALIFIED_NAME)
							&& lTmp.getChildCount() == 3) {
						Node lFirstChild = (Node) lTmp.getChildAt(0);
						Node lThirdChild = (Node) lTmp.getChildAt(2);
						
						if (!lFirstChild.getValue().equals(this.afClass)) {
							// c1.f1 ==> c2.f
							this.leftToRightOtherClassField.put(lTmp, rTmp);
							this.rightToLeftOtherClassField.put(rTmp, lTmp);
						} else if (!lThirdChild.getValue().equals(this.afName)) {
							// c2.f1 ==> c2.f
							this.leftToRightSameClassField.put(lTmp, rTmp);
							this.rightToLeftSameClassField.put(rTmp, lTmp);
						} 
					}
					
					// f1 ==> c2.f
					if (lTmp.getLabel().equals(JavaEntityType.SIMPLE_NAME)
							&& !((Node)lTmp.getParent()).getLabel().equals(JavaEntityType.QUALIFIED_NAME)) {
						this.leftToRightOtherClassField.put(lTmp, rTmp);
						this.rightToLeftOtherClassField.put(rTmp, lTmp);
					}
					
				}
			}
			
			// (c1.f1 or f1) ==> f
			if (rTmp.getLabel().equals(JavaEntityType.SIMPLE_NAME)
					&& rTmp.getValue().equals(this.afName)
					&& !((Node)rTmp.getParent()).getLabel().equals(JavaEntityType.QUALIFIED_NAME)) {
				
				// f1 ==> f
				if (lTmp.getLabel().equals(JavaEntityType.SIMPLE_NAME)
						&& !lTmp.getValue().equals(this.afName)
						&& !((Node)lTmp.getParent()).getLabel().equals(JavaEntityType.QUALIFIED_NAME)) {
					this.leftToRightSameClassField.put(lTmp, rTmp);
					this.rightToLeftSameClassField.put(rTmp, lTmp);
				}
				
				// c1.f1 ==> f
				if (lTmp.getLabel().equals(JavaEntityType.QUALIFIED_NAME)) {
					this.leftToRightOtherClassField.put(lTmp, rTmp);
					this.rightToLeftOtherClassField.put(rTmp, lTmp);
				}
			}
			
			// c1.f ==> c2.f
//			if (lTmp.getLabel().equals(JavaEntityType.QUALIFIED_NAME)
//					&& rTmp.getLabel().equals(JavaEntityType.QUALIFIED_NAME)
//					&& lTmp.getChildCount() == 3
//					&& rTmp.getChildCount() == 3) {
//				Node lFirstChild = (Node) lTmp.getChildAt(0);
//				Node rFirstChild = (Node) rTmp.getChildAt(0);
//				Node lSecondChild = (Node) lTmp.getChildAt(1);
//				Node rSecondChild = (Node) rTmp.getChildAt(1);
//				Node lThirdChild = (Node) lTmp.getChildAt(2);
//				Node rThirdChild = (Node) rTmp.getChildAt(2);
//				
//				if (/*lFirstChild.getLabel().equals(JavaEntityType.TYPE_PARAMETER)
//						&& rFirstChild.getLabel().equals(JavaEntityType.TYPE_PARAMETER)
//						&& */ rFirstChild.getValue().equals(this.afClass)
//						&& lSecondChild.getValue().equals(".")
//						&& rSecondChild.getValue().equals(".")
//						/*&& lThirdChild.getValue().equals(this.afName)*/
//						&& rThirdChild.getValue().equals(this.afName)) {
//					if (lFirstChild.getValue().equals(this.afClass)) {
//						this.leftToRightSameClassField.put(lTmp, rTmp);
//						this.rightToLeftSameClassField.put(rTmp, lTmp);
//					} else {
//						this.leftToRightOtherClassField.put(lTmp, rTmp);
//						this.rightToLeftOtherClassField.put(rTmp, lTmp);
//					}
//				}
//			}
//			
//			// f1 ==> f2, field in the same class
//			if (lTmp.getLabel().equals(JavaEntityType.SIMPLE_NAME)
//					&& rTmp.getLabel().equals(JavaEntityType.SIMPLE_NAME)
//					&& !lTmp.getValue().equals(this.afName)
//					&& rTmp.getValue().equals(this.afName)) {
//					this.leftToRightSameClassField.put(lTmp, rTmp);
//					this.rightToLeftSameClassField.put(rTmp, lTmp);
//			}
			
			// AF appears alone, with class or object before it
			if (rTmp.getLabel().equals(JavaEntityType.SIMPLE_NAME)
					&& rTmp.getValue().equals(this.afName)) {
				if (lTmp.getLabel().equals(JavaEntityType.STRING_LITERAL)) {
					// StringLiteral ==> AF
					this.leftToRightStringLiteral.put(lTmp, rTmp);
					this.rightToLeftStringLiteral.put(rTmp, lTmp);
				} else if (lTmp.getLabel().equals(JavaEntityType.NUMBER_LITERAL)) {
					// NumberLiteral ==> AF
					this.leftToRightNumberLiteral.put(lTmp, rTmp);
					this.rightToLeftNumberLiteral.put(rTmp, lTmp);
				} else if (lTmp.getLabel().equals(JavaEntityType.BOOLEAN_LITERAL)) {
					// BOOLEAN_LITERAL ==> AF
					this.leftToRightBooleanLiteral.put(lTmp, rTmp);
					this.rightToLeftBooleanLiteral.put(rTmp, lTmp);
				} else if (lTmp.getLabel().equals(JavaEntityType.NULL_LITERAL)) {
					// NULL_LITERAL ==> AF
					this.leftToRightNullLiteral.put(lTmp, rTmp);
					this.rightToLeftNullLiteral.put(rTmp, lTmp);
				} else if (lTmp.getLabel().equals(JavaEntityType.CHARACTER_LITERAL)) {
					// CHARACTER_LITERAL ==> AF
					this.leftToRightCharacterLiteral.put(lTmp, rTmp);
					this.rightToLeftCharacterLiteral.put(rTmp, lTmp);
				}
			}
			
			// Literal ==> afClass.AF
			if (rTmp.getLabel().equals(JavaEntityType.QUALIFIED_NAME)
					&& rTmp.getChildCount() == 3) {
				Node rThirdChild = (Node) rTmp.getChildAt(2);
				if (rThirdChild.getValue().equals(this.afName)) {
					if (lTmp.getLabel().equals(JavaEntityType.STRING_LITERAL)) {
						// StringLiteral ==> afClass.AF
						this.leftToRightStringLiteral.put(lTmp, rTmp);
						this.rightToLeftStringLiteral.put(rTmp, lTmp);
					} else if (lTmp.getLabel().equals(JavaEntityType.NUMBER_LITERAL)) {
						// NumberLiteral ==> afClass.AF
						this.leftToRightNumberLiteral.put(lTmp, rTmp);
						this.rightToLeftNumberLiteral.put(rTmp, lTmp);
					} else if (lTmp.getLabel().equals(JavaEntityType.BOOLEAN_LITERAL)) {
						// BOOLEAN_LITERAL ==> afClass.AF
						this.leftToRightBooleanLiteral.put(lTmp, rTmp);
						this.rightToLeftBooleanLiteral.put(rTmp, lTmp);
					} else if (lTmp.getLabel().equals(JavaEntityType.NULL_LITERAL)) {
						// NULL_LITERAL ==> afClass.AF
						this.leftToRightNullLiteral.put(lTmp, rTmp);
						this.rightToLeftNullLiteral.put(rTmp, lTmp);
					} else if (lTmp.getLabel().equals(JavaEntityType.CHARACTER_LITERAL)) {
						// CHARACTER_LITERAL ==> afClass.AF
						this.leftToRightCharacterLiteral.put(lTmp, rTmp);
						this.rightToLeftCharacterLiteral.put(rTmp, lTmp);
					}
				}
			}
			
		}
	}

	@Override
	public void setMatchingSet(Set<NodePair> matchingSet) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void enableDynamicThreshold(int depth, double threshold) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void disableDynamicThreshold() {
		// TODO Auto-generated method stub
		
	}

}
