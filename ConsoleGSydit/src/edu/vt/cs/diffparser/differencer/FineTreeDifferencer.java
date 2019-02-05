package edu.vt.cs.diffparser.differencer;

import java.util.ArrayList;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;

import edu.vt.cs.diffparser.astdiff.CommonADT;
import edu.vt.cs.diffparser.astdiff.edits.AbstractTreeEditOperation;
import edu.vt.cs.diffparser.astdiff.edits.DeleteOperation;
import edu.vt.cs.diffparser.astdiff.edits.EditGroup;
import edu.vt.cs.diffparser.astdiff.edits.ITreeEditOperation.CONTENT_TYPE;
import edu.vt.cs.diffparser.astdiff.edits.InsertOperation;
import edu.vt.cs.diffparser.astdiff.edits.LowlevelEditscript;
import edu.vt.cs.diffparser.astdiff.edits.UpdateOperation;
import edu.vt.cs.diffparser.tree.GeneralNode;
import edu.vt.cs.diffparser.tree.JavaImplementationNode;
import edu.vt.cs.diffparser.tree.JavaMethodHeaderNode;
import edu.vt.cs.diffparser.tree.JavaStatementNode;
import edu.vt.cs.diffparser.util.Pair;
import edu.vt.cs.diffparser.util.SourceCodeRange;

public class FineTreeDifferencer extends AbstractTreeDifferencer {

	@Override
	protected void computeEditScript(GeneralNode l, GeneralNode r) {
		JavaMethodHeaderNode left = (JavaMethodHeaderNode)l;
		JavaMethodHeaderNode right = (JavaMethodHeaderNode)r;
		fEditscript = new LowlevelEditscript(left.getStrValue());
		computeDeclarationEdits(left, right);
		compareBody(left.deepCopy(), right.deepCopy());
	}
	
	private void computeDeclarationEdits(JavaMethodHeaderNode left, JavaMethodHeaderNode right) {
		String lName = left.getStrValue();
		String rName = right.getStrValue();
		if (!lName.equals(rName)) {
			fEditscript.add(new UpdateOperation<String>(lName, rName, CONTENT_TYPE.METHOD_NAME));
		}
		EditGroup editGroup = new EditGroup(CONTENT_TYPE.PARAMETER);
		List<Pair<String, String>> paramList1 = left.getParameterList();
		List<Pair<String, String>> paramList2 = right.getParameterList();
		List<Pair<String, String>> params = new ArrayList<Pair<String, String>>(paramList1);
		params.removeAll(paramList2);		
		for (Pair<String, String> p : params) {
			editGroup.add(new DeleteOperation<Pair<String, String>>(p, CONTENT_TYPE.PARAMETER));
		}
		params = new ArrayList<Pair<String, String>>(paramList2);
		params.removeAll(paramList1);
		for (Pair<String, String> p : params) {
			editGroup.add(new InsertOperation<Pair<String, String>>(p, CONTENT_TYPE.PARAMETER));
		}
		if (!editGroup.isEmpty()) {
			fEditscript.add(editGroup);
		}
	}
	
	private Set<GeneralNode> getUpdatedRegions(GeneralNode left, GeneralNode right) {
		Set<GeneralNode> unmatchedLefts = left.findUnmatchedNodes();
		Set<GeneralNode> unmatchedRights = right.findUnmatchedNodes();
		Set<GeneralNode> updatedNodes = new HashSet<GeneralNode>();
		Enumeration<GeneralNode> enumeration = left.breadthFirstEnumeration();
		GeneralNode oNode = null, nNode = null;
		GeneralNode oParent = null, nParent = null;
		while (enumeration.hasMoreElements()) {
			oNode = enumeration.nextElement();
			if (oNode.isMatched()) {
				nNode = fLeftToRightMatch.get(oNode);
				oParent = (GeneralNode) oNode.getParent();
				nParent = (GeneralNode) nNode.getParent();
				if (!nNode.getStrValue().equals(oNode.getStrValue())) {
					if (oParent == null || !updatedNodes.contains(oParent))
						updatedNodes.add(oNode);
				}				
				if (oParent == null && nParent == null || oParent != null && fLeftToRightMatch.get(oParent).equals(nParent)){
					continue;
				}
				if (oParent == null) {
					if (nParent != null && !unmatchedRights.contains(nParent))						
						updatedNodes.add(fRightToLeftMatch.get(nParent));
				} else {
					if (nParent == null || unmatchedRights.contains(nParent)) {
						updatedNodes.add(oParent);
					} 
				} 
			} else {
				oParent = (GeneralNode)oNode.getParent();
				if (oParent != null && !unmatchedLefts.contains(oParent)) {
					updatedNodes.add(oParent);
				}
			}
		}
		return updatedNodes;
	}

	private void compareBody(GeneralNode left, GeneralNode right) {
		Set<GeneralNode> updatedNodes = getUpdatedRegions(left, right);
	}
	
	private Pair<GeneralNode, GeneralNode> removeMatch(GeneralNode lChild, GeneralNode rChild) {
		GeneralNode right = fLeftToRightMatch.remove(lChild);
		GeneralNode left = fRightToLeftMatch.remove(rChild);
		if (right == null) {
			right = fLeftToRightMatch.remove(left);
		}
		if (left == null) {
			left = fRightToLeftMatch.get(right);
		}
		right.setUnmatched();
		left.setUnmatched();
		Pair<GeneralNode, GeneralNode> pair = new Pair<GeneralNode, GeneralNode>(left, right);
		fMatch.remove(pair);
		return pair;
	}
}
