package edu.vt.cs.editscript;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;

import ch.uzh.ifi.seal.changedistiller.model.entities.SourceCodeEntity;
import ch.uzh.ifi.seal.changedistiller.treedifferencing.NodePair;

public class TreeMatchRecorder {

	public static TreeMatchRecorder recorder;
	
	public static void init() {
		recorder = new TreeMatchRecorder();
	}
	
	public Map<SourceCodeEntity, HashSet<NodePair>> leftEntityToMatch;
	public Map<SourceCodeEntity, HashSet<NodePair>> rightEntityToMatch;
	public Map<SourceCodeEntity, SourceCodeEntity> leftToRightEntity;
	public Map<SourceCodeEntity, SourceCodeEntity> rightToLeftEntity;
	
	public TreeMatchRecorder() {
		leftEntityToMatch = new HashMap<>();
		rightEntityToMatch = new HashMap<>();
		leftToRightEntity = new HashMap<>();
		rightToLeftEntity = new HashMap<>();
	}
	
	public void addMatch(SourceCodeEntity leftEntity, SourceCodeEntity rightEntity, HashSet<NodePair> match) {
		if (match == null || match.isEmpty())
			return;
		if (leftEntity.getType().isMethod() || rightEntity.getType().isMethod()) {
			if (leftEntity != null) {
				if (!leftEntityToMatch.containsKey(leftEntity)) {
					leftEntityToMatch.put(leftEntity, new HashSet<NodePair>(match));
				} else {
					leftEntityToMatch.get(leftEntity).addAll(match);
				}
				if (rightEntity != null) {
					leftToRightEntity.put(leftEntity, rightEntity);
				}
			}
			if (rightEntity != null) {
				if (!rightEntityToMatch.containsKey(rightEntity)) {
					rightEntityToMatch.put(rightEntity, new HashSet<NodePair>(match));
				} else {
					rightEntityToMatch.get(rightEntity).addAll(match);
				}
				if (leftEntity != null) {
					rightToLeftEntity.put(rightEntity, leftEntity);
				}
			}
		}
	}
	
	public HashSet<NodePair> findMatchByLeftEntity(SourceCodeEntity leftEntity) {
		return leftEntityToMatch.get(leftEntity);
	}
	
	public HashSet<NodePair> findMatchByRightEntity(SourceCodeEntity rightEntity) {
		return rightEntityToMatch.get(rightEntity);
	}
	
}