package edu.vt.cs.editscript;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import ch.uzh.ifi.seal.changedistiller.model.entities.SourceCodeEntity;
import ch.uzh.ifi.seal.changedistiller.treedifferencing.TreeEditOperation;

public class EditScriptRecorder {
	
	public static EditScriptRecorder recorder;
	
	public static void init() {
		recorder = new EditScriptRecorder();
	}
	
	public Map<SourceCodeEntity, List<TreeEditOperation>> leftEntityToScript;
	public Map<SourceCodeEntity, List<TreeEditOperation>> rightEntityToScript;
	public Map<SourceCodeEntity, SourceCodeEntity> leftToRightEntity;
	public Map<SourceCodeEntity, SourceCodeEntity> rightToLeftEntity;
	
	public EditScriptRecorder() {
		leftEntityToScript = new HashMap<>();
		rightEntityToScript = new HashMap<>();
		leftToRightEntity = new HashMap<>();
		rightToLeftEntity = new HashMap<>();
	}
	
	public void addScript(SourceCodeEntity leftEntity, SourceCodeEntity rightEntity, List<TreeEditOperation> editScript) {
		if (editScript == null || editScript.isEmpty())
			return;
		if (leftEntity.getType().isMethod() || rightEntity.getType().isMethod()) {
			if (leftEntity != null) {
				if (!leftEntityToScript.containsKey(leftEntity)) {
					leftEntityToScript.put(leftEntity, new ArrayList<TreeEditOperation>(editScript));
				} else {
					leftEntityToScript.get(leftEntity).addAll(editScript);
				}
				if (rightEntity != null) {
					leftToRightEntity.put(leftEntity, rightEntity);
				}
			}
			if (rightEntity != null) {
				if (!rightEntityToScript.containsKey(rightEntity)) {
					rightEntityToScript.put(rightEntity, new ArrayList<TreeEditOperation>(editScript));
				} else {
					rightEntityToScript.get(rightEntity).addAll(editScript);
				}
				if (leftEntity != null) {
					rightToLeftEntity.put(rightEntity, leftEntity);
				}
			}
		}
	}
	
	public List<TreeEditOperation> findEditScriptByLeftEntity(SourceCodeEntity leftEntity) {
		return leftEntityToScript.get(leftEntity);
	}
	
	public List<TreeEditOperation> findEditScriptByRightEntity(SourceCodeEntity rightEntity) {
		return rightEntityToScript.get(rightEntity);
	}
	
}