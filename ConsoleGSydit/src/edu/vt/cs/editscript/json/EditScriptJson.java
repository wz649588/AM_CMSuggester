package edu.vt.cs.editscript.json;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import ch.uzh.ifi.seal.changedistiller.treedifferencing.TreeEditOperation;
import ch.uzh.ifi.seal.changedistiller.treedifferencing.TreeEditOperation.OperationType;
import ch.uzh.ifi.seal.changedistiller.treedifferencing.operation.DeleteOperation;
import ch.uzh.ifi.seal.changedistiller.treedifferencing.operation.InsertOperation;
import ch.uzh.ifi.seal.changedistiller.treedifferencing.operation.MoveOperation;
import ch.uzh.ifi.seal.changedistiller.treedifferencing.operation.UpdateOperation;

public class EditScriptJson {
	private Map<String, List<EditOperationJson>> oldScripts;
	private Map<String, List<EditOperationJson>> newScripts;

	public EditScriptJson() {
		oldScripts = new HashMap<>();
		newScripts = new HashMap<>();
	}
	
	public List<EditOperationJson> getOldScript(String sig) {
		return oldScripts.get(sig);
	}
	
	public List<EditOperationJson> getNewScript(String sig) {
		return newScripts.get(sig);
	}
	
	public void addOldScript(String sig, List<TreeEditOperation> edits) {
		List<EditOperationJson> script = new ArrayList<>();
		for (TreeEditOperation edit: edits) {
			String type;
			String label;
			String value;
			String newValue = null;
			if (edit instanceof DeleteOperation) {
				type = "Delete";
				DeleteOperation op = (DeleteOperation) edit;
				label = op.getNodeToDelete().getLabel().toString();
				value = op.getNodeToDelete().getValue();
			} else if (edit instanceof InsertOperation) {
				type = "Insert";
				InsertOperation op = (InsertOperation) edit;
				label = op.getNodeToInsert().getLabel().toString();
				value = op.getNodeToInsert().getValue();
			} else if (edit instanceof MoveOperation) {
				type = "Move";
				MoveOperation op = (MoveOperation) edit;
				label = op.getNodeToMove().getLabel().toString();
				value = op.getNodeToMove().getValue();
			} else { // UpdateOperation
				type = "Update";
				UpdateOperation op = (UpdateOperation) edit;
				label = op.getNodeToUpdate().getLabel().toString();
				value = op.getNodeToUpdate().getValue();
				newValue = op.getNewNode().getValue();
			}
			script.add(new EditOperationJson(type, label, value, newValue));
		}
		oldScripts.put(sig, script);
	}
	
	public void addNewScript(String sig, List<TreeEditOperation> edits) {
		List<EditOperationJson> script = new ArrayList<>();
		for (TreeEditOperation edit: edits) {
			String type;
			String label;
			String value;
			String newValue = null;
			if (edit instanceof DeleteOperation) {
				type = "Delete";
				DeleteOperation op = (DeleteOperation) edit;
				label = op.getNodeToDelete().getLabel().toString();
				value = op.getNodeToDelete().getValue();
			} else if (edit instanceof InsertOperation) {
				type = "Insert";
				InsertOperation op = (InsertOperation) edit;
				label = op.getNodeToInsert().getLabel().toString();
				value = op.getNodeToInsert().getValue();
			} else if (edit instanceof MoveOperation) {
				type = "Move";
				MoveOperation op = (MoveOperation) edit;
				label = op.getNodeToMove().getLabel().toString();
				value = op.getNodeToMove().getValue();
			} else { // UpdateOperation
				type = "Update";
				UpdateOperation op = (UpdateOperation) edit;
				label = op.getNewNode().getLabel().toString();
				value = op.getNodeToUpdate().getValue();
				newValue = op.getNewNode().getValue();
			}
			script.add(new EditOperationJson(type, label, value, newValue));
		}
		newScripts.put(sig, script);
	}
	
	public class EditOperationJson {
		
		/**
		 * Type of edit operation: Delete, Insert, Move, Update
		 */
		String type;
		
		/**
		 * label of the edited node
		 */
		String label;
		
		/**
		 * The concrete statement
		 */
		String value;
		
		/**
		 * Only for Update, the new concrete statement
		 */
		String newValue;
		
		EditOperationJson(String type, String label) {
			this(type, label, null, null);
		}
		
		EditOperationJson(String type, String label, String value) {
			this(type, label, value, null);
		}
		
		EditOperationJson(String type, String label, String value, String newValue) {
			this.type = type;
			this.label = label;
			this.value = value;
			this.newValue = newValue;
		}
		
		public String getType() {
			return type;
		}
		
		public String getLabel() {
			return label;
		}
		
		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (this.getClass() != obj.getClass())
				return false;
			EditOperationJson e = (EditOperationJson) obj;
			if (type == null) {
				if (e.type != null)
					return false;
			} else if (!type.equals(e.type))
				return false;
			if (label == null) {
				if (e.label != null)
					return false;
			} else if (!label.equals(e.label))
				return false;
			return true;
		}
	}
}
