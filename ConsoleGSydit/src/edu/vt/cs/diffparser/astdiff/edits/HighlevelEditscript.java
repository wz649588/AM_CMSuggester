package edu.vt.cs.diffparser.astdiff.edits;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import edu.vt.cs.diffparser.astdiff.edits.ITreeEditOperation.CONTENT_TYPE;
import edu.vt.cs.diffparser.astdiff.edits.ITreeEditOperation.EDIT;
import edu.vt.cs.diffparser.tree.JavaMethodDeclarationNode;

public class HighlevelEditscript extends Editscript {

	List<UpdateOperation> methodUpdates;
	
	public HighlevelEditscript() {
		super();
		methodUpdates = new ArrayList<UpdateOperation>();
	}
	
	public void add(ITreeEditOperation edit) {
		super.add(edit);
		checkOrAddMethodUpdate(edit);			
	}
	
	private void checkOrAddMethodUpdate(ITreeEditOperation edit) {
		if (isMethodUpdate(edit)) {
			methodUpdates.add((UpdateOperation<JavaMethodDeclarationNode>) edit);
		} else if (edit instanceof EditGroup) {
			CONTENT_TYPE ct = null;
			List<ITreeEditOperation> tmpEdits = ((EditGroup)edit).edits;
			switch(edit.getContentType()) {
			case DECLARATION:
			case METHOD_DECLARATION:
				for (ITreeEditOperation tmpEdit : tmpEdits) {
					ct = tmpEdit.getContentType();
					if (ct.equals(CONTENT_TYPE.METHOD_DECLARATION) || ct.equals(CONTENT_TYPE.DECLARATION)) {
						checkOrAddMethodUpdate(tmpEdit);
					}
				}
				break;
			default:
					break;
			}
		}
	}
	
	private boolean isMethodUpdate(ITreeEditOperation edit) {
		return edit.getOperationType().equals(EDIT.UPDATE) &&
				edit.getContentType().equals(CONTENT_TYPE.METHOD_DECLARATION);
	}
	
	public Iterator<UpdateOperation> getMethodUpdates() {
		return methodUpdates.iterator();
	}
}
