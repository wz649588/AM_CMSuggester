package edu.vt.cs.append;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import ch.uzh.ifi.seal.changedistiller.model.classifiers.SourceRange;
import ch.uzh.ifi.seal.changedistiller.model.entities.SourceCodeChange;
import ch.uzh.ifi.seal.changedistiller.model.entities.SourceCodeEntity;


// added by nameng
public class FineChangesInMethod extends SourceCodeChange {
	private List<SourceCodeChange> fineChanges = null;
	// from old range to change
	private Map<SourceRange, SourceCodeChange> rangeToChange = null;
	
	public FineChangesInMethod(SourceCodeEntity oEntity, SourceCodeEntity nEntity, List<SourceCodeChange> changes) {
		super();
		super.setChangedEntity(new CompositeEntity(oEntity, nEntity));
		fineChanges = new ArrayList<SourceCodeChange>(changes);
		rangeToChange = new HashMap<SourceRange, SourceCodeChange>();
		for (SourceCodeChange c : fineChanges) {
			SourceCodeEntity e = c.getChangedEntity();
			rangeToChange.put(new SourceRange(e.getStartPosition(), e.getEndPosition()),
					c);
		}
	}

	public SourceCodeChange getChange(SourceRange r) {
		return rangeToChange.get(r);
	}
	
	public List<SourceCodeChange> getChanges() {
		return fineChanges;
	}

	public String toString() {
		StringBuffer buf = new StringBuffer(super.toString());
		buf.append("\n");
		for (SourceCodeChange c : fineChanges) {
			buf.append("\t").append(c);
		}
		buf.append("\n");
		return buf.toString();
	}
}
