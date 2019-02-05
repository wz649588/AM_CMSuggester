package edu.vt.cs.changes;

import java.util.ArrayList;
import java.util.List;

import partial.code.grapa.mapping.ClientMethod;
import ch.uzh.ifi.seal.changedistiller.model.classifiers.SourceRange;
import ch.uzh.ifi.seal.changedistiller.model.entities.Move;
import ch.uzh.ifi.seal.changedistiller.model.entities.SourceCodeChange;
import ch.uzh.ifi.seal.changedistiller.model.entities.SourceCodeEntity;
import ch.uzh.ifi.seal.changedistiller.model.entities.Update;
import edu.vt.cs.diffparser.util.SourceCodeRange;

public class ClientMethodMarker {

	public static final int OLD = 1;
	public static final int NEW = 2;
	
	public static List<SourceCodeRange> getChangeRanges(int label, List<SourceCodeChange> changes, ClientMethod m) {
		SourceCodeEntity e = null;
		List<SourceCodeRange> ranges = new ArrayList<SourceCodeRange>();
		SourceRange r = null;
		if (label == OLD) {
			for (SourceCodeChange c : changes) {
				switch (c.getChangeType()) {
				case STATEMENT_INSERT:
					break;
				case STATEMENT_DELETE:
					e = c.getChangedEntity();
					r = e.getSourceRange();
					ranges.add(SourceCodeRange.convert(r));
					break;
				case STATEMENT_UPDATE:
					e = c.getChangedEntity();
					r = e.getSourceRange();
					ranges.add(SourceCodeRange.convert(r));
					break;		
				case STATEMENT_PARENT_CHANGE:
					e = c.getChangedEntity();
					r = e.getSourceRange();
					ranges.add(SourceCodeRange.convert(r));
					break;
				}
			}
		} else {//label == NEW
			for (SourceCodeChange c : changes) {
				switch(c.getChangeType()) {
				case STATEMENT_INSERT:
					e = c.getChangedEntity();
					r = e.getSourceRange();
					ranges.add(new SourceCodeRange(r.getStart(), r.getEnd() - r.getStart()));
					break;
				case STATEMENT_DELETE:
					break;
				case STATEMENT_UPDATE:
					e = ((Update)c).getNewEntity();				
					r = e.getSourceRange();
					ranges.add(new SourceCodeRange(r.getStart(), r.getEnd() - r.getStart()));
					break;
				case STATEMENT_PARENT_CHANGE:
					e = ((Move)c).getNewEntity();
					r = e.getSourceRange();
					ranges.add(new SourceCodeRange(r.getStart(), r.getEnd() - r.getStart()));
					break;
				}
			}
		}
		return ranges;
	}
}
