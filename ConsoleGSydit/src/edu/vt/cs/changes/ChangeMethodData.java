package edu.vt.cs.changes;

import java.util.List;
import java.util.Map;
import java.util.Set;

import org.eclipse.jdt.core.dom.IBinding;

import edu.vt.cs.diffparser.util.SourceCodeRange;
import partial.code.grapa.mapping.ClientMethod;

public class ChangeMethodData {

	public ClientMethod oldMethod;
	public ClientMethod newMethod;
	public List<SourceCodeRange> oldASTRanges;
	public List<SourceCodeRange> newASTRanges;
	
	public Map<IBinding, Set<SourceCodeRange>> oldBindingMap = null;
	public Map<IBinding, Set<SourceCodeRange>> newBindingMap = null;
	
	public ChangeMethodData (ClientMethod oMethod, ClientMethod nMethod, List<SourceCodeRange> oRanges,
			List<SourceCodeRange> nRanges){
		oldMethod = oMethod;
		newMethod = nMethod;
		oldASTRanges = oRanges;
		newASTRanges = nRanges;
	}
	
	public String toString() {
		return oldMethod.getSignature() + "--" + newMethod.getSignature();
	}
}
