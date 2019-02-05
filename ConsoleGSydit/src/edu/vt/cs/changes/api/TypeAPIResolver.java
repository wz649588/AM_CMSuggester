package edu.vt.cs.changes.api;

import java.util.Map;
import java.util.Set;

import org.eclipse.jdt.core.dom.ITypeBinding;

import partial.code.grapa.dependency.graph.DataFlowAnalysisEngine;
import edu.vt.cs.changes.ChangeFact;

public class TypeAPIResolver extends APIResolver{
	public TypeAPIResolver(DataFlowAnalysisEngine lEngine,
			DataFlowAnalysisEngine rEngine) {
		super(lEngine, rEngine);
	}
}
