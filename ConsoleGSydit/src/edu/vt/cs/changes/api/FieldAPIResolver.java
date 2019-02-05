package edu.vt.cs.changes.api;

import java.util.Map;
import java.util.Set;

import org.eclipse.jdt.core.dom.IVariableBinding;

import partial.code.grapa.dependency.graph.DataFlowAnalysisEngine;
import edu.vt.cs.changes.ChangeFact;

public class FieldAPIResolver extends APIResolver{

	public FieldAPIResolver(DataFlowAnalysisEngine lEngine,
			DataFlowAnalysisEngine rEngine) {
		super(lEngine, rEngine);
	}

}
