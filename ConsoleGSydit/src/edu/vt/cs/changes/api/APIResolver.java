package edu.vt.cs.changes.api;

import partial.code.grapa.dependency.graph.DataFlowAnalysisEngine;

public abstract class APIResolver {

	protected DataFlowAnalysisEngine leftEngine;
	protected DataFlowAnalysisEngine rightEngine;
	
	public APIResolver(DataFlowAnalysisEngine lEngine, DataFlowAnalysisEngine rEngine) {
		leftEngine = lEngine;
		rightEngine = rEngine;
	}
}
