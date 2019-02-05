package edu.vt.cs.changes.api;

import java.util.Set;

public class SubgraphComparator {

	public void compare(Subgraph sg1, Subgraph sg2) {		
		Set<SNode> sources1 = sg1.getMarkedSources();
		Set<SNode> sources2 = sg2.getMarkedSources();
		Set<SNode> dests1 = sg1.getMarkedDests();
		Set<SNode> dests2 = sg2.getMarkedDests();
	}
}
