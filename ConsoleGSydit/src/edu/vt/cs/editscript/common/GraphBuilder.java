package edu.vt.cs.editscript.common;

import org.jgrapht.Graph;
import org.jgrapht.graph.DefaultDirectedGraph;

import edu.vt.cs.editscript.json.EditScriptJson;
import edu.vt.cs.editscript.json.GraphDataJson.GraphEdge;
import edu.vt.cs.editscript.json.GraphDataJson.GraphNode;
import edu.vt.cs.editscript.json.ScriptEdge;
import edu.vt.cs.editscript.json.ScriptNode;

public class GraphBuilder {
	
	/**
	 * Create a graph whose node contain an edit script
	 * @param g Original graph
	 * @param script Map for edit scripts
	 * @return a graph whose node contain an edit script
	 */
	public static Graph<ScriptNode, ScriptEdge> create(Graph<GraphNode, GraphEdge> g, EditScriptJson scriptMap) {
		
		Graph<ScriptNode, ScriptEdge> result = new DefaultDirectedGraph<>(ScriptEdge.class);
		for (GraphEdge edge: g.edgeSet()) {
			GraphNode src = edge.getSrc();
			GraphNode dst = edge.getDst();
			ScriptNode newSrc = new ScriptNode(src, scriptMap);
			ScriptNode newDst = new ScriptNode(dst, scriptMap);
			ScriptEdge newEdge = new ScriptEdge(newSrc, newDst, edge.getType());
			
			result.addVertex(newSrc);
			result.addVertex(newDst);
			result.addEdge(newSrc, newDst, newEdge);
		}
		
		return result;
		
	}

}
