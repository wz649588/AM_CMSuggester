package edu.vt.cs.editscript.json;

import java.util.ArrayList;
import java.util.List;

import org.jgrapht.Graph;
import org.jgrapht.graph.DefaultDirectedGraph;

import edu.vt.cs.editscript.json.GraphDataJson.GraphEdge;
import edu.vt.cs.editscript.json.GraphDataJson.GraphNode;
import edu.vt.cs.graph.ReferenceNode;

/**
 * The GraphDataJson class only has edges. However, sometimes
 * a graph has only one isolated node. This class is built to
 * store the single nodes.
 * @author Ye Wang
 *
 */
public class GraphDataWithNodesJson extends GraphDataJson {

	private List<GraphNode> nodes;
	
	public GraphDataWithNodesJson() {
		nodes = new ArrayList<>();
	}
	
	public void addNode(ReferenceNode node) {
		GraphNode newNode = new GraphNode(node);
		nodes.add(newNode);
	}
	
	public void addNode(GraphNode node) {
		nodes.add(node);
	}
	
	@Override
	public Graph<GraphNode, GraphEdge> getJgrapht() {
		Graph<GraphNode, GraphEdge> g = new DefaultDirectedGraph<GraphNode, GraphEdge>(GraphEdge.class);
		for (GraphNode n: nodes) {
			g.addVertex(n);
		}
		for (GraphEdge e: edges) {
			g.addEdge(e.src, e.dst, e);
		}
		return g;
	}
	
	public static GraphDataWithNodesJson convertToJsonClass(Graph<GraphNode, GraphEdge> g) {
		GraphDataWithNodesJson json = new GraphDataWithNodesJson();
		for (GraphNode n: g.vertexSet()) {
			json.addNode(n);
		}
		for (GraphEdge e: g.edgeSet()) {
			json.addEdge(e);
		}
		return json;
	}
	
}
