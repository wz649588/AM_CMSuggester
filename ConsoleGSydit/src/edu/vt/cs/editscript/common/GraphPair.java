package edu.vt.cs.editscript.common;

import org.jgrapht.Graph;

import edu.vt.cs.editscript.json.GraphDataJson.GraphEdge;
import edu.vt.cs.editscript.json.GraphDataJson.GraphNode;

public class GraphPair {
	
	public String bn1;
	public String bn2;
	
	public int gn1;
	public int gn2;
	
	public Graph<GraphNode, GraphEdge> g1;
	public Graph<GraphNode, GraphEdge> g2;
	
	public Graph<GraphNode, GraphEdge> sg1;
	public Graph<GraphNode, GraphEdge> sg2;
}
