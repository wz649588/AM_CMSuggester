package edu.vt.cs.editscript.common;

import java.util.Comparator;
import java.util.Iterator;

import org.jgrapht.Graph;
import org.jgrapht.GraphMapping;
import org.jgrapht.alg.isomorphism.VF2SubgraphIsomorphismInspector;
import org.jgrapht.graph.DefaultDirectedGraph;

import edu.vt.cs.editscript.json.GraphDataJson;
import edu.vt.cs.editscript.json.GraphDataJson.GraphEdge;
import edu.vt.cs.editscript.json.GraphDataJson.GraphNode;

public class Test2 {

	public static void main(String[] args) {
		GraphDataJson data1 = new GraphDataJson();
		GraphNode n1 = data1.new GraphNode("n1", 1);
		GraphNode n2 = data1.new GraphNode("n2", 1);
		GraphNode n3 = data1.new GraphNode("n3", 2);
		GraphEdge e1 = data1.new GraphEdge(n1, n2, 1, 0);
		GraphEdge e2 = data1.new GraphEdge(n2, n3, 1, 0);
		data1.addEdge(e1);
		data1.addEdge(e2);
		
//		Graph<GraphNode, GraphEdge> graph1 = new DefaultDirectedGraph<>(GraphEdge.class);
//		graph1.addVertex(n1);
//		graph1.addVertex(n2);
//		graph1.addVertex(n3);
//		graph1.addEdge(n1, n3, e1);
//		graph1.addEdge(n2, n3, e2);
		
		GraphDataJson data2 = new GraphDataJson();
		GraphNode m1 = data2.new GraphNode("m1", 1);
		GraphNode m2 = data2.new GraphNode("m2", 2);
		GraphEdge e4 = data2.new GraphEdge(m1, m2, 1, 0);
		data2.addEdge(e4);
		
//		Graph<GraphNode, GraphEdge> graph2= new DefaultDirectedGraph<>(GraphEdge.class);
//		graph2.addVertex(m1);
//		graph2.addVertex(m2);
//		graph2.addEdge(m1, m2, e3);
		
		Graph<GraphNode, GraphEdge> gA = data2.getJgrapht();
		Graph<GraphNode, GraphEdge> gB = data1.getJgrapht();
		
		boolean result = isGraphASubgraphOfGraphB(gA, gB);
		
		System.out.println(result);
		
		
	}
	
	private static Comparator<GraphNode> vertexComparator = new Comparator<GraphNode>(){
		@Override
		public int compare(GraphNode n1, GraphNode n2) {
			return n1.getType() - n2.getType();
//			return 0;
		}
	};
	
	private static Comparator<GraphEdge> edgeComparator = new Comparator<GraphEdge>(){
		@Override
		public int compare(GraphEdge e1, GraphEdge e2) {
			return e1.getType() - e2.getType();
//			return 0;
		}
	};
	
	private static boolean isGraphASubgraphOfGraphB(Graph<GraphNode, GraphEdge> gA, Graph<GraphNode, GraphEdge> gB) {
//		return gB.vertexSet().containsAll(gA.vertexSet()) && gB.edgeSet().containsAll(gA.edgeSet());
		VF2SubgraphIsomorphismInspector<GraphNode,GraphEdge> isoInspector =
				new VF2SubgraphIsomorphismInspector<>(gA, gB, vertexComparator, edgeComparator);
		
		boolean exists = isoInspector.isomorphismExists();
		
		Iterator<GraphMapping<GraphNode, GraphEdge>> isoIter = isoInspector.getMappings();
		
//		if (isTimeOut(isoIter))
//			return true;
		
		while (isoIter.hasNext()) {
			GraphMapping<GraphNode, GraphEdge> mapping = isoIter.next();
			boolean allNodesContained = true;
			for (GraphNode n: gA.vertexSet()) {
				if (mapping.getVertexCorrespondence(n, true) == null) {
					allNodesContained = false;
					break;
				}
			}
			if (allNodesContained) {
				boolean allEdgesContained = true;
				for (GraphEdge e: gA.edgeSet()) {
					if (mapping.getEdgeCorrespondence(e, true) == null) {
						allEdgesContained = false;
						break;
					}
				}
				if (allEdgesContained)
					return true;
			}
		}
		
		return false;
	}
}
