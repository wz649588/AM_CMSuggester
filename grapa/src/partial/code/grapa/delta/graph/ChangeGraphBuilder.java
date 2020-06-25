package partial.code.grapa.delta.graph;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.List;
import java.util.Set;








import partial.code.grapa.dependency.graph.StatementEdge;
import partial.code.grapa.dependency.graph.StatementNode;

import com.ibm.wala.ipa.slicer.NormalStatement;
import com.ibm.wala.ssa.IR;

import edu.uci.ics.jung.algorithms.cluster.WeakComponentClusterer;
import edu.uci.ics.jung.algorithms.filters.FilterUtils;
import edu.uci.ics.jung.algorithms.shortestpath.DijkstraShortestPath;
import edu.uci.ics.jung.graph.DirectedSparseGraph;

public class ChangeGraphBuilder extends GraphComparator{

	public ChangeGraphBuilder(
			DirectedSparseGraph<StatementNode, StatementEdge> oldGraph,
			IR oldIr,
			DirectedSparseGraph<StatementNode, StatementEdge> newGraph, IR newIr) {
		super(oldGraph, oldIr, newGraph, newIr);
		// TODO Auto-generated constructor stub
	}

	public ArrayList<DirectedSparseGraph<StatementNode, StatementEdge>> extractChangeGraph() {
		// TODO Auto-generated method stub
		Hashtable<StatementNode, StatementNode> vm = this.extractNodeMappings();
		DirectedSparseGraph<StatementNode, StatementEdge> graph = new DirectedSparseGraph<StatementNode, StatementEdge>();
		//add left nodes
		for(StatementNode s:leftGraph.getVertices()){
			s.side = StatementNode.LEFT;
			graph.addVertex(s);
		}
		
		//add right nodes
		for(StatementNode s:rightGraph.getVertices()){
			s.side = StatementNode.RIGHT;
			graph.addVertex(s);
		}
		
		for(StatementNode n1:graph.getVertices()){
			for(StatementNode n2:graph.getVertices()){
				if(!n1.equals(n2)&&n1.side==n2.side){
					StatementEdge edge;
					if(n1.side==StatementNode.LEFT){
						edge = leftGraph.findEdge(n1, n2);
					}else{
						edge = rightGraph.findEdge(n1, n2);
					}
					if(edge != null){
						graph.addEdge(edge, n1, n2);
					}
				}			
			}
		}
		//remove internal nodes
		ArrayList<StatementNode> toDeleteNodes = new ArrayList<StatementNode>();
		for(StatementNode n1:graph.getVertices()){
			if(n1.side == StatementNode.LEFT){
				StatementNode n2 = vm.get(n1);
				if(n2!=null&&calculateCost(n1,n2)==0){
						toDeleteNodes.add(n1);
						toDeleteNodes.add(n2);
				}
			}
		}		
		
		for(StatementNode node: toDeleteNodes){
			graph.removeVertex(node);
		}
		
		//	
		for(StatementNode n1:graph.getVertices()){
			StatementNode n2 = vm.get(n1);
			if(n2!=null){
				if(calculateCost(n1,n2)!=0&&n1.isSameInterestingType(n2, this.leftIr)){
					StatementEdge edge = graph.findEdge(n1, n2);
					if(edge==null){
						edge = new StatementEdge(n1, n2, StatementEdge.CHANGE);
						graph.addEdge(edge, n1, n2);
					}
				}
			}
		}
		
		ArrayList<DirectedSparseGraph<StatementNode,StatementEdge>> ccs = generateClusters(graph);
		
		return ccs;
	}

	private ArrayList<DirectedSparseGraph<StatementNode, StatementEdge>> generateClusters(
			DirectedSparseGraph<StatementNode, StatementEdge> graph) {
		// TODO Auto-generated method stub
		WeakComponentClusterer<StatementNode, StatementEdge> wcc = new WeakComponentClusterer<StatementNode, StatementEdge>();
		Set<Set<StatementNode>> set = wcc.transform(graph);
		ArrayList<DirectedSparseGraph<StatementNode,StatementEdge>> result = new  ArrayList<DirectedSparseGraph<StatementNode,StatementEdge>> ();
		Collection<DirectedSparseGraph<StatementNode, StatementEdge>> ccs = FilterUtils.createAllInducedSubgraphs(set, graph);
		Iterator<DirectedSparseGraph<StatementNode, StatementEdge>> it = ccs.iterator();
		while(it.hasNext()){
			DirectedSparseGraph<StatementNode, StatementEdge> g = it.next();
//			if(isInteresting(g)){
				result.add(g);
//			}
		}
		return result;
	}

	private boolean isInteresting(
			DirectedSparseGraph<StatementNode, StatementEdge> g) {
		// TODO Auto-generated method stub
		boolean bHasBasicIns = false;
		boolean bHasPhi = false;
		for(StatementNode s:g.getVertices()){
			String label;
			if(s.side == StatementNode.LEFT){
				label = GraphComparator.getComparedLabel(this.leftIr, s.statement);
			}else{
				label = GraphComparator.getComparedLabel(this.rightIr, s.statement);
			}
			if(label.startsWith("invoke")){
				bHasBasicIns = true;
				break;
			}else if(label.startsWith("put")){
				bHasBasicIns = true;
				break;
			}else if(label.startsWith("set")){
				bHasBasicIns = true;
				break;
			}else if(label.indexOf(" phi ")>0){
				bHasPhi = true;
				break;
			}
		}
		return bHasBasicIns||bHasPhi;
	}

}
 