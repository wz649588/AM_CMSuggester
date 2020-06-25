package partial.code.grapa.delta.graph;

import java.util.ArrayList;





import java.util.Collection;
import java.util.Hashtable;

import partial.code.grapa.dependency.graph.StatementEdge;
import partial.code.grapa.dependency.graph.StatementNode;

import com.ibm.wala.cast.ir.ssa.AstAssertInstruction;
import com.ibm.wala.cast.java.ssa.AstJavaInvokeInstruction;
import com.ibm.wala.classLoader.CallSiteReference;
import com.ibm.wala.classLoader.JavaLanguage;
import com.ibm.wala.classLoader.JavaLanguage.JavaInstructionFactory;
import com.ibm.wala.classLoader.NewSiteReference;
import com.ibm.wala.ipa.slicer.HeapStatement;
import com.ibm.wala.ipa.slicer.NormalStatement;
import com.ibm.wala.ipa.slicer.ParamCallee;
import com.ibm.wala.ipa.slicer.ParamCaller;
import com.ibm.wala.ipa.slicer.Statement;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.SSAAbstractInvokeInstruction;
import com.ibm.wala.ssa.SSAArrayStoreInstruction;
import com.ibm.wala.ssa.SSABinaryOpInstruction;
import com.ibm.wala.ssa.SSACheckCastInstruction;
import com.ibm.wala.ssa.SSAConditionalBranchInstruction;
import com.ibm.wala.ssa.SSAFieldAccessInstruction;
import com.ibm.wala.ssa.SSAGetInstruction;
import com.ibm.wala.ssa.SSAGotoInstruction;
import com.ibm.wala.ssa.SSAInstanceofInstruction;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSANewInstruction;
import com.ibm.wala.ssa.SSAPutInstruction;
import com.ibm.wala.ssa.SSAUnaryOpInstruction;
import com.ibm.wala.types.FieldReference;
import com.ibm.wala.types.TypeReference;























import uk.ac.shef.wit.simmetrics.similaritymetrics.Levenshtein;
import util.CostFunction;
import util.EditDistance;
import util.Graph;
import util.MatrixGenerator;
import edu.uci.ics.jung.graph.DirectedSparseGraph;

public class GraphEditScript extends GraphComparator{
	
	
	public GraphEditScript(
			DirectedSparseGraph<StatementNode, StatementEdge> oldGraph,
			IR oldIr, DirectedSparseGraph<StatementNode, StatementEdge> newGraph, IR newIr) {
		// TODO Auto-generated constructor stub
			super(oldGraph, oldIr, newGraph, newIr);
	}

	

	public ArrayList<AbstractEdit> extractChanges() {
		// TODO Auto-generated method stub
		ArrayList<AbstractEdit> changes = new ArrayList<AbstractEdit>();
	
        Hashtable<StatementNode, StatementNode> vm = extractNodeMappings();
        for(StatementNode v1:vm.keySet()){
        	StatementNode v2 = vm.get(v1);
        	if(v2!=null){
        		if(calculateCost(v1,v2)==0){
//	        		System.out.println(v1.statement+" matched.");
	        	}else{
	        		if(calculateNodeCost(v1,v2)!=0){
//	        			System.out.println(v1.statement+" modified.");
	        			UpdateNode un = new UpdateNode(getComparedLabel(leftIr, v1.statement),
		        					getComparedLabel(rightIr, v2.statement));
	           			changes.add(un);
	        		}
					ArrayList<AbstractEdit> ecs = extractEdgeChanges(v1, v2, vm);
					addUniqueEdgeEdits(changes,ecs);
				}
        	}
        }
        
        //left side unmapped nodes
        ArrayList<StatementNode> sns = new ArrayList<StatementNode>();
        sns.addAll(leftGraph.getVertices());
        sns.removeAll(vm.keySet());
        for(StatementNode sn:sns){
    		DeleteNode dn = new DeleteNode(getComparedLabel(leftIr, sn.statement));
    		changes.add(dn);
    		Collection<StatementEdge> edges = leftGraph.getInEdges(sn);
    		for(StatementEdge edge:edges){
        		DeleteEdge de = new DeleteEdge(getComparedLabel(leftIr, edge.from.statement),
        				getComparedLabel(leftIr, edge.to.statement),
        				edge.type);
        		addUniqueEdgeEdit(changes, de);
    		}
    		edges = leftGraph.getOutEdges(sn);
    		for(StatementEdge edge:edges){
        		DeleteEdge de = new DeleteEdge(getComparedLabel(leftIr, edge.from.statement),
        				getComparedLabel(leftIr, edge.to.statement),
        				edge.type);
        		addUniqueEdgeEdit(changes, de);
    		}
        }
        
        //right side unmapped nodes
        sns.clear();
        sns.addAll(rightGraph.getVertices());
        sns.removeAll(vm.values());
        for(StatementNode sn:sns){
    		InsertNode dn = new InsertNode(getComparedLabel(leftIr, sn.statement));
    		changes.add(dn);
    		Collection<StatementEdge> edges = leftGraph.getInEdges(sn);
    		if(edges!=null){
        		for(StatementEdge edge:edges){
        			InsertEdge de = new InsertEdge(getComparedLabel(rightIr, edge.from.statement),
        					getComparedLabel(rightIr, edge.to.statement),
        					edge.type);
	        		addUniqueEdgeEdit(changes, de);
        		}
    		}
    		edges = leftGraph.getOutEdges(sn);
    		if(edges!=null){
        		for(StatementEdge edge:edges){
        			InsertEdge de = new InsertEdge(getComparedLabel(rightIr, edge.from.statement),
        					getComparedLabel(rightIr, edge.to.statement),
        					edge.type);
	        		addUniqueEdgeEdit(changes, de);
        		}
    		}
        }
		return changes;
	}





	private void addUniqueEdgeEdits(ArrayList<AbstractEdit> changes,
			ArrayList<AbstractEdit> edges) {
		// TODO Auto-generated method stub
		for(AbstractEdit e1:edges){
			addUniqueEdgeEdit(changes, e1);
		}
	}

	private void addUniqueEdgeEdit(ArrayList<AbstractEdit> changes,
			AbstractEdit e1) {
		boolean bFound = false;
		for(AbstractEdit e2:changes){
			if(e1.getClass().getName().compareTo(e2.getClass().getName())==0){
				if(e1 instanceof DeleteEdge){
					DeleteEdge de1 = (DeleteEdge)e1;
					DeleteEdge de2 = (DeleteEdge)e2;
					if(de1.getFrom().compareTo(de2.getFrom())==0&&de1.getTo().compareTo(de2.getTo())==0){
						bFound = true;
						break;
					}
				}else{
					InsertEdge de1 = (InsertEdge)e1;
					InsertEdge de2 = (InsertEdge)e2;
					if(de1.getFrom().compareTo(de2.getFrom())==0&&de1.getTo().compareTo(de2.getTo())==0){
						bFound = true;
						break;
					}
				}
			}
		}
		if(!bFound){
			changes.add(e1);
		}
	}
	
	private ArrayList<AbstractEdit> extractEdgeChanges(StatementNode v1, StatementNode v2, Hashtable<StatementNode, StatementNode> vm) {
		// TODO Auto-generated method stub
		ArrayList<AbstractEdit> changes = new ArrayList<AbstractEdit>();
		ArrayList<StatementEdge> e1s = new ArrayList<StatementEdge>();
		e1s.addAll(leftGraph.getInEdges(v1));
		ArrayList<StatementEdge> e2s = new ArrayList<StatementEdge>();
		e2s.addAll(rightGraph.getInEdges(v2));
		for(int i=e1s.size()-1; i>=0; i--){
			StatementEdge e1 = (StatementEdge)e1s.toArray()[i];
			StatementNode v2from = vm.get(e1.from);
			StatementEdge e2 = leftGraph.findEdge(v2from, v2);
			if(e2!=null){
				e1s.remove(e1);
				e2s.remove(e2);
			}
		}
		
		for(StatementEdge e1:e1s){
			DeleteEdge de = new DeleteEdge(getComparedLabel(leftIr, e1.from.statement),
					getComparedLabel(leftIr, e1.to.statement),
					e1.type);
			changes.add(de);
		}
		for(StatementEdge e2:e2s){
			InsertEdge de = new InsertEdge(getComparedLabel(rightIr, e2.from.statement),
					getComparedLabel(rightIr, e2.to.statement),
					e2.type);
			changes.add(de);
		}
		
		e1s.clear();
		e1s.addAll(leftGraph.getOutEdges(v1));
		e2s.clear();
		e2s.addAll(rightGraph.getOutEdges(v2));
		for(int i=e1s.size()-1; i>=0; i--){
			StatementEdge e1 = (StatementEdge)e1s.toArray()[i];
			StatementNode v2to = vm.get(e1.to);
			StatementEdge e2 = leftGraph.findEdge(v2, v2to);
			if(e2!=null){
				e1s.remove(e1);
				e2s.remove(e2);
			}
		}
		
		for(StatementEdge e1:e1s){
			DeleteEdge de = new DeleteEdge(getComparedLabel(leftIr, e1.from.statement),
					getComparedLabel(leftIr, e1.to.statement),
					e1.type);
			changes.add(de);
		}
		for(StatementEdge e2:e2s){
			InsertEdge de = new InsertEdge(getComparedLabel(rightIr, e2.from.statement),
					getComparedLabel(rightIr, e2.to.statement),
					e2.type);
			changes.add(de);
		}
		return changes;
	}






	



	
	
	


	
}
