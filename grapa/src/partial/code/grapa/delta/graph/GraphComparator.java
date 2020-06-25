package partial.code.grapa.delta.graph;

import java.util.Hashtable;

import partial.code.grapa.dependency.graph.StatementEdge;
import partial.code.grapa.dependency.graph.StatementNode;
import uk.ac.shef.wit.simmetrics.similaritymetrics.Levenshtein;
import util.EditDistance;

import com.ibm.wala.cast.ir.ssa.AstAssertInstruction;
import com.ibm.wala.cast.java.ssa.AstJavaInvokeInstruction;
import com.ibm.wala.classLoader.CallSiteReference;
import com.ibm.wala.classLoader.NewSiteReference;
import com.ibm.wala.ipa.slicer.HeapStatement;
import com.ibm.wala.ipa.slicer.NormalReturnCaller;
import com.ibm.wala.ipa.slicer.NormalStatement;
import com.ibm.wala.ipa.slicer.ParamCallee;
import com.ibm.wala.ipa.slicer.ParamCaller;
import com.ibm.wala.ipa.slicer.PhiStatement;
import com.ibm.wala.ipa.slicer.Statement;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.SSAAbstractThrowInstruction;
import com.ibm.wala.ssa.SSAArrayStoreInstruction;
import com.ibm.wala.ssa.SSABinaryOpInstruction;
import com.ibm.wala.ssa.SSACheckCastInstruction;
import com.ibm.wala.ssa.SSAConditionalBranchInstruction;
import com.ibm.wala.ssa.SSAGetInstruction;
import com.ibm.wala.ssa.SSAGotoInstruction;
import com.ibm.wala.ssa.SSAInstanceofInstruction;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSANewInstruction;
import com.ibm.wala.ssa.SSAPutInstruction;
import com.ibm.wala.ssa.SSAReturnInstruction;
import com.ibm.wala.ssa.SSAUnaryOpInstruction;
import com.ibm.wala.types.TypeReference;

import edu.uci.ics.jung.graph.DirectedSparseGraph;

public class GraphComparator {
	private double[][] costMatrix;
	private DirectedSparseGraph<StatementNode, StatementEdge> internalLeftGraph;
	private DirectedSparseGraph<StatementNode, StatementEdge> internalRightGraph;
	private IR internalLeftIr;
	private IR internalRightIr;
	private boolean mode;//true: does not swap left and right. false: does.
	
	protected DirectedSparseGraph<StatementNode, StatementEdge> leftGraph;
	protected DirectedSparseGraph<StatementNode, StatementEdge> rightGraph;
	protected IR leftIr;
	protected IR rightIr;
	protected Levenshtein stringComparator;
	
	
	public GraphComparator(
			DirectedSparseGraph<StatementNode, StatementEdge> oldGraph,
			IR oldIr,
			DirectedSparseGraph<StatementNode, StatementEdge> newGraph, IR newIr) {
		// TODO Auto-generated constructor stub
		if (oldGraph.getVertexCount()>newGraph.getVertexCount()){
			internalLeftGraph = newGraph;
			internalRightGraph = oldGraph;
			internalLeftIr = newIr;
			internalRightIr = oldIr;
			mode = false;
		}else{
			internalLeftGraph = oldGraph;
			internalRightGraph = newGraph;
			internalLeftIr = oldIr;
			internalRightIr = newIr;
			mode = true;
		}
		this.leftGraph = oldGraph;
		this.leftIr = oldIr;
		this.rightGraph = newGraph;
		this.rightIr = newIr;
		stringComparator = new Levenshtein();
	}
	
	public Hashtable<StatementNode, StatementNode> extractNodeMappings() {
		// TODO Auto-generated method stub
		calculateCostMatrix();
		HungarianAlgorithm ha = new HungarianAlgorithm();
        int[][] matching = ha.hgAlgorithm(costMatrix);
//		VolgenantJonker vj = new VolgenantJonker();
//      int[][] matching = vj.run(costMatrix);
        
        //mapped nodes
        Hashtable<StatementNode, StatementNode> vm = new Hashtable<StatementNode, StatementNode>();
        for(int i=0; i<matching.length; i++){
			StatementNode v1 = (StatementNode)internalLeftGraph.getVertices().toArray()[matching[i][0]];
			StatementNode v2 = (StatementNode)internalRightGraph.getVertices().toArray()[matching[i][1]];
			if(mode){
				vm.put(v1, v2);
			}else{
				vm.put(v2, v1);
			}
        }
        return vm;
	}
	
	private void calculateCostMatrix() {
		// TODO Auto-generated method stub
		costMatrix =  new double[internalLeftGraph.getVertexCount()][internalRightGraph.getVertexCount()];
		double inNodeCost;
		double outNodeCost;
		double nodeCost;
//		System.out.print("\t");
//		for (int j = 0; j < rightGraph.getVertexCount(); j++) {
//			StatementNode rightNode = (StatementNode)rightGraph.getVertices().toArray()[j];
//			System.out.print(this.getString(((NormalStatement)rightNode.statement).getInstruction())+"\t");
//		}
//		System.out.println();
		for (int i = 0; i < internalLeftGraph.getVertexCount(); i++) {
			StatementNode leftNode = (StatementNode)internalLeftGraph.getVertices().toArray()[i];
//			System.out.print(this.getString(((NormalStatement)leftNode.statement).getInstruction())+"\t");
//			if(leftNode.statement.toString().indexOf("maxDoc()I")>0){
//        		System.out.print("");
//        	}
            for (int j = 0; j < internalRightGraph.getVertexCount(); j++) {
            	StatementNode rightNode = (StatementNode)internalRightGraph.getVertices().toArray()[j];
            	inNodeCost = calculateIndegreeSimilarity(leftNode, rightNode);
            	outNodeCost = calculateOutDegreeSimilarity(leftNode, rightNode);
                nodeCost = calculateNodeCost(leftNode, rightNode);
                costMatrix[i][j] = inNodeCost+outNodeCost+nodeCost;
//                if(Double.isFinite(nodeCost)){
//                	System.out.print(inNodeCost+outNodeCost+nodeCost+"\t");
//                }else{
//                	System.out.print("na\t");
//                }
            }
//            System.out.println();
        }
	}

	private double calculateOutDegreeSimilarity(StatementNode leftNode,
			StatementNode rightNode) {
		double outNodeCost = 0;
		try{
			if((internalLeftGraph.outDegree(leftNode) + internalRightGraph.outDegree(rightNode))!=0){
				outNodeCost = (double)Math.abs(internalLeftGraph.outDegree(leftNode) -  internalRightGraph.outDegree(rightNode))/(internalLeftGraph.outDegree(leftNode) + internalRightGraph.outDegree(rightNode));
			}else{
				outNodeCost = 0;
			}
		}catch(Exception e){
//			System.out.println("jung internal error at: "+leftNode.toString());
		}
		return outNodeCost;
	}

	private double calculateIndegreeSimilarity(StatementNode leftNode,
			StatementNode rightNode) {
		double inNodeCost = 0;
		try{
			if((internalLeftGraph.inDegree(leftNode) + internalRightGraph.inDegree(rightNode))!=0){
				inNodeCost = (double)Math.abs(internalLeftGraph.inDegree(leftNode) - internalRightGraph.inDegree(rightNode))/(internalLeftGraph.inDegree(leftNode) + internalRightGraph.inDegree(rightNode));
			}else{
				inNodeCost = 0;
			}
		}catch(Exception e){
//			System.out.println("jung internal error at "+leftNode.toString());
		}
		return inNodeCost;
	}

	protected double calculateNodeCost(StatementNode leftNode,
			StatementNode rightNode) {
		// TODO Auto-generated method stub
		String leftLine;
		String rightLine;
		
		leftLine = getComparedLabel(internalLeftIr, leftNode.statement);
		rightLine = getComparedLabel(internalRightIr, rightNode.statement);
	
		double distance = stringComparator.getUnNormalisedSimilarity(leftLine, rightLine);
		int length = leftLine.length()>rightLine.length()?leftLine.length():rightLine.length();
		return distance/length;
	}
	
	


	protected double calculateCost(StatementNode v1, StatementNode v2) {
		// TODO Auto-generated method stub
		double inNodeCost = calculateIndegreeSimilarity(v1, v2);
    	double outNodeCost = calculateOutDegreeSimilarity(v1, v2);
        double nodeCost = calculateNodeCost(v1, v2);
        return inNodeCost+outNodeCost+nodeCost;
	}
	
	

	
	public static String getComparedLabel(IR ir, Statement s) {
		// TODO Auto-generated method stub
		
		String line = "";
		switch (s.getKind()) {
	        case HEAP_PARAM_CALLEE:
	        case HEAP_PARAM_CALLER:
	        case HEAP_RET_CALLEE:
	        case HEAP_RET_CALLER:
	          HeapStatement h = (HeapStatement) s;
	          line = s.getKind() + "\\n" + h.getNode();
	          break;
	        case NORMAL:
	          NormalStatement n = (NormalStatement) s;
	          SSAInstruction ins = n.getInstruction();
	          line = getComparedInstructionString(ir, ins);
	          break;
	        case PARAM_CALLEE:
	          ParamCallee paramCallee = (ParamCallee) s;
	          line = s.getKind() + " " + paramCallee.getValueNumber();
	          break;
	        case PARAM_CALLER:
	          ParamCaller paramCaller = (ParamCaller) s;
	          line = s.getKind() + " " + paramCaller.getValueNumber();
	          break;	      
	        case EXC_RET_CALLER:
	        	line = s.toString();
	        	break;
	        case PHI:
	        	PhiStatement phi = (PhiStatement)s;
	        	line = phi.getPhi().toString();
	        	break;	
	        case NORMAL_RET_CALLER:
	        	NormalReturnCaller caller = (NormalReturnCaller)s;
	        	line = "NORMAL_RET_CALLER:" + getComparedInstructionString(ir, caller.getInstruction());
	        	break;	
	        case EXC_RET_CALLEE:
	        case NORMAL_RET_CALLEE:
	        default:
	          line =  s.toString();
	     }
		 return line;
	}
	

	
	public static String getComparedInstructionString(IR ir, SSAInstruction ins) {
		String line;
		if(ins instanceof AstJavaInvokeInstruction){
			  AstJavaInvokeInstruction aji = (AstJavaInvokeInstruction)ins;
			  CallSiteReference site = aji.getCallSite();
			  line = "invoke "+site.getInvocationString() + " ";
			  line = line + site.getDeclaredTarget().toString();
		  }else if (ins instanceof SSANewInstruction){
			  SSANewInstruction nis = (SSANewInstruction)ins;
			  NewSiteReference site = nis.getNewSite();
			  line = "new " + site.getDeclaredType();
		  }else if(ins instanceof SSAPutInstruction){
			  SSAPutInstruction pis = (SSAPutInstruction)ins;
			  if (pis.isStatic()) {
			      line = "putstatic " + pis.getDeclaredField() + " = " + pis.getValueString(null, pis.getVal());
			  } else {
			      line =  "putfield " + pis.getDeclaredField();
			  }
//			  String value = ins.getValueString(ir.getSymbolTable(), pis.getVal());
//			  if(value.indexOf("#")>0){
//				  line = line + "= "+value; 
//			  }
		  }else if(ins instanceof SSAGetInstruction){
			  SSAGetInstruction gis = (SSAGetInstruction)ins;
			  if (gis.isStatic()) {
			      line = "getstatic " + gis.getDeclaredField();
			  } else {
			      line =  "getfield " + gis.getDeclaredField();
			  }
//			  String value = ins.getValueString(ir.getSymbolTable(), gis.getRef());
//			  if(value.indexOf("#")>0){
//				  line = line + "= "+value; 
//			  }
		  }else if(ins instanceof SSABinaryOpInstruction){
			  SSABinaryOpInstruction ois = (SSABinaryOpInstruction)ins;
//			  line = ois.toString(ir.getSymbolTable());
			  line = "binaryop(" + ois.getOperator() + ") ";
		  }else if(ins instanceof SSAArrayStoreInstruction){
			  line = "arraystore";
		  }else if(ins instanceof SSAUnaryOpInstruction){
			  SSAUnaryOpInstruction uoi = (SSAUnaryOpInstruction)ins;
			  line = uoi.getOpcode().toString();
		  }else if(ins instanceof SSAGotoInstruction){
			  line = "goto";
		  }else if(ins instanceof AstAssertInstruction){
			  line = "assert"; 
		  }else if(ins instanceof SSAConditionalBranchInstruction){
			  SSAConditionalBranchInstruction cbi = (SSAConditionalBranchInstruction)ins;
			  line = "conditional branch(" + cbi.getOperator() + ") ";
		  }else if(ins instanceof SSAInstanceofInstruction){
			  SSAInstanceofInstruction iis = (SSAInstanceofInstruction)ins;
			  line = "instanceof " + iis.getCheckedType();
		  }else if(ins instanceof SSACheckCastInstruction){
			  SSACheckCastInstruction cci = (SSACheckCastInstruction)ins;
			  line = "checkcast";
		      for (TypeReference t : cci.getDeclaredResultTypes()) {
		          line = line + " " + t;
		      }
		  }else if(ins instanceof SSAAbstractThrowInstruction){
			  line = "throw";
		  }else{
			  line = ins.toString(ir.getSymbolTable());
//			  System.err.println(line);
		  }
		  return line;
	}
	
	public static String getVisualLabel(IR ir, Statement s) {
		// TODO Auto-generated method stub
		String line = "";
		 switch (s.getKind()) {
	        case HEAP_PARAM_CALLEE:
	        case HEAP_PARAM_CALLER:
	        case HEAP_RET_CALLEE:
	        case HEAP_RET_CALLER:
	          HeapStatement h = (HeapStatement) s;
	          line = s.getKind() + "\\n" + h.getNode();
	          break;
	        case NORMAL:
	          NormalStatement n = (NormalStatement) s;
	          SSAInstruction ins = n.getInstruction();
	          line = getInstructionVisualString(ir, ins);
	          break;
	        case PARAM_CALLEE:
	          ParamCallee paramCallee = (ParamCallee) s;
	          line = s.getKind() + " " + paramCallee.getValueNumber();
	          break;
	        case PARAM_CALLER:
	          ParamCaller paramCaller = (ParamCaller) s;
	          line = s.getKind() + " " + paramCaller.getValueNumber();
	          break;	      
	        case EXC_RET_CALLER:
	        	line = s.toString();
	        	break;
	        case PHI:
	        	PhiStatement phi = (PhiStatement)s;
	        	line = phi.getPhi().toString();
	        	break;	
	        case NORMAL_RET_CALLER:
	        	NormalReturnCaller caller = (NormalReturnCaller)s;
	        	line = "NORMAL_RET_CALLER:" + getInstructionVisualString(ir, caller.getInstruction());
	        	break;	
	        case EXC_RET_CALLEE:
	        case NORMAL_RET_CALLEE:
	        default:
	          line =  s.toString();
	        }
		 return line;
	}

	public static String getInstructionVisualString(IR ir, SSAInstruction ins) {
		String line;
		if(ins instanceof AstJavaInvokeInstruction){
			  AstJavaInvokeInstruction aji = (AstJavaInvokeInstruction)ins;
			  CallSiteReference site = aji.getCallSite();
			  line = "invoke "+site.getInvocationString() + " ";
			  line += site.getDeclaredTarget().toString();
			  line += " @" + site.getProgramCounter();
		  }else if (ins instanceof SSANewInstruction){
			  SSANewInstruction nis = (SSANewInstruction)ins;
			  NewSiteReference site = nis.getNewSite();
			  line = "new " + site.getDeclaredType();
			  line += " @" + site.getProgramCounter();
		  }else if(ins instanceof SSAPutInstruction){
//			  SSAPutInstruction pis = (SSAPutInstruction)ins;
//			  if (pis.isStatic()) {
//			      line = "putstatic " + pis.getDeclaredField() + " = " + pis.getValueString(null, pis.getVal());
//			  } else {
//			      line =  "putfield " + pis.getDeclaredField();
//			  }
//			  String value = ins.getValueString(ir.getSymbolTable(), pis.getVal());
//			  if(value.indexOf("#")>0){
//				  line = line + "= "+value; 
//			  }
			  line = ins.toString(ir.getSymbolTable());
			  
		  }else if(ins instanceof SSAGetInstruction){
//			  SSAGetInstruction gis = (SSAGetInstruction)ins;
//			  if (gis.isStatic()) {
//			      line = "getstatic " + gis.getDeclaredField();
//			  } else {
//			      line =  "getfield " + gis.getDeclaredField();
//			  }
//			  String value = ins.getValueString(ir.getSymbolTable(), gis.getRef());
//			  if(value.indexOf("#")>0){
//				  line = line + "= "+value; 
//			  }
			  line = ins.toString(ir.getSymbolTable());
		  }else if(ins instanceof SSABinaryOpInstruction){
			  SSABinaryOpInstruction ois = (SSABinaryOpInstruction)ins;
			  line = ois.toString(ir.getSymbolTable());
		  }else if(ins instanceof SSAArrayStoreInstruction){
			  line = ins.toString(ir.getSymbolTable());
		  }else if(ins instanceof SSAUnaryOpInstruction){
			  SSAUnaryOpInstruction uoi = (SSAUnaryOpInstruction)ins;
			  line = uoi.getOpcode().toString();
		  }else if(ins instanceof SSAGotoInstruction){
			  SSAGotoInstruction goi = (SSAGotoInstruction)ins;
			  line = goi.toString(ir.getSymbolTable());
		  }else if(ins instanceof AstAssertInstruction){
			  line = ins.toString(ir.getSymbolTable());
		  }else if(ins instanceof SSAConditionalBranchInstruction){
			  SSAConditionalBranchInstruction cbi = (SSAConditionalBranchInstruction)ins;
			  line = cbi.toString(ir.getSymbolTable());
		  }else if(ins instanceof SSAInstanceofInstruction){
//			  SSAInstanceofInstruction iis = (SSAInstanceofInstruction)ins;
			  line = ins.toString(ir.getSymbolTable());
		  }else if(ins instanceof SSACheckCastInstruction){
//			  SSACheckCastInstruction cci = (SSACheckCastInstruction)ins;
			  line = ins.toString(ir.getSymbolTable());
		  }else{
			  line = ins.toString();
//			  System.err.println(line);
		  }
		return line;
	}
}
