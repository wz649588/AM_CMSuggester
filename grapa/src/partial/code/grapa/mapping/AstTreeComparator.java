package partial.code.grapa.mapping;

import java.util.ArrayList;
import java.util.Hashtable;
import java.util.List;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.MethodDeclaration;

import com.ibm.wala.util.collections.Pair;

import partial.code.grapa.delta.graph.HungarianAlgorithm;
import partial.code.grapa.dependency.graph.StatementNode;
import uk.ac.shef.wit.simmetrics.similaritymetrics.Levenshtein;

public class AstTreeComparator {
	private boolean mode;//true: does not swap left and right. false: does.
	private ArrayList<ASTNode> leftTrees;
	private ArrayList<ASTNode> rightTrees;
	protected Levenshtein stringComparator = new Levenshtein();
	
	public AstTreeComparator(ArrayList<ASTNode> leftTrees,
			ArrayList<ASTNode> rightTrees) {
		// TODO Auto-generated constructor stub
		this.leftTrees = leftTrees;
		this.rightTrees = rightTrees;
	}

	public List<Pair<ClientMethod, ClientMethod>> extractMappings() {
		// TODO Auto-generated method stub
		Hashtable<ASTNode, ASTNode> nm = extractNodeMapping();
		List<Pair<ClientMethod, ClientMethod>> mms = new ArrayList<Pair<ClientMethod, ClientMethod>>();
		for(ASTNode leftTree:leftTrees){
			ASTNode rightTree = nm.get(leftTree);
			if(rightTree!=null){
				Hashtable<ClientMethod, ClientMethod> mm = extractMethodMapping(leftTree, rightTree);
				if(mm!=null){
					for(ClientMethod m1:mm.keySet()){
						ClientMethod m2 = mm.get(m1);
						if(m1.methodbody.toString().compareTo(m2.methodbody.toString())!=0){	
							mms.add(new Pair<ClientMethod, ClientMethod>(m1, m2));
						}
					}
				}
			}
		}		
		return mms;
	}

	private Hashtable<ClientMethod, ClientMethod> extractMethodMapping(
			ASTNode leftTree, ASTNode rightTree) {
		// TODO Auto-generated method stub
		ClientMethodVisitor visitor = new ClientMethodVisitor();
		leftTree.accept(visitor);
		ArrayList<ClientMethod> leftMethods = new ArrayList<ClientMethod>();
		leftMethods.addAll(visitor.methods);
		
		visitor.clear();
		rightTree.accept(visitor);
		ArrayList<ClientMethod> rightMethods = new ArrayList<ClientMethod>();
		rightMethods.addAll(visitor.methods);
		
		if(leftMethods.size()==0||rightMethods.size()==0){
			return null;
		}		
		
		ArrayList<ClientMethod> internalLeftMethods;
		ArrayList<ClientMethod> internalRightMethods;
		if(leftMethods.size()>rightMethods.size()){
			mode = false;
			internalLeftMethods = rightMethods;
			internalRightMethods = leftMethods;
		}else{
			mode = true;
			internalLeftMethods = leftMethods;
			internalRightMethods = rightMethods;
		}
		double[][] costMatrix = calculateMethodCostMatrix(internalLeftMethods, internalRightMethods);
		HungarianAlgorithm ha = new HungarianAlgorithm();
        int[][] matching = ha.hgAlgorithm(costMatrix);
        
        Hashtable<ClientMethod, ClientMethod> nm = new Hashtable<ClientMethod, ClientMethod>();
        for(int i=0; i<matching.length; i++){
        	ClientMethod v1 = internalLeftMethods.get(matching[i][0]);
        	ClientMethod v2 = internalRightMethods.get(matching[i][1]);
	        if(mode){
	        	nm.put(v1, v2);
	        }else{
	        	nm.put(v2, v1);
	        }
        }
		return nm;
	}

	private double[][] calculateMethodCostMatrix(
			ArrayList<ClientMethod> internalLeftMethods,
			ArrayList<ClientMethod> internalRightMethods) {
		// TODO Auto-generated method stub
		double[][] costMatrix =  new double[internalLeftMethods.size()][internalRightMethods.size()];
		
		for (int i = 0; i < internalLeftMethods.size(); i++) {
			ClientMethod leftNode = internalLeftMethods.get(i);
            for (int j = 0; j < internalRightMethods.size(); j++) {
            	ClientMethod rightNode = internalRightMethods.get(j);
            	String leftLine = leftNode.getTypeName()+"."+leftNode.getSignature();
            	String rightLine = rightNode.getTypeName()+"."+rightNode.getSignature();
                costMatrix[i][j] = stringComparator.getUnNormalisedSimilarity(leftLine, rightLine);;
            }
        }
		return costMatrix;
	}

	private Hashtable<ASTNode, ASTNode> extractNodeMapping() {
		ArrayList<ASTNode> internalLeftTrees;
		ArrayList<ASTNode> internalRightTrees;
		if(leftTrees.size()>rightTrees.size()){
			mode = false;
			internalLeftTrees = rightTrees;
			internalRightTrees = leftTrees;
		}else{
			mode = true;
			internalLeftTrees = leftTrees;
			internalRightTrees = rightTrees;
		}
		double[][] costMatrix = calculateAstNodeCostMatrix(internalLeftTrees, internalRightTrees);
		HungarianAlgorithm ha = new HungarianAlgorithm();
        int[][] matching = ha.hgAlgorithm(costMatrix);
        
        Hashtable<ASTNode, ASTNode> nm = new Hashtable<ASTNode, ASTNode>();
        for(int i=0; i<matching.length; i++){
        	ASTNode v1 = internalLeftTrees.get(matching[i][0]);
        	ASTNode v2 = internalRightTrees.get(matching[i][1]);
	        if(mode){
	        	nm.put(v1, v2);
	        }else{
	        	nm.put(v2, v1);
	        }
        }
		return nm;
	}

	private double[][] calculateAstNodeCostMatrix(
			ArrayList<ASTNode> internalLeftTrees,
			ArrayList<ASTNode> internalRightTrees) {
		// TODO Auto-generated method stub
		double[][] costMatrix =  new double[internalLeftTrees.size()][internalRightTrees.size()];
	
		for (int i = 0; i < internalLeftTrees.size(); i++) {
			ASTNode leftNode = internalLeftTrees.get(i);
            for (int j = 0; j < internalRightTrees.size(); j++) {
            	ASTNode rightNode = internalRightTrees.get(j);
            	String leftLine = ((CompilationUnit)leftNode).getTypeRoot().getElementName();
            	String rightLine = ((CompilationUnit)rightNode).getTypeRoot().getElementName();
                costMatrix[i][j] = stringComparator.getUnNormalisedSimilarity(leftLine, rightLine);;
            }
        }
		return costMatrix;
	}

}
