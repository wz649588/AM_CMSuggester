package edu.vt.cs.prediction.neo;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.Statement;


/**
 * Find the statements near the 
 * @author Ye Wang
 * @since 06/09/2017
 *
 */
public class NearStmtFinder {

	private ASTNode method;
	
	private String afName;
	
	private String classSig;
	
	private List<ASTNode> aboves = new ArrayList<>();
	
	private List<ASTNode> belows = new ArrayList<>();
	
	public NearStmtFinder(ASTNode method, String afName, String classSig) {
		this.method = method;
		this.afName = afName;
		this.classSig = classSig;
	}
	
	public List<ASTNode> getAboves() {
		return aboves;
	}
	
	public List<ASTNode> getBelows() {
		return belows;
	}
	
	public void execute() {
		// Get the leaf statements in the method
		LeafStatementFinder leafFinder = new LeafStatementFinder(method);
		leafFinder.execute();
		List<ASTNode> leaves = leafFinder.getLeaves();
		
		// Get the first statement that contains AF
		ASTNode afStatement = null;
		for (ASTNode stmt: leaves) {
			AFStatementChecker checker = new AFStatementChecker(stmt, afName, classSig);
			if (checker.containsAF()) {
				afStatement = stmt;
				break;
			}
		}
		
		// Get the 2 statements above AF statement and the 2 statements below AF statement
		if (afStatement != null) {
			int afIndex = leaves.indexOf(afStatement);
			if (afIndex - 2 >= 0)
				aboves.add(leaves.get(afIndex - 2));
			if (afIndex - 1 >= 0)
				aboves.add(leaves.get(afIndex - 1));
			if (afIndex + 1 < leaves.size())
				belows.add(leaves.get(afIndex + 1));
			if (afIndex + 2 < leaves.size())
				belows.add(leaves.get(afIndex + 2));
		}
	}
	
}
