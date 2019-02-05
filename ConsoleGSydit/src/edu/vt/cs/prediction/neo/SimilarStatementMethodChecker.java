package edu.vt.cs.prediction.neo;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jdt.core.dom.ASTNode;

import edu.vt.cs.editscript.common.LongestCommonSubseq;

/**
 * Check if the method has textually similar statements
 * @author Ye Wang
 * @since 07/10/2017
 *
 */
public class SimilarStatementMethodChecker {

	private ASTNode method;
	
	private List<ASTNode> aboves;
	
	private List<ASTNode> belows;
	
	private List<String> codeLines;
	
	private double similarityThreshold = 0.75;
	
	private boolean fHasSimilarStatements = false;
	
	
	public SimilarStatementMethodChecker(ASTNode method, List<ASTNode> aboves, List<ASTNode> belows) {
		this.method = method;
		this.aboves = aboves;
		this.belows = belows;
	}
	
	private void check(List<ASTNode> refs) {
		List<String> refLines = new ArrayList<>();
		for (ASTNode node: refs) {
			String line = ASTNodeToString.convert(node);
			refLines.add(line);
		}
		for (int i = 0; i < codeLines.size() - 1; i++) {
			String code = codeLines.get(i);
			if (isSimilar(refLines.get(0), code) && isSimilar(refLines.get(1), code)) {
				fHasSimilarStatements = true;
				return;
			}
		}
	}
	
	private boolean isSimilar(String a, String b) {
		LongestCommonSubseq<Character> lcs = new LongestCommonSubseq<>(toCharList(a), toCharList(b));
		List<Character> common = lcs.getResultList();
		return ((double) common.size()) / a.length() >= similarityThreshold
				&& ((double) common.size()) / b.length() >= similarityThreshold;
	}
	
	private List<Character> toCharList(String s) {
		List<Character> list = new ArrayList<>();
		for (char c: s.toCharArray()) {
			list.add(c);
		}
		return list;
	}
	
	public boolean hasSimilarStatements() {
		return fHasSimilarStatements;
	}
	
	public void execute() {
		LeafStatementFinder leafFinder = new LeafStatementFinder(method);
		leafFinder.execute();
		List<ASTNode> leaves = leafFinder.getLeaves();
		
		codeLines = new ArrayList<>();
		for (ASTNode node: leaves) {
			String line = ASTNodeToString.convert(node);
			codeLines.add(line);
		}
		
		if (aboves.size() == 2) {
			check(aboves);
		}
		
		if (!fHasSimilarStatements && aboves.size() >= 1 && belows.size() >= 1) {
			List<ASTNode> refs = new ArrayList<>();
			refs.add(aboves.get(aboves.size() - 1));
			refs.add(belows.get(0));
			check(refs);
		}
		
		if (!fHasSimilarStatements && belows.size() == 2) {
			check(belows);
		}
		
	}
	
	
}
