package edu.vt.cs.graph;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.eclipse.jdt.core.SourceRange;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.MethodDeclaration;

import com.ibm.wala.ipa.slicer.StatementWithInstructionIndex;
import com.ibm.wala.ssa.SSAInstruction;

public class LineMapper {

	private Map<Integer, List<ASTNode>> lineToAsts = null;
	private Map<MethodDeclaration, SourceRange> methodToRange = null;
	
	public LineMapper(Map<Integer, List<ASTNode>> lineToAsts, 
			Map<MethodDeclaration, SourceRange> methodToRange) {
		this.lineToAsts = lineToAsts;
		this.methodToRange = methodToRange;			
	}
	
	public ASTNode findEnclosingMethod(int lineNum) {
		int maxDistance = Integer.MAX_VALUE;
		int tmpDistance = 0;
		MethodDeclaration md = null;
		for (Entry<MethodDeclaration, SourceRange> entry : methodToRange.entrySet()) {
			tmpDistance = Math.abs(lineNum - entry.getValue().getOffset()); 
			if (tmpDistance < maxDistance) {
				md = entry.getKey();
				maxDistance = tmpDistance; 
			}
		}
		return md;
	}
	
	/**
	 * Here we have conservative estimation to reduce complexity of inferring ASTNodes based on line numbers
	 * @param lineNum
	 * @param statement
	 * @return
	 */
	public List<ASTNode> findNodes(int lineNum) {
		List<ASTNode> asts = lineToAsts.get(lineNum);
		if (asts == null) {
			System.err.println("lineNum = " + lineNum);
			return null;
		}		
		return asts;
	}
	
	
}
