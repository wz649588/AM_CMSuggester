package org.eclipse.jdt.internal.compiler.ast;

import org.eclipse.jdt.internal.compiler.ASTVisitor;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;

/**
 * An ASTVisitor for debugging
 * @author Ye Wang
 * @since 02/03/2018
 *
 */
public class DebugVisitor extends ASTVisitor {

	
	@Override
	public boolean visit(AllocationExpression node, BlockScope scope) {
		if (node.toString().contains("AutoSavingKeyCache")) {
			System.out.println(node);
		}
		
		return super.visit(node, scope);
	}
}
