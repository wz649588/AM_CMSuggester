package org.eclipse.jdt.core.dom;

import java.util.List;
import java.util.ArrayList;


//added by nameng. If the original bindingResolver does not work correctly, do not continue any process 
public class SanityCheck extends ASTVisitor{

	List<SanityCheckException> exps = new ArrayList<SanityCheckException>();
	
//	@Override
//	public boolean visit(ClassInstanceCreation node) {
// 		if (exps.isEmpty()) {
// 			IMethodBinding mb = node.resolveConstructorBinding();
// 			if (mb != null) {
// 				ITypeBinding[] paramBs = mb.getParameterTypes();
// 				List<ASTNode> args = node.arguments();
// 				if (!mb.isVarargs() && args.size() != paramBs.length) {
// 					exps.add(new SanityCheckException("constructor method invocation is bound wrongly"));
// 				} else {
// 					
// 				}
// 			}
// 		}		
//		return super.visit(node);
//	}
	
	@Override
	public boolean visit(SuperConstructorInvocation node) {
		if (exps.isEmpty()) {
			IMethodBinding mb = node.resolveConstructorBinding();
			if (mb != null) {
				ITypeBinding[] paramBs = mb.getParameterTypes();
				List<ASTNode> args = node.arguments();
				if (!mb.isVarargs() && args.size() != paramBs.length) {
					exps.add(new SanityCheckException("super method invocation is bound wrongly"));
				}
			}
		}		
		return super.visit(node);
	}
	
	@Override
	public boolean visit(SuperMethodInvocation node) {
		if (exps.isEmpty()) {
			IMethodBinding mb = node.resolveMethodBinding();
			if (mb != null) {
				ITypeBinding[] paramBs = mb.getParameterTypes();
				List<ASTNode> args = node.arguments();
				if (!mb.isVarargs() && args.size() != paramBs.length) {
					exps.add(new SanityCheckException("super method invocation is bound wrongly"));
				}
			}
		}		
		return super.visit(node);
	}
	
	public boolean hasException() {
		return !exps.isEmpty();
	}
}
