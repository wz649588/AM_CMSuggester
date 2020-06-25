package org.eclipse.jdt.core.dom;

public class TestVisitor extends ASTVisitor {

	@Override
	public boolean visit(Assignment node) { //added by nameng, to test the Assignment
//		ITypeBinding type = node.resolveTypeBinding();
//		if (type == null) {
//			System.out.println("left = " + node.getLeftHandSide().resolveTypeBinding());
//			System.out.println("right = " + node.getRightHandSide().resolveTypeBinding());
//		}
//		System.out.println(type.getQualifiedName());
		return super.visit(node);
	}
	
	@SuppressWarnings("unused")
	@Override
	public boolean visit(ClassInstanceCreation node) {
		if (node.toString().equals("new ConcurrentLinkedHashMap.Builder<K,V>()")) {
			IMethodBinding mBinding = node.resolveConstructorBinding();
			mBinding = null;
		}
//		if (node.toString().contains("AutoSavingKeyCache")) {
//			System.out.println(node.resolveTypeBinding());
//			IMethodBinding mBinding = node.resolveConstructorBinding();
//			ITypeBinding binding = node.resolveTypeBinding();
//			ITypeBinding dClass = mBinding.getDeclaringClass();
//			Expression exp = node.getExpression();
//		}
		return super.visit(node);
	}
	
	@Override
	public boolean visit(InfixExpression node) {
//		ITypeBinding type = node.resolveTypeBinding();
//		if (type == null) {
//			System.out.println("unresolved");			
//		} else {
//			System.out.println(type.toString());
//		}
		return super.visit(node);
	}
	
	@Override
	public boolean visit(MethodDeclaration node) {
		// TODO Auto-generated method stub
//		if(node.toString().indexOf("assertUnorderedResultSet")>=0){
//			IMethodBinding nodeB = node.resolveBinding();
//			System.out.println(nodeB.getKey());
//			ITypeBinding typeB = nodeB.getDeclaringClass();
//			System.out.println(typeB.getQualifiedName());
//		}
		return super.visit(node);
	}
	@Override
	public boolean visit(TypeLiteral node) {
		// TODO Auto-generated method stub
//		if(node.toString().indexOf("InitialContextFactory.class")>=0){
//			ITypeBinding nodeB = node.resolveTypeBinding();
//			if(nodeB==null){
//				System.out.println("NULL");
//			}
////			System.out.println("Here");
//		}
		return super.visit(node);
	}
	@Override
	public boolean visit(MethodInvocation node) {
		if (node.toString().equals("new ConcurrentLinkedHashMap.Builder<K,V>().weigher(weigher)")) {
			IMethodBinding binding = node.resolveMethodBinding();
			System.out.println();
			
		}
		// TODO Auto-generated method stub
//		  String t = node.toString();
//		    if(t.indexOf("MessageService.getTextMessage")>=0){
//		      IMethodBinding nodeB = node.resolveMethodBinding();
//		      System.out.println(node.resolveTypeBinding());
//		      System.out.println(nodeB);
//		    }
//		if (node.toString().contains("AutoSavingKeyCache")) {
//			System.out.println(node);
//		}
//		System.out.println(node);
	    return super.visit(node);
	}
	
//	@Override
//	public boolean visit(QualifiedName node) {		
//		if (node.toString().contains("TYPE_FORWARD_ONLY")) {
//			IBinding nodeB = node.resolveBinding();
//		      if(nodeB instanceof IVariableBinding){
//		    	  IVariableBinding varB = (IVariableBinding)nodeB;
//		    	  ITypeBinding type = varB.getDeclaringClass();
//		    	  System.out.println(node.toString());
//		    	  System.out.println(type.toString());
//		    	  System.out.println(node.resolveBinding());
//		      }			
//		}
//		return super.visit(node);
//	}
	
	@Override
	public boolean visit(SimpleName node) {
//		if (!(node.getParent() instanceof TypeDeclaration)) {
//			if (node.toString().equals("DatabaseDescriptor") 
//					&& node.getParent().toString().contains("DatabaseDescriptor.hintedHandoffEnabled")) {
//				IBinding binding = node.resolveBinding();
//				if (binding instanceof ITypeBinding) {
//					ITypeBinding dc = ((ITypeBinding) binding).getDeclaringClass();
//					System.out.println();
//				}
//			}
//			if (node.toString().equals("LoggerFactory")
//					&& node.getParent().toString().contains("LoggerFactory.getLogger")) {
//				IBinding binding = node.resolveBinding();
//				System.out.println();
//			}
//			if (node.toString().equals("localDataCenter")) {
//				IVariableBinding binding = (IVariableBinding)node.resolveBinding();
//				boolean isParameter = binding.isParameter();
//				boolean isEnumConstant = binding.isEnumConstant();
//				boolean isField = binding.isField();
//				ASTNode parent = node.getParent();
//				System.out.println(parent);
//			}
//		}
		return super.visit(node);
	}
	
	@Override
	public boolean visit(SuperMethodInvocation node) {
//		IMethodBinding mb = node.resolveMethodBinding();
//		if (mb != null) {
//			System.out.println(mb.getDeclaringClass().getQualifiedName());
//			IMethodBinding[] mbs = mb.getDeclaringClass().getDeclaredMethods();
//			System.out.println(mb.getMethodDeclaration().toString());
//		}
		return super.visit(node);
	}
	
	@Override
	public boolean visit(PrefixExpression node) {
		if (node.toString().contains("!command.isDigestQuery()")) {
			MethodInvocation mi = (MethodInvocation) node.getOperand();
			SimpleName name = (SimpleName) mi.getExpression();
			IVariableBinding binding = (IVariableBinding) name.resolveBinding();
//			boolean isParameter = binding.isParameter();
//			boolean isEnumConstant = binding.isEnumConstant();
//			boolean isField = binding.isField();
			if (binding != null) {
				ITypeBinding tbinding = binding.getDeclaringClass();
			}
		}
		return super.visit(node);
	}
}
