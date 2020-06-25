package ca.mcgill.cs.swevo.ppa.inference;

import java.util.List;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.AbstractInferenceStrategy;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.eclipse.jdt.core.dom.PPABindingsUtil;
import org.eclipse.jdt.core.dom.PPADefaultBindingResolver;
import org.eclipse.jdt.core.dom.PPAEngine;
import org.eclipse.jdt.core.dom.PPATypeRegistry;
import org.eclipse.jdt.core.dom.SimpleName;

import ca.mcgill.cs.swevo.ppa.PPAIndex;
import ca.mcgill.cs.swevo.ppa.PPAIndexer;
import ca.mcgill.cs.swevo.ppa.TypeFact;

public class SimpleNameInferenceStrategy extends AbstractInferenceStrategy {

	public SimpleNameInferenceStrategy(PPAIndexer indexer, PPAEngine ppaEngine) {
		super(indexer, ppaEngine);
		// TODO Auto-generated constructor stub
	}

	@Override
	public boolean isSafe(ASTNode node) {
		// TODO Auto-generated method stub
		boolean isSafe = true;
		SimpleName sn = (SimpleName)node;
		ITypeBinding snb = sn.resolveTypeBinding();
		if(snb==null){
			isSafe = false;
		}else{
			isSafe = !PPABindingsUtil.isUnknownType(snb);//modified by nameng, isUnknownType(snb)should be considered as unsafe, right? 
		}
		return isSafe;
	}

	@Override
	public void inferTypes(ASTNode node) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void makeSafe(ASTNode node, TypeFact typeFact) {
		// TODO Auto-generated method stub
		fixWithFact(node, typeFact);
	}

	private void fixWithFact(ASTNode node, TypeFact typeFact) {
		// TODO Auto-generated method stub
		SimpleName sn = (SimpleName)node;
		PPATypeRegistry typeRegistry = ppaEngine.getRegistry();
		PPADefaultBindingResolver resolver = getResolver(sn);
		ITypeBinding snb = sn.resolveTypeBinding();
		ITypeBinding newType = typeFact.getNewType();
		if(PPABindingsUtil.getSafetyValue(snb)<PPABindingsUtil.getSafetyValue(newType)){
			ITypeBinding dcc = null;
			if(snb!=null){
				dcc = snb.getDeclaringClass();
			}
			if(dcc==null){
				dcc = typeRegistry.getUnknownBinding(resolver);
			}
			if (resolver.isSimpleNameRef(sn)|| resolver.isFieldReference(sn)||resolver.isQualifiedNameReference(sn)) {
				IVariableBinding newBinding = typeRegistry.getFieldBindingWithType(
						sn.getIdentifier(), dcc, newType, resolver);
				resolver.fixFieldBinding(sn, newBinding);
			}
		}
	}

	@Override
	public void makeSafeSecondary(ASTNode node, TypeFact typeFact) {
		// TODO Auto-generated method stub
		fixWithFact(node, typeFact);
	}
}
