package ca.mcgill.cs.swevo.ppa.inference;

import java.util.List;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.AbstractInferenceStrategy;
import org.eclipse.jdt.core.dom.Expression;
import org.eclipse.jdt.core.dom.IBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.eclipse.jdt.core.dom.Name;
import org.eclipse.jdt.core.dom.PPABindingsUtil;
import org.eclipse.jdt.core.dom.PPADefaultBindingResolver;
import org.eclipse.jdt.core.dom.PPAEngine;
import org.eclipse.jdt.core.dom.PPATypeRegistry;
import org.eclipse.jdt.core.dom.SimpleName;
import org.eclipse.jdt.core.dom.SwitchCase;
import org.eclipse.jdt.core.dom.SwitchStatement;

import ca.mcgill.cs.swevo.ppa.PPAIndex;
import ca.mcgill.cs.swevo.ppa.PPAIndexer;
import ca.mcgill.cs.swevo.ppa.TypeFact;


public class SwitchStatementInferenceStrategy  extends AbstractInferenceStrategy {

	

	public SwitchStatementInferenceStrategy(PPAIndexer indexer,
			PPAEngine ppaEngine) {
		super(indexer, ppaEngine);
		// TODO Auto-generated constructor stub
	}

	

	@Override
	public boolean isSafe(ASTNode node) {
		// TODO Auto-generated method stub
		SwitchStatement sws = (SwitchStatement)node;
		Expression exp = sws.getExpression();
		boolean isSafe = PPABindingsUtil.getSafetyValue(exp.resolveTypeBinding()) > PPABindingsUtil.MISSING_TYPE;
		if(isSafe){
			for(Object o:sws.statements()){
				if(o instanceof SwitchCase){
					SwitchCase sc = (SwitchCase)o;
					if(sc.getExpression()!=null){
						isSafe = PPABindingsUtil.getSafetyValue(sc.getExpression().resolveTypeBinding()) > PPABindingsUtil.MISSING_TYPE;
						if(!isSafe){
							break;
						}
					}
					
				}
			}
		}
		return isSafe;
	}

	@Override
	public void inferTypes(ASTNode node) {
		// TODO Auto-generated method stub
		SwitchStatement sws = (SwitchStatement)node;
		Expression exp = sws.getExpression();
		ITypeBinding newBinding = null;
		if(PPABindingsUtil.getSafetyValue(exp.resolveTypeBinding()) > PPABindingsUtil.UNKNOWN_TYPE){
			newBinding = exp.resolveTypeBinding();
		}
	
		for(Object o:sws.statements()){
			if(o instanceof SwitchCase){
				SwitchCase sc = (SwitchCase)o;
				exp = sc.getExpression();
				if(exp!=null&&PPABindingsUtil.getSafetyValue(sc.getExpression().resolveTypeBinding()) > PPABindingsUtil.getSafetyValue(newBinding)){
					newBinding = sc.getExpression().resolveTypeBinding();
				}
			}
		}
		if(newBinding!=null){
			TypeFact tFact = new TypeFact(indexer.getMainIndex(node), null,
					TypeFact.UNKNOWN, newBinding, TypeFact.RELATED, TypeFact.ASSIGN_STRATEGY);
			ppaEngine.reportTypeFact(tFact);
		}
	}

	@Override
	public void makeSafe(ASTNode node, TypeFact typeFact) {
		// TODO Auto-generated method stub
		SwitchStatement sws = (SwitchStatement)node;
		Expression exp = sws.getExpression();
		if(exp instanceof Name){
			fixName(typeFact, exp);
		}
		for(Object o:sws.statements()){
			if(o instanceof SwitchCase){
				SwitchCase sc = (SwitchCase)o;
				exp = sc.getExpression();
				if(exp instanceof Name){
					fixName(typeFact, exp);
				}
			}
		}
	}



	private void fixName(TypeFact typeFact, Expression exp) {
		Name sn = (Name)exp;
		PPATypeRegistry typeRegistry = ppaEngine.getRegistry();
		PPADefaultBindingResolver resolver = getResolver(sn);
		IVariableBinding varBinding = null;
		try{//the try-catch is added by nameng because jdt can throw exception when resolving the binding
			varBinding = (IVariableBinding) sn.resolveBinding();
		} catch(Exception e){
			//do nothing
		}		
		if(varBinding!=null&&PPABindingsUtil.isUnknownType(varBinding.getType())){
			ITypeBinding newType = typeFact.getNewType();
			IVariableBinding newBinding = typeRegistry.getFieldBindingWithType(
					varBinding.getName(), varBinding.getDeclaringClass(), newType, resolver);
			resolver.fixFieldBinding(sn, newBinding);
		}
	}

	@Override
	public void makeSafeSecondary(ASTNode node, TypeFact typeFact) {
		// TODO Auto-generated method stub

	}

}
