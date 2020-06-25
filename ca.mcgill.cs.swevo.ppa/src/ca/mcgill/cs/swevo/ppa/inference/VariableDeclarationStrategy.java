package ca.mcgill.cs.swevo.ppa.inference;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.AbstractInferenceStrategy;
import org.eclipse.jdt.core.dom.EnhancedForStatement;
import org.eclipse.jdt.core.dom.EnumDeclaration;
import org.eclipse.jdt.core.dom.ForStatement;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.Name;
import org.eclipse.jdt.core.dom.PPABindingsUtil;
import org.eclipse.jdt.core.dom.PPADefaultBindingResolver;
import org.eclipse.jdt.core.dom.PPAEngine;
import org.eclipse.jdt.core.dom.PPATypeRegistry;
import org.eclipse.jdt.core.dom.SimpleName;
import org.eclipse.jdt.core.dom.SimpleType;
import org.eclipse.jdt.core.dom.SwitchStatement;
import org.eclipse.jdt.core.dom.Type;
import org.eclipse.jdt.core.dom.TypeDeclaration;
import org.eclipse.jdt.core.dom.VariableDeclaration;
import org.eclipse.jdt.core.dom.VariableDeclarationFragment;
import org.eclipse.jdt.core.dom.VariableDeclarationStatement;

import ca.mcgill.cs.swevo.ppa.PPAIndex;
import ca.mcgill.cs.swevo.ppa.PPAIndexer;
import ca.mcgill.cs.swevo.ppa.TypeFact;

public class VariableDeclarationStrategy extends AbstractInferenceStrategy {

	public VariableDeclarationStrategy(PPAIndexer indexer,
			PPAEngine ppaEngine) {
		// TODO Auto-generated constructor stub
		super(indexer, ppaEngine);
	}

	@Override
	public boolean isSafe(ASTNode node) {
		// TODO Auto-generated method stub
		VariableDeclarationStatement vd = (VariableDeclarationStatement)node;
		boolean bSafe = true;
		ITypeBinding vdt = null;
		try{
			vdt = vd.getType().resolveBinding();
			bSafe = PPABindingsUtil.isProblemType(vdt);
		}catch(Exception e){
			bSafe = false;
		}
		
		if(bSafe){
			MethodDeclaration md = getMethodDeclaration(node);
			
			if(md!=null){
				ArrayList<String> vars = new ArrayList<String>();
				for(Object o:vd.fragments()){
					VariableDeclarationFragment frag = (VariableDeclarationFragment)o;
					vars.add(frag.getName().getIdentifier());
				}
				VariableCollector visitor = new VariableCollector(vars);
				md.accept(visitor);
				int safeValue = vdt==null?0:PPABindingsUtil.getSafetyValue(vdt);
				for(ITypeBinding type:visitor.getTypes()){
					if(type==null){
						bSafe = false;
						break;
					}else{
						if(PPABindingsUtil.getSafetyValue(type)!=safeValue){
							bSafe = false;
							break;
						}
					}
				}
			}
		}

		return bSafe;
	}

	private MethodDeclaration getMethodDeclaration(ASTNode node) {
		// TODO Auto-generated method stub
		ASTNode parent = node.getParent();
		while(parent!=null&&!(parent instanceof MethodDeclaration)){
			parent = parent.getParent();			
		}
		return (MethodDeclaration)parent;
	}
	
	private ASTNode getTypeDeclaration(ASTNode node) {
		// TODO Auto-generated method stub
		ASTNode parent = node.getParent();
		while(parent.getParent()!=null){
			parent = parent.getParent();
			if((parent instanceof TypeDeclaration)||(parent instanceof EnumDeclaration)){
				break;
			}
		}
		return parent;
	}

	@Override
	public void inferTypes(ASTNode node) {
		// TODO Auto-generated method stub
		VariableDeclarationStatement vd = (VariableDeclarationStatement)node;
		ITypeBinding vdt = null;
		try{
			vdt = vd.getType().resolveBinding();
		}catch(Exception e){
			vdt = null;
		}
	
		MethodDeclaration md = getMethodDeclaration(node);
		
		if(md!=null){
			ArrayList<String> vars = new ArrayList<String>();
			for(Object o:vd.fragments()){
				VariableDeclarationFragment frag = (VariableDeclarationFragment)o;
				vars.add(frag.getName().getIdentifier());
			}
			VariableCollector visitor = new VariableCollector(vars);
			md.accept(visitor);
			ArrayList<ITypeBinding> types = visitor.getTypes();
			
		
			for(ITypeBinding type:types){
				if(type==null){
				}else if(vdt==null){
					vdt = type;
				}else if(PPABindingsUtil.getSafetyValue(vdt)<PPABindingsUtil.getSafetyValue(type)){
					vdt = type;
				}
			}
			TypeFact tFact = new TypeFact(indexer.getMainIndex(node), null,
					TypeFact.UNKNOWN, vdt, TypeFact.RELATED, TypeFact.VAR_STRATEGY);
			ppaEngine.reportTypeFact(tFact);
			
		}
	}

	@Override
	public void makeSafe(ASTNode node, TypeFact typeFact) {
		// TODO Auto-generated method stub
		
		VariableDeclarationStatement vd = (VariableDeclarationStatement)node;
		ITypeBinding vdt = null;
		try{
			vdt = vd.getType().resolveBinding();
		}catch(Exception e){
			vdt = null;
		}
		ITypeBinding newType = typeFact.getNewType();
		
		
		if(vdt==null||PPABindingsUtil.getSafetyValue(vdt)<PPABindingsUtil.getSafetyValue(newType)){
			fixType(vd.getType(), newType);
		}
		
	
		MethodDeclaration md = getMethodDeclaration(node);
		
		if(md!=null){
			ArrayList<String> vars = new ArrayList<String>();
			for(Object o:vd.fragments()){
				VariableDeclarationFragment frag = (VariableDeclarationFragment)o;
				vars.add(frag.getName().getIdentifier());
			}
			// added by nameng
			System.out.print("");
			VariableCollector visitor = new VariableCollector(vars);
			md.accept(visitor);
			PPADefaultBindingResolver resolver = null;
			for (SimpleName name : visitor.getNames()) {
				resolver = getResolver(name);
				resolver.fixLocal(name);
			}
			
			/*// by nameng: The processing here looks pretty weird. Instead, if the vars are known to be 
			  // local variables, just fix their local bindings instead of field bindings
			ASTNode root = this.getTypeDeclaration(node);
			ITypeBinding typeB = null;
			
			if(root instanceof TypeDeclaration){
				TypeDeclaration td = (TypeDeclaration)root;
				typeB = td.resolveBinding();
			}else if(root instanceof EnumDeclaration){
				EnumDeclaration ed = (EnumDeclaration)root;
				typeB = ed.resolveBinding();
			}
			VariableCollector visitor = new VariableCollector(vars);
			md.accept(visitor);
			for(SimpleName name: visitor.getNames()){				
				PPATypeRegistry typeRegistry = ppaEngine.getRegistry();
				PPADefaultBindingResolver resolver = getResolver(name);
				IVariableBinding newBinding = typeRegistry.getFieldBindingWithType(
						name.getFullyQualifiedName(), typeB, newType, resolver);
				resolver.fixFieldBinding(name, newBinding);
			}
			*/
		}
	}



	private void fixType(Type type, ITypeBinding newType) {
		// TODO Auto-generated method stub
		if(type instanceof SimpleType){
			SimpleType st = (SimpleType)type;
			Name name = st.getName();
			PPADefaultBindingResolver resolver = getResolver(type);
			resolver.fixTypeBinding(name, newType);
		}
	}

	@Override
	public void makeSafeSecondary(ASTNode node, TypeFact typeFact) {
		// TODO Auto-generated method stub
		
	}

	
}
