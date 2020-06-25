package ca.mcgill.cs.swevo.ppa.inference;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.AbstractInferenceStrategy;
import org.eclipse.jdt.core.dom.FieldDeclaration;
import org.eclipse.jdt.core.dom.IBinding;
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
import org.eclipse.jdt.core.dom.Type;
import org.eclipse.jdt.core.dom.TypeDeclaration;
import org.eclipse.jdt.core.dom.VariableDeclarationFragment;
import org.eclipse.jdt.core.dom.VariableDeclarationStatement;

import ca.mcgill.cs.swevo.ppa.PPAIndex;
import ca.mcgill.cs.swevo.ppa.PPAIndexer;
import ca.mcgill.cs.swevo.ppa.TypeFact;

public class FieldDeclarationStrategy extends AbstractInferenceStrategy {
	private int t1,t2;
	
	public FieldDeclarationStrategy(PPAIndexer indexer,
			PPAEngine ppaEngine) {
		// TODO Auto-generated constructor stub
		super(indexer, ppaEngine);
	}

	@Override
	public boolean isSafe(ASTNode node) {
		// TODO Auto-generated method stub
		FieldDeclaration vd = (FieldDeclaration)node;
		ITypeBinding vdt = vd.getType().resolveBinding();
		boolean bSafe = !PPABindingsUtil.isUnknownType(vdt);
		if(bSafe){
			TypeDeclaration td = getTypeDeclaration(node);
			
			if(td!=null){
				ArrayList<String> vars = new ArrayList<String>();
				for(Object o:vd.fragments()){
					VariableDeclarationFragment frag = (VariableDeclarationFragment)o;
					vars.add(frag.getName().getIdentifier());
				}
				VariableCollector visitor = new VariableCollector(vars);
				td.accept(visitor);
				int safeValue = PPABindingsUtil.getSafetyValue(vdt);
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


	
	private TypeDeclaration getTypeDeclaration(ASTNode node) {
		// TODO Auto-generated method stub
		ASTNode parent = node.getParent();
		while(parent!=null&&!(parent instanceof TypeDeclaration)){
			parent = parent.getParent();
		}
		return (TypeDeclaration)parent;
	}

	@Override
	public void inferTypes(ASTNode node) {
		// TODO Auto-generated method stub

		FieldDeclaration fd = (FieldDeclaration)node;
		ITypeBinding fdt = fd.getType().resolveBinding();
	
		TypeDeclaration td = getTypeDeclaration(node);
		
		if(td!=null){
			ArrayList<String> vars = new ArrayList<String>();
			for(Object o:fd.fragments()){
				VariableDeclarationFragment frag = (VariableDeclarationFragment)o;
				vars.add(frag.getName().getIdentifier());
			}
			VariableCollector visitor = new VariableCollector(vars);
			td.accept(visitor);
			ArrayList<ITypeBinding> types = visitor.getTypes();
		
			if (fdt == null) {//added by nameng
				for (ITypeBinding type : types) {
					if (type != null) {
						fdt = type;
						break;
					}
				}
			}
//			for(ITypeBinding type:types){//commmented by nameng
//				if(type==null){
//				}else if(fdt==null){
//					fdt = type;
//				}
				//commented out by nameng: This does not make sense. If type is a local variable,
				// while fdt is a field type, there is no reason to replace fdt with type.
//				else if(PPABindingsUtil.getSafetyValue(fdt)<PPABindingsUtil.getSafetyValue(type)){
//					fdt = type;
//				}
//			}
			TypeFact tFact = new TypeFact(indexer.getMainIndex(node), null,
					TypeFact.UNKNOWN, fdt, TypeFact.RELATED, TypeFact.VAR_STRATEGY);
			ppaEngine.reportTypeFact(tFact);
			
		}
	}

	@Override
	public void makeSafe(ASTNode node, TypeFact typeFact) {
		// TODO Auto-generated method stub
		FieldDeclaration vd = (FieldDeclaration)node;
		ITypeBinding vdt = vd.getType().resolveBinding();
		ITypeBinding newType = typeFact.getNewType();
		
		
		if(vdt==null||PPABindingsUtil.getSafetyValue(vdt)<PPABindingsUtil.getSafetyValue(newType)){
			fixType(vd.getType(), newType);
		}
		
		ArrayList<String> vars = new ArrayList<String>();
		for(Object o:vd.fragments()){
			VariableDeclarationFragment frag = (VariableDeclarationFragment)o;
			vars.add(frag.getName().getIdentifier());
		}
		TypeDeclaration td = getTypeDeclaration(node);
		ITypeBinding typeB = td.resolveBinding();
		VariableCollector visitor = new VariableCollector(vars);
		td.accept(visitor);
		for(SimpleName name: visitor.getNames()){
			ITypeBinding oldBinding = name.resolveTypeBinding();
			if(PPABindingsUtil.getSafetyValue(oldBinding)<PPABindingsUtil.getSafetyValue(newType)){
				PPATypeRegistry typeRegistry = ppaEngine.getRegistry();
				PPADefaultBindingResolver resolver = getResolver(name);
				IVariableBinding newBinding = typeRegistry.getFieldBindingWithType(
						name.getFullyQualifiedName(), typeB, newType, resolver);
				resolver.fixFieldBinding(name, newBinding);
			}
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
