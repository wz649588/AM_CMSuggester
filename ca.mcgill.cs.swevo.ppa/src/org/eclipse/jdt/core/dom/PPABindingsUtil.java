/*******************************************************************************
 * PPA - Partial Program Analysis for Java
 * Copyright (C) 2008 Barthelemy Dagenais
 * 
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either 
 * version 3 of the License, or (at your option) any later version.
 * 
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this library. If not, see 
 * <http://www.gnu.org/licenses/lgpl-3.0.txt>
 *******************************************************************************/
package org.eclipse.jdt.core.dom;

import java.io.File;
import java.io.FileOutputStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.apache.log4j.Logger;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.dom.AST;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.AnonymousClassDeclaration;
import org.eclipse.jdt.core.dom.BindingResolver;
import org.eclipse.jdt.core.dom.ClassInstanceCreation;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.DefaultBindingResolver;
import org.eclipse.jdt.core.dom.EnumDeclaration;
import org.eclipse.jdt.core.dom.Expression;
import org.eclipse.jdt.core.dom.IBinding;
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.IPackageBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.eclipse.jdt.core.dom.MethodInvocation;
import org.eclipse.jdt.core.dom.Modifier;
import org.eclipse.jdt.core.dom.Name;
import org.eclipse.jdt.core.dom.SimpleName;
import org.eclipse.jdt.core.dom.SuperMethodInvocation;
import org.eclipse.jdt.core.dom.Type;
import org.eclipse.jdt.core.dom.TypeBinding;
import org.eclipse.jdt.core.dom.TypeDeclaration;
import org.eclipse.jdt.internal.compiler.ClassFile;
import org.eclipse.jdt.internal.compiler.ast.AbstractMethodDeclaration;
import org.eclipse.jdt.internal.compiler.ast.CompilationUnitDeclaration;
import org.eclipse.jdt.internal.compiler.ast.ConstructorDeclaration;
import org.eclipse.jdt.internal.compiler.lookup.BaseTypeBinding;
import org.eclipse.jdt.internal.compiler.lookup.PPAType;
import org.eclipse.jdt.internal.compiler.lookup.ProblemMethodBinding;
import org.eclipse.jdt.internal.compiler.lookup.ProblemReferenceBinding;
import org.eclipse.jdt.internal.compiler.lookup.TagBits;
import org.eclipse.jdt.internal.core.JavaProject;

import ca.mcgill.cs.swevo.ppa.PPAASTUtil;
import ca.mcgill.cs.swevo.ppa.PPAIndexer;
import ca.mcgill.cs.swevo.ppa.PPALoggerUtil;
import ca.mcgill.cs.swevo.ppa.PPAOptions;
import ca.mcgill.cs.swevo.ppa.TypeFact;
import ca.mcgill.cs.swevo.ppa.ValidatorUtil;

public class PPABindingsUtil {

	private static final String CLASS_EXTENSION = ".class";

	public static final int PROBLEM_TYPE = -1;
	public static final int UNKNOWN_TYPE = 0;
	public static final int MISSING_TYPE = 1;
	public static final int MISSING_SUPER_TYPE = 2;
	public static final int FULL_TYPE = 3;

	private final static Logger logger = PPALoggerUtil.getLogger(PPABindingsUtil.class);

	public static boolean compatibleTypes(ITypeBinding formalType, ITypeBinding actualType) {
		boolean compatible = false;
		if(formalType==null||actualType==null){
			return false;
		}
			
		String actualTypeType = getTypeString(actualType);
		String formalTypeType = getTypeString(formalType);

		boolean areBooleans = formalTypeType.equals("boolean") && actualTypeType.equals("boolean");
		boolean oneIsBoolean = !areBooleans
				&& (formalTypeType.equals("boolean") || actualTypeType.equals("boolean"));

		boolean areVoids = formalTypeType.equals("void") && actualTypeType.equals("void");
		boolean oneIsVoid = !areVoids
				&& (formalTypeType.equals("void") || actualTypeType.equals("void"));

		int formalSafetyValue = getSafetyValue(formalType);
		int actualSafetyValue = getSafetyValue(actualType);
		compatible = formalType.isEqualTo(actualType);
		compatible = compatible || isUnknownType(formalType) || isUnknownType(actualType);
		compatible = compatible
				|| (formalType.isPrimitive() && actualType.isPrimitive() && !oneIsBoolean && !oneIsVoid);
		compatible = compatible || (!formalType.isPrimitive() && actualType.isNullType());
		compatible = compatible || (formalSafetyValue < FULL_TYPE && actualSafetyValue < FULL_TYPE);
		compatible = compatible
				|| (!formalType.isPrimitive() && !Modifier.isFinal(formalType.getModifiers())
						&& formalSafetyValue == FULL_TYPE && actualSafetyValue < FULL_TYPE);
		compatible = compatible || JdtTool.isSubTypeCompatible(actualType, formalType);

		// TODO: Primitive with Reference Type -> enforce in the next one...
		// TODO: Formal known super type, but unknown actual...
		
		return compatible;
	}

	public static List<IMethodBinding> filterMethods(List<IMethodBinding> methodBindings,
			boolean filterUnknowns) {
		List<IMethodBinding> acceptableMethods = new ArrayList<IMethodBinding>();
		Set<String> keys = new HashSet<String>();

		for (IMethodBinding binding : methodBindings) {
			String key = getShortMethodSignature(binding);
			boolean acceptable = true;

			if (filterUnknowns) {
				acceptable = !getTypeString(binding.getReturnType()).equals(
						PPATypeRegistry.UNKNOWN_CLASS_FQN);

				if (acceptable) {
					int size = getArgsLength(binding);
					for (int i = 0; i < size; i++) {
						if (getTypeString(binding.getParameterTypes()[i]).equals(
								PPATypeRegistry.UNKNOWN_CLASS_FQN)) {
							acceptable = false;
							break;
						}
					}
				}
			}

			if (acceptable && !keys.contains(key)) {
				keys.add(key);
				acceptableMethods.add(binding);
			}
		}

		return acceptableMethods;
	}

	private static List<IMethodBinding> findAcceptableConstructors(int numberParams,
			ITypeBinding containerType) {

		List<IMethodBinding> acceptableMethods = new ArrayList<IMethodBinding>();

		if (!isUnknownType(containerType) && !isMissingType(containerType)) {
			for (IMethodBinding mBinding : containerType.getDeclaredMethods()) {
				if (mBinding.isConstructor() && getArgsLength(mBinding) == numberParams) {
					acceptableMethods.add(mBinding);
				}
			}
		}

		return acceptableMethods;
	}

	public static List<IMethodBinding> findAcceptableConstructors(ITypeBinding[] params,
			ITypeBinding container) {
		List<IMethodBinding> acceptableMethods = new ArrayList<IMethodBinding>();
		int numberParams = params.length;
		List<IMethodBinding> tempMethods = findAcceptableConstructors(numberParams, container);

		for (IMethodBinding mBinding : tempMethods) {
			boolean valid = true;
			ITypeBinding[] formalParams = mBinding.getParameterTypes();
			for (int i = 0; i < numberParams; i++) {
				if (!compatibleTypes(formalParams[i], params[i])) {
					valid = false;
					break;
				}
			}
			if (valid) {
				acceptableMethods.add(mBinding);
			}
		}

		return acceptableMethods;
	}

	public static List<IMethodBinding> findAcceptableMethods(String name, int numberParams,
			ITypeBinding container) {
		List<IMethodBinding> acceptableMethods = new ArrayList<IMethodBinding>();

		if (!isUnknownType(container) && !isMissingType(container)) {
			ITypeBinding[] superTypes = getAllSuperTypes(container);
			for (IMethodBinding mBinding : container.getDeclaredMethods()) {
				if (mBinding.getName().equals(name) && getArgsLength(mBinding) == numberParams) {
					acceptableMethods.add(mBinding);
				}
			}

			for (ITypeBinding superType : superTypes) {
				for (IMethodBinding mBinding : superType.getDeclaredMethods()) {
					if (mBinding.getName().equals(name) && getArgsLength(mBinding) == numberParams
							&& !Modifier.isPrivate(mBinding.getModifiers())) {
						acceptableMethods.add(mBinding);
					}
				}
			}
		}

		return acceptableMethods;
	}

	public static List<IMethodBinding> findAcceptableMethods(String name, ITypeBinding[] params,
			ITypeBinding container) {
		List<IMethodBinding> acceptableMethods = new ArrayList<IMethodBinding>();
		int numberParams = params.length;
		List<IMethodBinding> tempMethods = findAcceptableMethods(name, numberParams, container);

		for (IMethodBinding mBinding : tempMethods) {
			boolean valid = true;
			ITypeBinding[] formalParams = mBinding.getParameterTypes();
			for (int i = 0; i < numberParams; i++) {
				if (!compatibleTypes(formalParams[i], params[i])) {
					valid = false;
					break;
				}
			}
			if (valid) {
				acceptableMethods.add(mBinding);
			}
		}

		return acceptableMethods;
	}

	public static List<IMethodBinding> findAcceptableMethods(String name, ITypeBinding[] params,
			ITypeBinding returnType, ITypeBinding container) {
		List<IMethodBinding> acceptableMethods = new ArrayList<IMethodBinding>();
		List<IMethodBinding> tempMethods = findAcceptableMethods(name, params, container);

		for (IMethodBinding mBinding : tempMethods) {
			if (compatibleTypes(returnType, mBinding.getReturnType())) {
				acceptableMethods.add(mBinding);
			}
		}

		return acceptableMethods;
	}

	private static List<IMethodBinding> findAcceptableKnownMethods(String name, ITypeBinding[] params,
			ITypeBinding returnType, ITypeBinding container) {
		// TODO Auto-generated method stub
		List<IMethodBinding> acceptableMethods = new ArrayList<IMethodBinding>();
		List<IMethodBinding> tempMethods = findAcceptableMethods(name, params, container);
		Set<String> keys = new HashSet<String>();
		for (IMethodBinding mBinding : tempMethods) {
			boolean acceptable = !getTypeString(mBinding.getReturnType()).equals(
					PPATypeRegistry.UNKNOWN_CLASS_FQN);
			if (acceptable) {
				int size = getArgsLength(mBinding);
				for (int i = 0; i < size; i++) {
					if (getTypeString(mBinding.getParameterTypes()[i]).equals(
							PPATypeRegistry.UNKNOWN_CLASS_FQN)) {
						acceptable = false;
						break;
					}
				}
			}
			if (acceptable&&compatibleTypes(returnType, mBinding.getReturnType())) {
				String key = getShortMethodSignature(mBinding);
				
				// commented by Ye Wang to fix bug, this stmt should not exist, because of the same stmt in the if-stmt.
				// If this stmt exists, the same mBinding will be added to acceptableMethods twice.
//				acceptableMethods.add(mBinding);
				if (!keys.contains(key)) {
					keys.add(key);
					acceptableMethods.add(mBinding);
				}
			}
		}
		return acceptableMethods;
	}
	
	public static IVariableBinding findField(ITypeBinding type, String fieldName) {
		return findFieldHierarchy(type, fieldName);
	}

	public static IVariableBinding findFieldHierarchy(ITypeBinding type, String fieldName) {
		IVariableBinding fieldBinding = findFieldInType(type, fieldName);
		if (fieldBinding != null) {
			return fieldBinding;
		}
		if(type!=null){
			ITypeBinding superClass = type.getSuperclass();
			if (superClass != null) {
				fieldBinding = findFieldHierarchy(superClass, fieldName);
				if (fieldBinding != null) {
					return fieldBinding;
				}
			}
			ITypeBinding[] interfaces = type.getInterfaces();
			if (interfaces != null) {
				for (int i = 0; i < interfaces.length; i++) {
					fieldBinding = findFieldHierarchy(interfaces[i], fieldName);
					if (fieldBinding != null) {
						return fieldBinding;
					}
				}
			}
		}
		return null;
	}

	public static IVariableBinding findFieldInType(ITypeBinding type, String fieldName) {
		IVariableBinding fieldBinding = null;
		if(type!=null){
			IVariableBinding[] fields = type.getDeclaredFields();
			for (int i = 0; i < fields.length; i++) {
				IVariableBinding field = fields[i];
				if (field.getName().equals(fieldName)&&!Modifier.isPrivate(field.getModifiers())) {
					fieldBinding = field;
					break;
				}
			}
		}
		return fieldBinding;
	}

	public static void fixConstructor(ClassInstanceCreation cic, PPATypeRegistry typeRegistry,
			PPADefaultBindingResolver resolver, PPAIndexer indexer, PPAEngine engine,
			boolean skipSuperMissing, boolean filterUnknowns) {
		IMethodBinding oldBinding = cic.resolveConstructorBinding();
		ITypeBinding unknownType = typeRegistry.getUnknownBinding(resolver);
		ITypeBinding[] paramTypes = PPABindingsUtil.getParamTypes(cic, unknownType);
		ITypeBinding containerType = null;

		if (oldBinding == null) {
			if (cic.getAnonymousClassDeclaration() != null) {
				// XXX Case when this is an anonymous class that is not resolved.
				containerType = cic.getType().resolveBinding();
			}
		} else {
			containerType = oldBinding.getDeclaringClass();
		}

		// XXX This is to prevent the problem of null container type. it should
		// not happen.
		if (containerType == null) {
			logger.info("This container type was null: " + cic.toString());
			containerType = unknownType;
		}

		List<IMethodBinding> acceptableMethods = new ArrayList<IMethodBinding>();

		if (!skipSuperMissing
				|| PPABindingsUtil.getSafetyValue(containerType) == PPABindingsUtil.FULL_TYPE) {
			acceptableMethods = PPABindingsUtil.filterMethods(
					PPABindingsUtil.findAcceptableConstructors(paramTypes, containerType),
					filterUnknowns);
		}

		if (acceptableMethods.size() == 1) {
			IMethodBinding newBinding = acceptableMethods.get(0);
			if (oldBinding == null || !newBinding.isEqualTo(oldBinding)) {
				resolver.fixClassInstanceCreation(cic, newBinding);
				reportNewConstructorBinding(indexer, engine, unknownType, cic, paramTypes,
						newBinding);
			}
		} else {
			IMethodBinding newBinding = typeRegistry.createConstructor(containerType, paramTypes,
					resolver);
			resolver.fixClassInstanceCreation(cic, newBinding);
			
			
		}
	}

	public static void fixMethod(SimpleName name, ITypeBinding expectedReturnType,
			PPATypeRegistry typeRegistry, PPADefaultBindingResolver resolver, PPAIndexer indexer,
			PPAEngine ppaEngine) {
		fixMethod(name, expectedReturnType, typeRegistry, resolver, indexer, ppaEngine, true, true);
	}

	public static void fixMethod(SimpleName name, ITypeBinding expectedReturnType,
			PPATypeRegistry typeRegistry, PPADefaultBindingResolver resolver, PPAIndexer indexer,
			PPAEngine ppaEngine, boolean skipSuperMissing, boolean filterUnknowns) {
		ASTNode parent = name.getParent();
		String methodName = name.getFullyQualifiedName();
		ITypeBinding unknownType = typeRegistry.getUnknownBinding(resolver);
		IMethodBinding oldBinding = null;
		ITypeBinding[] paramTypes = null;
		ITypeBinding containerType = null;
		ASTNode container = null;
	
		if (parent instanceof MethodInvocation) {
			MethodInvocation mi = (MethodInvocation) parent;
			container = PPAASTUtil.getContainer(mi);
			if (container == null) {
				return;
			}
			paramTypes = PPABindingsUtil.getParamTypes(mi.arguments(), unknownType);
			containerType = PPABindingsUtil.getTypeBinding(container);
			oldBinding = mi.resolveMethodBinding();
			//zhh
			ITypeBinding[] formTypes = oldBinding.getParameterTypes();
			int size = formTypes.length<paramTypes.length?formTypes.length:paramTypes.length;
			for(int i=0; i<size; i++){
				ITypeBinding paraType = paramTypes[i];
				ITypeBinding formType = formTypes[i];
				if(paraType == unknownType){
					paramTypes[i] = formType;
				}
			}
		
			if(oldBinding.getReturnType().toString().indexOf("capture#")>=0){
				expectedReturnType = unknownType;
			}else if(expectedReturnType==null){
				expectedReturnType = oldBinding.getReturnType();
			}
		}
	
		if (parent instanceof SuperMethodInvocation) {
			SuperMethodInvocation smi = (SuperMethodInvocation) parent;
			container = PPAASTUtil.getSpecificParentType(parent, ASTNode.TYPE_DECLARATION);
			if (container != null) {
				TypeDeclaration td = (TypeDeclaration) container;
				container = td.getSuperclassType();
			}

			if (container != null) {
				paramTypes = PPABindingsUtil.getParamTypes(smi.arguments(), unknownType);
				containerType = PPABindingsUtil.getTypeBinding(container);
				oldBinding = smi.resolveMethodBinding();
			}
		}

		if (container != null) {
			// XXX This is to prevent the problem of null container type. it
			// should not happen.
			if (containerType == null) {
				logger.info("This container type was null: " + name.getFullyQualifiedName() + " : "
						+ container.toString());
				containerType = PPABindingsUtil.getTypeBinding(container);
				containerType = unknownType;
			}
			if(containerType.toString().indexOf("capture#")>=0){
				containerType = containerType.getSuperclass();
			}
			List<IMethodBinding> acceptableMethods = new ArrayList<IMethodBinding>();

			if (!skipSuperMissing
					|| PPABindingsUtil.getSafetyValue(containerType) == PPABindingsUtil.FULL_TYPE) {
				if (expectedReturnType == null) {
					if(filterUnknowns){
						acceptableMethods = PPABindingsUtil
								.findAcceptableKnownMethods(methodName, paramTypes, expectedReturnType,
										containerType);
					}else{
						acceptableMethods = PPABindingsUtil.filterMethods(PPABindingsUtil
							.findAcceptableMethods(methodName, paramTypes, expectedReturnType,
									containerType), filterUnknowns);
					}
				} else {
					if(filterUnknowns){
						acceptableMethods = PPABindingsUtil
								.findAcceptableKnownMethods(methodName, paramTypes, expectedReturnType,
										containerType);
					}else{
						acceptableMethods = PPABindingsUtil.filterMethods(PPABindingsUtil
							.findAcceptableMethods(methodName, paramTypes, expectedReturnType,
									containerType), filterUnknowns);
					}
				}
			}

			if (acceptableMethods.size() == 1) {
				IMethodBinding newBinding = acceptableMethods.get(0);

				if (oldBinding == null || !newBinding.isEqualTo(oldBinding)) {
					resolver.fixMessageSend(name, newBinding);
					reportNewMethodBinding(indexer, ppaEngine, unknownType, parent, paramTypes,
							newBinding);
				}
			} else {
				if(container instanceof TypeDeclaration){
					TypeDeclaration td = (TypeDeclaration)container;
					boolean bFound = false;
					for(MethodDeclaration md:td.getMethods()){
						if(md.getName().getIdentifier().compareTo(methodName)==0){
							bFound = true;
							break;
						}						
					}
					ITypeBinding newContainerType = null;
					if(bFound){
						newContainerType = td.resolveBinding();
					}else{
						newContainerType = PPABindingsUtil
								.getFirstFieldContainerMissingSuperType(container);
					}
					ITypeBinding newReturnType = expectedReturnType == null ? unknownType
							: expectedReturnType;
					if (newContainerType == null) {
						newContainerType = containerType;
					}

					IMethodBinding newBinding = typeRegistry.createMethodBinding(methodName,
							newContainerType, newReturnType, paramTypes, resolver);
					resolver.fixMessageSend(name, newBinding);
				}else{
					ITypeBinding newReturnType = expectedReturnType == null ? unknownType
							: expectedReturnType;
					IMethodBinding newBinding = typeRegistry.createMethodBinding(methodName,
							containerType, newReturnType, paramTypes, resolver);
					resolver.fixMessageSend(name, newBinding);
				}
			}

		}
	}

	

	public static void fixMethod(SimpleName name, PPATypeRegistry typeRegistry,
			PPADefaultBindingResolver resolver, PPAIndexer indexer, PPAEngine ppaEngine) {
		fixMethod(name, null, typeRegistry, resolver, indexer, ppaEngine);
	}

	@SuppressWarnings({ "rawtypes", "unchecked" })
	public static ITypeBinding[] getAllSuperTypes(ITypeBinding type) {
		Set superTypes = new HashSet();
		getAllSuperTypes(type, superTypes);
		superTypes.remove(type);
		return (ITypeBinding[]) superTypes.toArray(new ITypeBinding[superTypes.size()]);
	}

	@SuppressWarnings({ "rawtypes", "unchecked" })
	private static void getAllSuperTypes(ITypeBinding type, Set superTypes) {
		if (superTypes.contains(type)) {
			// Possible because of interfaces
			return;
		} else {
			superTypes.add(type);
			// Interfaces first.
			ITypeBinding[] interfaces = type.getInterfaces();
			for (int i = 0; i < interfaces.length; i++) {
				getAllSuperTypes(interfaces[i], superTypes);
			}
			// Super class in second.
			ITypeBinding superClass = type.getSuperclass();
			if (superClass != null) {
				getAllSuperTypes(superClass, superTypes);
			}
		}

	}

	public static int getArgsLength(IMethodBinding mBinding) {
		ITypeBinding[] args = mBinding.getParameterTypes();
		return args == null ? 0 : args.length;
	}

	public static char[][] getArrayFromName(String name) {
		ValidatorUtil.validateEmpty(name, "name", true);
		String[] fragments = name.split("\\.");
		int size = fragments.length;
		char[][] packages = new char[size][];

		for (int i = 0; i < size; i++) {
			packages[i] = fragments[i].toCharArray();
		}

		return packages;
	}

	public static String getBindingText(IBinding binding) {
		String bindingText = "";
		if (binding != null) {
			if (binding instanceof IMethodBinding) {
				IMethodBinding mBinding = (IMethodBinding) binding;
				bindingText = "MBinding: " + PPABindingsUtil.getFullMethodSignature(mBinding);
			} else if (binding instanceof IVariableBinding) {
				IVariableBinding vBinding = (IVariableBinding) binding;
				if (vBinding.isField()) {
					String type = "nil";
					if (vBinding.getType() != null) {
						type = getTypeString(vBinding.getType());
					}

					String decType = "nil";
					if (vBinding.getDeclaringClass() != null) {
						decType = getTypeString(vBinding.getDeclaringClass());
					}
					bindingText = "FBinding: " + type + " " + decType + ":" + vBinding.getName();
				} else {
					String type = "nil";
					if (vBinding.getType() != null) {
						type = getTypeString(vBinding.getType());
					}
					bindingText = "VBinding: " + type + " " + vBinding.getName();
				}
			} else if (binding instanceof ITypeBinding) {
				ITypeBinding typeBinding = (ITypeBinding) binding;
				bindingText = "TBinding: " + typeBinding.getName();
			} else if (binding instanceof IPackageBinding) {
				IPackageBinding pBinding = (IPackageBinding) binding;
				bindingText = "PBinding: " + pBinding.getName();
			}
		}
		return bindingText;
	}

	public static ASTNode getCU(ICompilationUnit icu) throws JavaModelException, SanityCheckException {
		PPATypeRegistry registry = new PPATypeRegistry((JavaProject) JavaCore.create(icu
				.getUnderlyingResource().getProject()));

		return getCU(icu, registry, true);
	}
	
	public static ASTNode getCU(ICompilationUnit icu, boolean cleanup) throws JavaModelException, SanityCheckException {
		PPATypeRegistry registry = new PPATypeRegistry((JavaProject) JavaCore.create(icu
				.getUnderlyingResource().getProject()));

		return getCU(icu, registry, cleanup);
	}
	
	// For testing
	public static ASTNode getCU(ICompilationUnit icu, PPATypeRegistry registry) throws JavaModelException, SanityCheckException {
		return getCU(icu, registry, true);
	}

	// For testing
	public static ASTNode getCU(ICompilationUnit icu, PPATypeRegistry registry, boolean cleanup)
			throws JavaModelException, SanityCheckException {//SanityCheckExeption added by nameng
		ASTNode node = null;
		PPAASTParser parser2 = new PPAASTParser(AST.JLS3);
		parser2.setStatementsRecovery(true);
		// parser2.setBindingsRecovery(true);
		parser2.setResolveBindings(true);
		parser2.setSource(icu);
		node = parser2.createAST(cleanup, null);
		PPAEngine ppaEngine = new PPAEngine(registry, new PPAOptions());

		CompilationUnit cu = (CompilationUnit) node;

		ppaEngine.addUnitToProcess(cu);
		ppaEngine.doPPA();
		ppaEngine.reset();
		return node;
	}

	// For testing
	public static ASTNode getCUWithoutMemberInference(ICompilationUnit icu)
			throws JavaModelException, SanityCheckException {
		PPATypeRegistry registry = new PPATypeRegistry((JavaProject) JavaCore.create(icu
				.getUnderlyingResource().getProject()));
		ASTNode node = null;
		PPAASTParser parser2 = new PPAASTParser(AST.JLS3);
		parser2.setStatementsRecovery(true);
		// parser2.setBindingsRecovery(true);
		parser2.setResolveBindings(true);
		parser2.setSource(icu);
		node = parser2.createAST(true, null);
		PPAEngine ppaEngine = new PPAEngine(registry, new PPAOptions());
		ppaEngine.setAllowMemberInference(false);

		CompilationUnit cu = (CompilationUnit) node;
		ppaEngine.addUnitToProcess(cu);
		ppaEngine.doPPA();
		ppaEngine.reset();
		return node;
	}

	public static ASTNode getCUWithoutMethodBinding(ICompilationUnit icu) throws JavaModelException, SanityCheckException {
		PPATypeRegistry registry = new PPATypeRegistry((JavaProject) JavaCore.create(icu
				.getUnderlyingResource().getProject()));
		ASTNode node = null;
		PPAASTParser parser2 = new PPAASTParser(AST.JLS3);
		parser2.setStatementsRecovery(true);
		// parser2.setBindingsRecovery(true);
		parser2.setResolveBindings(true);
		parser2.setSource(icu);
		node = parser2.createAST(true, null);
		PPAEngine ppaEngine = new PPAEngine(registry, new PPAOptions());
		CompilationUnit cu = (CompilationUnit) node;
		ppaEngine.setAllowMethodBindingMode(false);
		ppaEngine.addUnitToProcess(cu);
		ppaEngine.doPPA();
		ppaEngine.reset();
		return node;
	}

	/**
	 * <p>
	 * </p>
	 * 
	 * @param container
	 * @return The type in the hierarchy of the container that has a missing declaration. Can be the
	 *         container itself for FieldAccess and Name. Null if the type of a name cannot be
	 *         resolved.
	 */
	public static ITypeBinding getFirstFieldContainerMissingSuperType(ASTNode container) {
		ITypeBinding superTypeBinding = null;
		if (container == null) {
			superTypeBinding = null;
		} else if (container instanceof TypeDeclaration) {
			TypeDeclaration tDeclaration = (TypeDeclaration) container;
			superTypeBinding = getFirstMissingSuperType(tDeclaration.resolveBinding());
		} else if (container instanceof AnonymousClassDeclaration) {
			AnonymousClassDeclaration aDeclaration = (AnonymousClassDeclaration) container;
			superTypeBinding = aDeclaration.resolveBinding();
			if (!isMissingType(superTypeBinding)) {
				superTypeBinding = getFirstMissingSuperType(superTypeBinding);
			}
		} else if (container instanceof Expression) {
			Expression expression = (Expression) container;
			//zhh
			superTypeBinding = expression.resolveTypeBinding();

			if (getSafetyValue(superTypeBinding) > PPABindingsUtil.MISSING_TYPE) {
				superTypeBinding = getFirstMissingSuperType(superTypeBinding);
			}
		}

		if (superTypeBinding == null
				&& (container instanceof TypeDeclaration || container instanceof AnonymousClassDeclaration)) {
			container = PPAASTUtil.getFieldContainer(container, true, false);
			if (container != null) {
				superTypeBinding = getFirstFieldContainerMissingSuperType(container);
			}
		}

		return superTypeBinding;
	}

	/**
	 * <p>
	 * Depth-first search to find the first missing interface of a type.
	 * </p>
	 * 
	 * @param typeBinding
	 *            A type which is neither unknown nor missing.
	 * @return The first interface of this type in a depth-first search that is missing.
	 */
	public static ITypeBinding getFirstMissingInterface(ITypeBinding typeBinding) {
		ITypeBinding missingSuperInterface = null;

		if (!isProblemType(typeBinding) && !isUnknownType(typeBinding)
				&& !isMissingType(typeBinding)) {
			for (ITypeBinding superInterface : typeBinding.getInterfaces()) {
				if (isMissingType(superInterface)) {
					missingSuperInterface = superInterface;
					break;
				} else {
					missingSuperInterface = getFirstMissingInterface(superInterface);
					if (missingSuperInterface != null) {
						break;
					}
				}
			}
		}

		return missingSuperInterface;
	}

	/**
	 * <p>
	 * Depth-first search to find the first missing superclass of a type.
	 * </p>
	 * 
	 * @param typeBinding
	 *            A type which is neither unknown nor missing.
	 * @return The first class of this type in a depth-first search that is missing.
	 */
	public static ITypeBinding getFirstMissingSuperClass(ITypeBinding typeBinding) {
		ITypeBinding missingSuperClass = null;

		if (!isProblemType(typeBinding) && !isUnknownType(typeBinding)
				&& !isMissingType(typeBinding)) {
			ITypeBinding superType = typeBinding.getSuperclass();
			if (isMissingType(superType)) {
				missingSuperClass = superType;
			} else {
				missingSuperClass = getFirstMissingSuperClass(superType);
			}
		}

		return missingSuperClass;
	}

	public static ITypeBinding getFirstMissingSuperType(ITypeBinding typeBinding) {
		ITypeBinding missingSuperType = null;

		if (!isProblemType(typeBinding) && !isUnknownType(typeBinding)
				&& !isMissingType(typeBinding)) {
			missingSuperType = getFirstMissingSuperClass(typeBinding);
			// look for interfaces;
			if (missingSuperType == null) {
				missingSuperType = getFirstMissingInterface(typeBinding);
			}
		}

		return missingSuperType;
	}

	public static String getFQN(String packageName, String name) {
		String fqn = name;
		if (ValidatorUtil.validateEmpty(packageName, "package", false)) {
			fqn = packageName + "." + name;
		}

		return fqn;
	}

	public static String getFullMethodSignature(IMethodBinding methodBinding) {
		StringBuffer buffer = new StringBuffer();
		try {
			int numArgs = getArgsLength(methodBinding);
			ITypeBinding[] params = methodBinding.getParameterTypes();
			ITypeBinding returnType = methodBinding.getReturnType();
			String name = methodBinding.getName();
			buffer.append(getTypeString(returnType));
			buffer.append(" ");
			buffer.append(getTypeString(methodBinding.getDeclaringClass()));
			buffer.append(":");
			buffer.append(name);
			buffer.append("(");

			for (int i = 0; i < numArgs; i++) {
				buffer.append(getTypeString(params[i]));
				if (i < numArgs - 1) {
					buffer.append(",");
				}
			}

			buffer.append(")");
		} catch (Exception e) {
			logger.error("Error while getting method signature", e);
			exdist.ExceptionHandler.process(e, "Error while getting method signature");
		}
		return buffer.toString();
	}

	public static org.eclipse.jdt.internal.compiler.lookup.TypeBinding getInternalTypeBinding(
			ITypeBinding typeBinding) {
		org.eclipse.jdt.internal.compiler.lookup.TypeBinding internalTBinding = null;

		if (typeBinding instanceof TypeBinding) {
			TypeBinding tBinding = (TypeBinding) typeBinding;
			internalTBinding = tBinding.binding;
		}

		return internalTBinding;
	}

	public static String getPackage(String name) {
		ValidatorUtil.validateEmpty(name, "name", true);
		String packageName = null;

		int index = name.lastIndexOf(".");
		if (index != PROBLEM_TYPE && index != (name.length() - 1)) {
			packageName = name.substring(0, index);
		}

		return packageName;
	}

	public static String[] getPackageArray(String packageName) {
		String[] packages = null;
		if (ValidatorUtil.validateEmpty(packageName, "packageName", false)) {
			packages = packageName.split("\\.");
		}

		return packages;
	}

	@SuppressWarnings("rawtypes")
	private static ITypeBinding[] getParamTypes(ClassInstanceCreation cic,
			ITypeBinding unknownBinding) {
		List args = cic.arguments();
		int size = args.size();
		ITypeBinding[] typeBindings = new ITypeBinding[args.size()];

		for (int i = 0; i < size; i++) {
			ASTNode node = (ASTNode) args.get(i);
			ITypeBinding tempBinding = PPABindingsUtil.getTypeBinding(node);
			if (tempBinding == null) {
				tempBinding = unknownBinding;
			}
			typeBindings[i] = tempBinding;
		}

		return typeBindings;
	}

	@SuppressWarnings("rawtypes")
	public static ITypeBinding[] getParamTypes(List args, ITypeBinding unknownBinding) {
		int size = args.size();
		ITypeBinding[] typeBindings = new ITypeBinding[args.size()];

		for (int i = 0; i < size; i++) {
			ASTNode node = (ASTNode) args.get(i);
			ITypeBinding tempBinding = PPABindingsUtil.getTypeBinding(node);
			if (tempBinding == null || tempBinding.isNullType()||tempBinding.toString().indexOf("capture#")>=0) {
				tempBinding = unknownBinding;
			}
			typeBindings[i] = tempBinding;
		}

		return typeBindings;
	}

	public static PPADefaultBindingResolver getResolver(AST ast) {
		PPADefaultBindingResolver returnResolver = null;
		BindingResolver resolver = ast.getBindingResolver();
		if (resolver instanceof PPADefaultBindingResolver) {
			returnResolver = (PPADefaultBindingResolver) resolver;
		}
		return returnResolver;
	}

	public static int getSafetyValue(ITypeBinding binding) {
		if (isProblemType(binding)) {
			return PROBLEM_TYPE;
		} else if (isUnknownType(binding)) {
			return UNKNOWN_TYPE;
		} else if (isMissingType(binding)) {
			return MISSING_TYPE;
		} else if (isSuperMissingType(binding)) {
			return MISSING_SUPER_TYPE;
		} else if (isFullType(binding)) {
			return FULL_TYPE;
		} else {
			// We've got a problem;
			assert false;
			return -100;
		}
	}

	public static String getShortMethodSignature(IMethodBinding methodBinding) {
		StringBuffer buffer = new StringBuffer();
		int numArgs = getArgsLength(methodBinding);
		ITypeBinding[] params = methodBinding.getParameterTypes();
		ITypeBinding returnType = methodBinding.getReturnType();
		String name = methodBinding.getName();

		buffer.append(getTypeString(returnType));
		buffer.append(" ");
		buffer.append(name);
		buffer.append("(");

		for (int i = 0; i < numArgs; i++) {
			buffer.append(getTypeString(params[i]));
			if (i < numArgs - 1) {
				buffer.append(",");
			}
		}

		buffer.append(")");

		return buffer.toString();
	}

	public static String getSimpleName(String name) {
		ValidatorUtil.validateEmpty(name, "name", true);
		String simpleName = name;
		int index = name.lastIndexOf(".");
		if (index != -1 && index != (name.length() - 1)) {
			simpleName = name.substring(index + 1);
		}

		return simpleName;
	}

	public static ITypeBinding getTypeBinding(ASTNode node) {
		ITypeBinding typeBinding = null;

		if (node == null) {
			typeBinding = null;
		} else if (node instanceof TypeDeclaration) {
			TypeDeclaration typeDec = (TypeDeclaration) node;
			typeBinding = typeDec.resolveBinding();
		} else if (node instanceof AnonymousClassDeclaration) {
			AnonymousClassDeclaration anon = (AnonymousClassDeclaration) node;
			typeBinding = anon.resolveBinding();
		} else if (node instanceof EnumDeclaration) {
			EnumDeclaration enumD = (EnumDeclaration) node;
			typeBinding = enumD.resolveBinding();
		} else if (node instanceof Name) {
			try{
				Name name = (Name) node;
				IBinding binding = name.resolveBinding();
				if (binding instanceof IVariableBinding) {
					// XXX This is to avoid the nasty .getDeclaringClass in
					// qualified name reference.
					IVariableBinding varBinding = (IVariableBinding) binding;
					typeBinding = varBinding.getType();
				} else if (binding instanceof IMethodBinding) {
					IMethodBinding methodBinding = (IMethodBinding) binding;
					typeBinding = methodBinding.getReturnType();
				} else {
					typeBinding = name.resolveTypeBinding();
				}
			}catch(Exception e){
				System.out.println("Error in name.resolveBinding().");
				exdist.ExceptionHandler.process(e, "Error in name.resolveBinding().");
			}
		} else if (node instanceof ClassInstanceCreation) { // added by Ye Wang, 02/19/2018
			ClassInstanceCreation cic = (ClassInstanceCreation) node;
			Type type = cic.getType();
			typeBinding = type.resolveBinding();
		} else if (node instanceof Expression) {
			Expression exp = (Expression) node;
			typeBinding = exp.resolveTypeBinding();
		} else if (node instanceof Type) {
			Type typeNode = (Type) node;
			typeBinding = typeNode.resolveBinding();
		}

		return typeBinding;
	}

	public static String getTypeString(ITypeBinding binding) {
		if (binding == null) {
			return "nil";
		} else {
			return binding.getQualifiedName();
		}
	}

	public static boolean isComplexName(String name) {
		ValidatorUtil.validateEmpty(name, "name", true);
		return name.contains(".");
	}

	public static boolean isConventionalClassName(String name) {
		String simpleName = getSimpleName(name);
		boolean isConventional = Character.isUpperCase(simpleName.charAt(0));
		isConventional = isConventional && !simpleName.toUpperCase().equals(simpleName);
		return isConventional;
	}

	public static boolean isEquivalent(IBinding binding1, IBinding binding2) {
		boolean isEquivalent = binding1.getKey().equals(binding2.getKey());
		if (!isEquivalent) {
			if (binding1 instanceof IVariableBinding && binding2 instanceof IVariableBinding) {
				isEquivalent = isEquivalent((IVariableBinding) binding1,
						(IVariableBinding) binding2);
			} else if (binding1 instanceof IMethodBinding && binding2 instanceof IMethodBinding) {
				isEquivalent = isEquivalent((IMethodBinding) binding1, (IMethodBinding) binding2);
			}
		}
		return isEquivalent;
	}

	public static boolean isEquivalent(IMethodBinding binding1, IMethodBinding binding2) {
		boolean isEquivalent = false;

		if (binding1.getName().equals(binding2.getName())
				&& getArgsLength(binding1) == getArgsLength(binding2)) {
			isEquivalent = binding1.getReturnType().getKey()
					.equals(binding2.getReturnType().getKey())
					|| binding1.getDeclaringClass().getKey()
							.equals(binding2.getDeclaringClass().getKey());
		}

		return isEquivalent;
	}

	public static boolean isEquivalent(IVariableBinding binding1, IVariableBinding binding2) {
		boolean isEquivalent = false;

		if (binding1.getName().equals(binding2.getName()) && binding1.isField()
				&& binding2.isField()) {
			isEquivalent = binding1.getType().getKey().equals(binding2.getType().getKey());

			if (!isEquivalent) {
				ITypeBinding dClass1 = binding1.getDeclaringClass();
				ITypeBinding dClass2 = binding2.getDeclaringClass();
				if ((dClass1 == null && dClass2 != null) || (dClass1 != null && dClass2 == null)) {
					isEquivalent = false;
				} else {
					isEquivalent = (dClass1 == null && dClass2 == null)
							|| dClass1.getKey().equals(dClass2.getKey());
				}
			}
		}

		return isEquivalent;
	}

	public static boolean isFullType(ITypeBinding typeBinding) {
		return !isProblemType(typeBinding) && !isUnknownType(typeBinding)
				&& !isMissingType(typeBinding) && getFirstMissingSuperType(typeBinding) == null;
	}

	/**
	 * 
	 * @param typeBinding
	 * @return True if the type declaration is missing (unknown is a missing type too).
	 */
	public static boolean isMissingType(ITypeBinding typeBinding) {
		org.eclipse.jdt.internal.compiler.lookup.TypeBinding binding = null;
		if (typeBinding instanceof TypeBinding) {
			TypeBinding tb = (TypeBinding) typeBinding;
			binding = tb.binding;

		}

		return (binding instanceof PPAType);
	}

	public static boolean isMissingType(
			org.eclipse.jdt.internal.compiler.lookup.TypeBinding typeBinding) {
		return (typeBinding instanceof PPAType);
	}

	public static boolean isNullType(
			org.eclipse.jdt.internal.compiler.lookup.TypeBinding typeBinding) {
		boolean isNull = false;

		if (typeBinding.isBaseType()) {
			BaseTypeBinding base = (BaseTypeBinding) typeBinding;
			isNull = new String(base.simpleName).equals("null");
		}

		return isNull;
	}

	public static boolean isPrimitiveName(String name) {
		return Arrays.binarySearch(PPATypeRegistry.PRIMITIVES, name) > PROBLEM_TYPE;
	}

	public static boolean isProblemType(ITypeBinding typeBinding) {
		org.eclipse.jdt.internal.compiler.lookup.TypeBinding binding = null;
		if (typeBinding instanceof TypeBinding) {
			TypeBinding tb = (TypeBinding) typeBinding;
			binding = tb.binding;

		}

		return isProblemType(binding);
	}

	public static boolean isProblemType(
			org.eclipse.jdt.internal.compiler.lookup.TypeBinding typeBinding) {
		return (typeBinding == null) || typeBinding instanceof ProblemReferenceBinding
				|| ((typeBinding.tagBits & TagBits.HasMissingType) != 0);
	}

	/**
	 * 
	 * @param binding1
	 * @param binding2
	 * @return true if binding1 is safer than binding2
	 */
	public static boolean isSafer(ITypeBinding binding1, ITypeBinding binding2) {
		return getSafetyValue(binding1) > getSafetyValue(binding2);
	}

	public static boolean isStarImport(String packageName) {
		ValidatorUtil.validateEmpty(packageName, "packageName", true);
		return packageName.endsWith("*");
	}

	public static boolean isSuperMissingType(ITypeBinding typeBinding) {
		return getFirstMissingSuperType(typeBinding) != null;
	}

	public static boolean isUnknownType(ITypeBinding typeBinding) {
		boolean isUnknown = false;
		org.eclipse.jdt.internal.compiler.lookup.TypeBinding binding = null;
		if (typeBinding instanceof TypeBinding) {
			TypeBinding tb = (TypeBinding) typeBinding;
			binding = tb.binding;

		}
		if (binding != null) {
			isUnknown = isUnknownType(binding);
		}

		return isUnknown;
	}

	public static boolean isUnknownType(
			org.eclipse.jdt.internal.compiler.lookup.TypeBinding typeBinding) {
		if(typeBinding!=null){
			return PPATypeRegistry.UNKNOWN_CLASS_FQN.equals(typeBinding.toString());
		}else{
			return true;
		}
	}

	@SuppressWarnings("rawtypes")
	private static void reportNewConstructorBinding(PPAIndexer indexer, PPAEngine engine,
			ITypeBinding unknownType, ClassInstanceCreation cic, ITypeBinding[] paramTypes,
			IMethodBinding newBinding) {
		TypeFact tFact = null;

		// Report params type.
		ITypeBinding[] newParams = newBinding.getParameterTypes();
		List args = cic.arguments();
		for (int i = 0; i < paramTypes.length; i++) {
			ASTNode arg = (ASTNode) args.get(i);
			if (indexer.isIndexable(arg)) {
				tFact = new TypeFact(indexer.getMainIndex(arg), paramTypes[i], TypeFact.UNKNOWN,
						newParams[i], TypeFact.SUBTYPE, TypeFact.METHOD_STRATEGY);
				engine.reportTypeFact(tFact);
			}
		}
	}

	@SuppressWarnings("rawtypes")
	private static void reportNewMethodBinding(PPAIndexer indexer, PPAEngine ppaEngine,
			ITypeBinding unknownType, ASTNode method, ITypeBinding[] previousParamTypes,
			IMethodBinding newBinding) {
		// Report return type.
		TypeFact tFact = new TypeFact(indexer.getMainIndex(method), unknownType, TypeFact.UNKNOWN,
				newBinding.getReturnType(), TypeFact.EQUALS, TypeFact.METHOD_STRATEGY);
		ppaEngine.reportTypeFact(tFact);

		// Report params type.
		ITypeBinding[] newParams = newBinding.getParameterTypes();
		List args = MethodInvocationUtil.getArguments(method);
		for (int i = 0; i < previousParamTypes.length; i++) {
			ASTNode arg = (ASTNode) args.get(i);
			if (indexer.isIndexable(arg)) {
				tFact = new TypeFact(indexer.getMainIndex(arg), previousParamTypes[i],
						TypeFact.UNKNOWN, newParams[i], TypeFact.SUBTYPE, TypeFact.METHOD_STRATEGY);
				ppaEngine.reportTypeFact(tFact);
			}
		}
	}

	public static ClassFile[] compileCU(CompilationUnit cu) {
		List<ClassFile> classFiles = new ArrayList<ClassFile>();
		DefaultBindingResolver resolver = (DefaultBindingResolver) cu.ast
				.getBindingResolver();
		CompilationUnitDeclaration compilationUnitDeclaration = (CompilationUnitDeclaration) resolver.newAstToOldAst
				.get(cu);
		try {
			// initial type binding creation
//			resolver.lookupEnvironment().buildTypeBindings(compilationUnitDeclaration, null /*no access restriction*/);
//
//			// binding resolution
//			resolver.lookupEnvironment().completeTypeBindings();
//			compilationUnitDeclaration.scope.faultInTypes();
//			compilationUnitDeclaration.scope.verifyMethods(resolver.lookupEnvironment().methodVerifier());
//			checkCompileCompilationUnitDeclaration(compilationUnitDeclaration);
//			compilationUnitDeclaration.resolve();
			checkCompileCompilationUnitDeclaration(compilationUnitDeclaration);
			compilationUnitDeclaration.analyseCode();
			checkCompileCompilationUnitDeclaration(compilationUnitDeclaration);
			compilationUnitDeclaration.generateCode();
			for (Object classFileObject : compilationUnitDeclaration.scope.referenceContext.compilationResult.compiledTypes
					.values()) {
				classFiles.add((ClassFile) classFileObject);
			}
		} catch (Exception e) {
			logger.error("Error while compiling a PPA source file", e);
			exdist.ExceptionHandler.process(e, "Error while compiling a PPA source file");
		}
		return classFiles.toArray(new ClassFile[0]);
	}

	public static void writeClassFile(ClassFile classFile, File baseDir) {
		try {
			char[][] compoundName = classFile.getCompoundName();
			String simpleName = new String(compoundName[compoundName.length - 1]);
			FileOutputStream fos = new FileOutputStream(new File(baseDir, simpleName
					+ CLASS_EXTENSION));
			fos.write(classFile.getBytes());
			fos.close();
		} catch (Exception e) {
			logger.error("Error while writing a compiled PPA class", e);
			exdist.ExceptionHandler.process(e, "Error while writing a compiled PPA class");
		}
	}

	private static void checkCompileCompilationUnitDeclaration(CompilationUnitDeclaration cud) {
		cud.ignoreFurtherInvestigation = false;
		cud.scope.referenceContext.compilationResult.problems = null;
		cud.scope.referenceContext.compilationResult.problemCount = 0;
		if (cud.types != null) {
			for (org.eclipse.jdt.internal.compiler.ast.TypeDeclaration td : cud.types) {
				checkCompileTypeDeclaration(td);
			}
		}
	}

	private static void checkCompileTypeDeclaration(
			org.eclipse.jdt.internal.compiler.ast.TypeDeclaration td) {
		td.bits = td.bits & ~org.eclipse.jdt.internal.compiler.ast.ASTNode.HasBeenGenerated;
		td.ignoreFurtherInvestigation = false;
		if (td.methods != null) {
			for (AbstractMethodDeclaration amd : td.methods) {
				checkCompileMethodDeclaration(amd);
			}
		}
		if (td.memberTypes != null) {
			for (org.eclipse.jdt.internal.compiler.ast.TypeDeclaration memberTd : td.memberTypes) {
				checkCompileTypeDeclaration(memberTd);
			}
		}
	}

	private static void checkCompileMethodDeclaration(AbstractMethodDeclaration md) {
		md.bits = md.bits & ~org.eclipse.jdt.internal.compiler.ast.ASTNode.HasBeenGenerated;
		md.ignoreFurtherInvestigation = false;
		if (md.isConstructor()) {
			checkConstructor((ConstructorDeclaration) md);
		}
	}

	private static void checkConstructor(ConstructorDeclaration md) {
		if (md.constructorCall != null
				&& md.constructorCall.binding instanceof ProblemMethodBinding) {
			md.constructorCall = null;
		}
	}
}
