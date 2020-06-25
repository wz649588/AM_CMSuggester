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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.jdt.core.compiler.CharOperation;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.BindingResolver;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.IBinding;
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.eclipse.jdt.core.dom.ImportDeclaration;
import org.eclipse.jdt.core.dom.TypeBinding;
import org.eclipse.jdt.core.dom.VariableBinding;
import org.eclipse.jdt.internal.compiler.ast.ParameterizedSingleTypeReference;
import org.eclipse.jdt.internal.compiler.classfmt.ClassFileConstants;
import org.eclipse.jdt.internal.compiler.lookup.ArrayBinding;
import org.eclipse.jdt.internal.compiler.lookup.BaseTypeBinding;
import org.eclipse.jdt.internal.compiler.lookup.Binding;
import org.eclipse.jdt.internal.compiler.lookup.FieldBinding;
import org.eclipse.jdt.internal.compiler.lookup.MethodBinding;
import org.eclipse.jdt.internal.compiler.lookup.PPATypeBinding;
import org.eclipse.jdt.internal.compiler.lookup.PPATypeBindingOptions;
import org.eclipse.jdt.internal.compiler.lookup.PackageBinding;
import org.eclipse.jdt.internal.compiler.lookup.ParameterizedTypeBinding;
import org.eclipse.jdt.internal.compiler.lookup.ReferenceBinding;
import org.eclipse.jdt.internal.compiler.lookup.TypeConstants;
import org.eclipse.jdt.internal.core.DefaultWorkingCopyOwner;
import org.eclipse.jdt.internal.core.JavaProject;
import org.eclipse.jdt.internal.core.NameLookup;

import ca.mcgill.cs.swevo.ppa.PPAASTUtil;

public class PPATypeRegistry {

	private Map<CompilationUnit, Map<String, ITypeBinding>> cuTypeBindings = new HashMap<CompilationUnit, Map<String, ITypeBinding>>();

	private Map<String, ITypeBinding> typeBindings = new HashMap<String, ITypeBinding>();

	private Map<String, PackageBinding> packageBindings = new HashMap<String, PackageBinding>();

	private NameLookup lookup;

	private JavaProject javaProject;

	public final static String UNKNOWN_PACKAGE = "UNKNOWNP";

	public final static String UNKNWON_CLASS = "UNKNOWN";

	public final static String UNKNOWN_CLASS_FQN = UNKNOWN_PACKAGE + "."
			+ UNKNWON_CLASS;

	public final static String JAVA_LANG_PACKAGE = "java.lang";

	public final static String[] PRIMITIVES = { "boolean", "byte", "char",
			"double", "float", "int", "long", "short", "void" };

	public PPATypeRegistry(JavaProject javaProject) {
		this.javaProject = javaProject;
		try {
			lookup = this.javaProject
					.newNameLookup(DefaultWorkingCopyOwner.PRIMARY);
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	public void clear() {
		cuTypeBindings.clear();
		typeBindings.clear();
		packageBindings.clear();
	}

	// public void init(BindingResolver resolver) {
	// }

	public IMethodBinding createConstructor(ITypeBinding declaringClass,
			ITypeBinding[] paramTypes, PPADefaultBindingResolver resolver) {
		ReferenceBinding container = null;
		if (declaringClass instanceof TypeBinding) {
			TypeBinding tBinding = (TypeBinding) declaringClass;
			container = (ReferenceBinding) tBinding.binding;
		} else {
			container = getInternalUnknownBinding(resolver);
		}
		MethodBinding mBinding = getInternalConstructorBinding(container,
				paramTypes.length, paramTypes, resolver);
		org.eclipse.jdt.core.dom.MethodBinding newBinding = new org.eclipse.jdt.core.dom.MethodBinding(
				resolver, mBinding);
		return newBinding;
	}

	private IVariableBinding createFieldBinding(String fieldName,
			ITypeBinding container, ITypeBinding fieldType,
			BindingResolver resolver, boolean unknownContainer) {
		IVariableBinding newFieldBinding = null;

		if (container instanceof TypeBinding
				&& fieldType instanceof TypeBinding) {
			TypeBinding containerType = (org.eclipse.jdt.core.dom.TypeBinding) container;
			TypeBinding fieldTypeType = (org.eclipse.jdt.core.dom.TypeBinding) fieldType;
			FieldBinding fBinding = null;

			if (containerType.binding instanceof ArrayBinding) {
				if (!fieldName.equals("length")) {
					// Should not happen.
				}
				fBinding = ArrayBinding.ArrayLength;
			} else {
				org.eclipse.jdt.internal.compiler.lookup.TypeBinding containerBinding = containerType.binding;

				// This was to ensure that a field was not created for a full
				// type.
				// But we want to allow this.
				// if (unknownContainer) {
				// containerBinding = getInternalUnknownBinding(resolver);
				// containerType = (TypeBinding) getUnknownBinding(resolver);
				// }

				fBinding = new FieldBinding(fieldName.toCharArray(),
						fieldTypeType.binding, ClassFileConstants.AccPublic,
						(ReferenceBinding) containerBinding, null);
				if (!PPABindingsUtil.isUnknownType(containerType)
						&& containerType.binding instanceof PPATypeBinding) {
					PPATypeBinding containerPPABinding = (PPATypeBinding) containerType.binding;
					containerPPABinding.getFieldsList().add(fBinding);
				}
			}

			newFieldBinding = new VariableBinding(resolver, fBinding);
		}

		return newFieldBinding;
	}

	private MethodBinding createInternalMethodBinding(char[] name,
			org.eclipse.jdt.internal.compiler.lookup.TypeBinding returnType,
			ReferenceBinding container, int numberOfParams,
			BindingResolver resolver) {
		org.eclipse.jdt.internal.compiler.lookup.TypeBinding[] params = new org.eclipse.jdt.internal.compiler.lookup.TypeBinding[numberOfParams];

		for (int i = 0; i < numberOfParams; i++) {
			params[i] = getInternalUnknownBinding(resolver);
		}

		return new MethodBinding(0, name, returnType, params,
				new ReferenceBinding[0], container);
	}

	private MethodBinding createInternalMethodBinding(char[] name,
			org.eclipse.jdt.internal.compiler.lookup.TypeBinding returnType,
			ReferenceBinding container, int numberOfParams,
			ITypeBinding[] paramBindings, BindingResolver resolver) {
		org.eclipse.jdt.internal.compiler.lookup.TypeBinding[] params = new org.eclipse.jdt.internal.compiler.lookup.TypeBinding[numberOfParams];

		for (int i = 0; i < numberOfParams; i++) {
			ITypeBinding tempBinding = paramBindings[i];
			if (tempBinding.isNullType()) {
				params[i] = getInternalUnknownBinding(resolver);
			} else if (tempBinding instanceof TypeBinding) {
				TypeBinding tempBinding2 = (TypeBinding) tempBinding;
				params[i] = tempBinding2.binding;
			}
		}

		return new MethodBinding(0, name, returnType, params,
				new ReferenceBinding[0], container);
	}

	public IMethodBinding createMethodBinding(String name,
			ITypeBinding container, ITypeBinding returnType,
			ITypeBinding[] paramBindings, BindingResolver resolver) {
		MethodBinding mBinding = null;
		int size = paramBindings.length;
		org.eclipse.jdt.internal.compiler.lookup.TypeBinding internalReturnType = PPABindingsUtil
				.getInternalTypeBinding(returnType);
		org.eclipse.jdt.internal.compiler.lookup.TypeBinding tempContainerType = PPABindingsUtil
				.getInternalTypeBinding(container);
		ReferenceBinding internalContainerType = null;

		// XXX Special case: happens probably only with local variables inside
		// anon classes.
		if (tempContainerType.isBaseType()) {
			internalContainerType = getInternalUnknownBinding(resolver);
		} else {
			try{
				internalContainerType = (ReferenceBinding) PPABindingsUtil
						.getInternalTypeBinding(container);
			}catch(Exception e){
				System.out.println("zhh error at public IMethodBinding createMethodBinding(String name,. ");
				exdist.ExceptionHandler.process(e, "zhh error at public IMethodBinding createMethodBinding(String name,. ");
			}
		}
		org.eclipse.jdt.internal.compiler.lookup.TypeBinding[] internalParamTypes = new org.eclipse.jdt.internal.compiler.lookup.TypeBinding[size];

		for (int i = 0; i < size; i++) {
			internalParamTypes[i] = PPABindingsUtil
					.getInternalTypeBinding(paramBindings[i]);
		}
		mBinding = new MethodBinding(ClassFileConstants.AccPublic,
				name.toCharArray(), internalReturnType, internalParamTypes,
				new ReferenceBinding[0], internalContainerType);

		if (!PPABindingsUtil.isUnknownType(internalContainerType)
				&& PPABindingsUtil.isMissingType(internalContainerType)) {
			if (internalContainerType instanceof PPATypeBinding) {
				PPATypeBinding ppaTypeBinding = (PPATypeBinding) internalContainerType;
				ppaTypeBinding.getMethodsList().add(mBinding);
			}
		}

		return new org.eclipse.jdt.core.dom.MethodBinding(resolver, mBinding);
	}

	private ITypeBinding createParameterizedTypeBinding(ITypeBinding base,
			ParameterizedSingleTypeReference typeReference,
			BindingResolver resolver) {
		TypeBinding tBinding = null;
		ReferenceBinding realType = (ReferenceBinding) PPABindingsUtil
				.getInternalTypeBinding(base);
		ReferenceBinding rBinding = getParameterizedTypeBinding(realType,
				typeReference, resolver);
		tBinding = new TypeBinding(resolver, rBinding);
		return tBinding;
	}

	public ITypeBinding createTypeBinding(String name, String fqn,
			BindingResolver resolver, CompilationUnit cu,
			PPATypeBindingOptions options) {
		char[][] cName = PPABindingsUtil.getArrayFromName(fqn);
		TypeBinding tBinding = null;
		org.eclipse.jdt.internal.compiler.lookup.TypeBinding tempBinding = null;
		try {
			tempBinding = resolver.scope().getType(cName, cName.length);
		} catch (Exception e) {
			// This is usually when there is a problem with fully qualified
			// name.
			fqn = UNKNOWN_PACKAGE + "." + fqn;
		}
		if (!PPABindingsUtil.isProblemType(tempBinding)) {
			// tempBinding.tagBits = (tempBinding.tagBits ^
			// TagBits.HasMissingType);
			tBinding = new TypeBinding(resolver, tempBinding);
		} else {
			String packageName = PPABindingsUtil.getPackage(fqn);
			PackageBinding pBinding = getInternalPackageBinding(resolver,
					packageName);
			PPATypeBinding stBinding = new PPATypeBinding(cName, pBinding,
					options);
			tBinding = new TypeBinding(resolver, stBinding);
		}

		if (cu != null) {
			putCuTypeBinding(cu, name, tBinding);
		}

		typeBindings.put(fqn, tBinding);
		return tBinding;
	}

	private String findJavaLangType(String name) {
		String fullName = null;
		String tempName = PPABindingsUtil.getFQN(JAVA_LANG_PACKAGE, name);
		if (lookup.findType(tempName, false, NameLookup.ACCEPT_ALL) != null) {
			fullName = tempName;
		}

		return fullName;
	}

	public void fixBinary(ASTNode node, ITypeBinding newType) {
		BindingResolver resolver = node.getAST().getBindingResolver();
		if (resolver instanceof PPADefaultBindingResolver) {
			PPADefaultBindingResolver ppaResolver = (PPADefaultBindingResolver) resolver;
			ppaResolver.fixBinary(node, newType);
		}
	}
	
	public void fixConditional(ASTNode node, ITypeBinding newType) {
		BindingResolver resolver = node.getAST().getBindingResolver();
		if (resolver instanceof PPADefaultBindingResolver) {
			PPADefaultBindingResolver ppaResolver = (PPADefaultBindingResolver) resolver;
			ppaResolver.fixConditional(node, newType);
		}
	}

	private IVariableBinding fixExpectedType(IVariableBinding fieldBinding,
			ITypeBinding expectedFieldType, BindingResolver resolver) {
		IVariableBinding newFieldBinding = null;
		ITypeBinding container = fieldBinding.getDeclaringClass();

		if (container instanceof TypeBinding
				&& expectedFieldType instanceof TypeBinding) {
			TypeBinding containerType = (org.eclipse.jdt.core.dom.TypeBinding) container;
			TypeBinding fieldTypeType = (org.eclipse.jdt.core.dom.TypeBinding) expectedFieldType;

			FieldBinding fBinding = new FieldBinding(fieldBinding.getName()
					.toCharArray(), fieldTypeType.binding,
					ClassFileConstants.AccPublic,
					(ReferenceBinding) containerType.binding, null);
			if (!PPABindingsUtil.isUnknownType(containerType)
					&& containerType.binding instanceof PPATypeBinding) {
				PPATypeBinding containerPPABinding = (PPATypeBinding) containerType.binding;
				FieldBinding toRemove = containerPPABinding.getField(
						fBinding.name, true);
				containerPPABinding.getFieldsList().remove(toRemove);
				containerPPABinding.getFieldsList().add(fBinding);
			}
			newFieldBinding = new VariableBinding(resolver, fBinding);
		}

		return newFieldBinding;
	}

	public void fixUnary(ASTNode node, ITypeBinding newType) {
		BindingResolver resolver = node.getAST().getBindingResolver();
		if (resolver instanceof PPADefaultBindingResolver) {
			PPADefaultBindingResolver ppaResolver = (PPADefaultBindingResolver) resolver;
			ppaResolver.fixUnary(node, newType);
		}
	}

	public ITypeBinding getArrayTypeBinding(ITypeBinding factType, ASTNode node) {
		return getArrayTypeBinding(factType, node.getAST().getBindingResolver());
	}

	private ITypeBinding getArrayTypeBinding(ITypeBinding baseType,
			BindingResolver bindingResolver) {
		ITypeBinding newBinding = null;
		if (baseType instanceof TypeBinding) {
			TypeBinding tBinding = (TypeBinding) baseType;
			newBinding = new TypeBinding(bindingResolver, new ArrayBinding(
					tBinding.binding, 1, bindingResolver.lookupEnvironment()));
		}

		return newBinding;
	}

	private ITypeBinding getCuTypeBinding(CompilationUnit cu, String name) {
		ITypeBinding binding = null;

		if (cu != null && cuTypeBindings.containsKey(cu)) {
			binding = cuTypeBindings.get(cu).get(name);
		}

		return binding;
	}

	public IVariableBinding getFieldBinding(String fieldName,
			ITypeBinding container, ITypeBinding expectedFieldType,
			BindingResolver resolver) {
		IVariableBinding fieldBinding = null;
		boolean shouldBeUnknown = false;

		if (!PPABindingsUtil.isUnknownType(container)) {
			fieldBinding = PPABindingsUtil.findField(container, fieldName);
			shouldBeUnknown = PPABindingsUtil.isFullType(container)
					&& fieldBinding == null;
		}
		// Create the fieldBinding
		if (fieldBinding == null) {
			fieldBinding = createFieldBinding(fieldName, container,
					expectedFieldType, resolver, shouldBeUnknown);
//			fieldBinding.getDeclaringClass();//added by nameng
		}
		return fieldBinding;
	}

	public IVariableBinding getFieldBindingWithType(String fieldName,
			ITypeBinding container, ITypeBinding expectedFieldType,
			BindingResolver resolver) {
		IVariableBinding fieldBinding = null;
		boolean shouldBeUnknown = false;

		if (!PPABindingsUtil.isUnknownType(container)) {
			fieldBinding = PPABindingsUtil.findField(container, fieldName);
			shouldBeUnknown = PPABindingsUtil.isFullType(container)
					&& fieldBinding == null;
		}

		// Create the fieldBinding
		if (fieldBinding == null) {
			fieldBinding = createFieldBinding(fieldName, container,
					expectedFieldType, resolver, shouldBeUnknown);
		} else if (!fieldBinding.getType().isEqualTo(expectedFieldType)) {
			fieldBinding = fixExpectedType(fieldBinding, expectedFieldType,
					resolver);
		}

		return fieldBinding;
	}

	public String getFullName(String name, CompilationUnit cu) {
		String fullName = name;

		if (cu != null && !PPABindingsUtil.isComplexName(name)
				&& !PPABindingsUtil.isPrimitiveName(name)) {
			String fqnImport = null;
			String packageName = PPAASTUtil.getPackageName(cu);
			boolean hasStar = false;
			List<String> packages = new ArrayList<String>();

			for (Object importObject : cu.imports()) {
				ImportDeclaration importDec = (ImportDeclaration) importObject;
				String fqn = importDec.getName().getFullyQualifiedName();
				if (importDec.isOnDemand()) {
					hasStar = true;
					packages.add(importDec.getName().getFullyQualifiedName());
				} else if (PPABindingsUtil.getSimpleName(fqn).equals(name)) {
					fqnImport = fqn;
				}
			}

			if (fqnImport != null) {
				fullName = fqnImport;
			} else {
				// First, search if this is a java.lang class.
				fullName = findJavaLangType(name);

				// Else, look using the package rules.
				if (fullName == null && hasStar) {
					fullName = getFullNameFromPackages(name, packageName,
							packages);
				} else if (fullName == null) {
					fullName = PPABindingsUtil.getFQN(packageName, name);
				}
			}
		}

		return fullName;
	}

	private String getFullNameFromPackages(String name, String cuPackageName,
			List<String> packages) {
		String fullName = null;
		boolean onlyJavaImports = true;
		for (String packageName : packages) {
			if (!packageName.startsWith("java.")) {
				onlyJavaImports = false;
			}
			String tempName = PPABindingsUtil.getFQN(packageName, name);
			if (lookup.findType(tempName, false, NameLookup.ACCEPT_ALL) != null) {
				if (fullName != null) {
					// It means multiple * imports contain this type.
					// In normal circumstances, it would mean that the type is
					// in the same package
					// as the cu
					// But for now, we will abort, because we live in uncertain
					// environments.
					fullName = null;
					break;
				} else {
					fullName = tempName;
				}
			}
		}

		if (fullName == null) {
			if (onlyJavaImports) {
				fullName = PPABindingsUtil.getFQN(cuPackageName, name);
			} else {
				fullName = PPABindingsUtil.getFQN(UNKNOWN_PACKAGE, name);
			}
		}

		return fullName;
	}

	public MethodBinding getInternalConstructorBinding(
			ReferenceBinding container, int numberOfParams,
			ITypeBinding[] paramBindings, BindingResolver resolver) {
		MethodBinding mBinding = null;
		if (container instanceof PPATypeBinding
				&& !container.toString().equals(UNKNOWN_CLASS_FQN)) {
			PPATypeBinding ppaContainer = (PPATypeBinding) container;
			// mBinding =
			// ppaContainer.getUnknownConstructor(TypeConstants.INIT,numberOfParams);
			// if (mBinding == null) {
			mBinding = createInternalMethodBinding(TypeConstants.INIT,
					org.eclipse.jdt.internal.compiler.lookup.TypeBinding.VOID,
					container, numberOfParams, paramBindings, resolver);
			ppaContainer.addConstructor(mBinding);
			// }
		} else {
			mBinding = createInternalMethodBinding(TypeConstants.INIT,
					org.eclipse.jdt.internal.compiler.lookup.TypeBinding.VOID,
					container, numberOfParams, paramBindings, resolver);
		}

		return mBinding;
	}

	public FieldBinding getInternalFieldBinding(IVariableBinding varBinding) {
		FieldBinding fBinding = null;

		org.eclipse.jdt.internal.compiler.lookup.TypeBinding container = ((TypeBinding) varBinding
				.getDeclaringClass()).binding;
		org.eclipse.jdt.internal.compiler.lookup.TypeBinding fieldType = ((TypeBinding) varBinding
				.getType()).binding;

		fBinding = new FieldBinding(varBinding.getName().toCharArray(),
				fieldType, ClassFileConstants.AccPublic,
				(ReferenceBinding) container, null);

		return fBinding;
	}

	private PackageBinding getInternalPackageBinding(BindingResolver resolver,
			String packageName) {
		char[][] pName = CharOperation.NO_CHAR_CHAR;
		if (packageName != null) {
			pName = PPABindingsUtil.getArrayFromName(packageName);
		} else {
			return new PackageBinding(resolver.lookupEnvironment());
		}

		PackageBinding pBinding = packageBindings.get(packageName);

		// Look for a specific binding...
		if (pBinding == null) {
			Binding binding = resolver.scope().getTypeOrPackage(pName);
			if (binding != null && binding instanceof PackageBinding) {
				pBinding = (PackageBinding) binding;
				packageBindings.put(packageName, pBinding);
			}
		}

		// Must create the binding
		if (pBinding == null) {
			String packageNameTemp = PPABindingsUtil.getPackage(packageName);
			if (packageNameTemp == null) {
				pBinding = new PackageBinding(pName[0],
						resolver.lookupEnvironment());
			} else {
				PackageBinding pBindingParent = getInternalPackageBinding(
						resolver, packageNameTemp);
				pBinding = new PackageBinding(pName, pBindingParent,
						resolver.lookupEnvironment());
			}

			packageBindings.put(packageName, pBinding);
		}

		return pBinding;
	}

	public PPATypeBinding getInternalUnknownBinding(BindingResolver resolver) {
		TypeBinding tBinding = (TypeBinding) getUnknownBinding(resolver);
		return (PPATypeBinding) tBinding.binding;
	}

	public ReferenceBinding getParameterizedTypeBinding(
			ReferenceBinding realType,
			ParameterizedSingleTypeReference typeReference,
			BindingResolver resolver) {
		int length = typeReference.typeArguments.length;
		org.eclipse.jdt.internal.compiler.lookup.TypeBinding[] params = new org.eclipse.jdt.internal.compiler.lookup.TypeBinding[length];
		for (int i = 0; i < length; i++) {
			params[i] = typeReference.typeArguments[i].resolvedType;
		}

		ParameterizedTypeBinding newType = new ParameterizedTypeBinding(
				realType, params, realType.enclosingType(),
				resolver.lookupEnvironment());

		return newType;
	}

	public MethodBinding getInternalUnknownConstructorBinding(
			ReferenceBinding container, int numberOfParams,
			BindingResolver resolver) {
		MethodBinding mBinding = null;
		if (container instanceof PPATypeBinding
				&& !container.toString().equals(UNKNOWN_CLASS_FQN)) {
			PPATypeBinding ppaContainer = (PPATypeBinding) container;
			mBinding = ppaContainer.getUnknownConstructor(TypeConstants.INIT,
					numberOfParams);
			if (mBinding == null) {
				mBinding = createInternalMethodBinding(
						TypeConstants.INIT,
						org.eclipse.jdt.internal.compiler.lookup.TypeBinding.VOID,
						container, numberOfParams, resolver);
				ppaContainer.addUnknownConstructor(mBinding);
			}
		} else {
			mBinding = createInternalMethodBinding(TypeConstants.INIT,
					org.eclipse.jdt.internal.compiler.lookup.TypeBinding.VOID,
					container, numberOfParams, resolver);
		}

		return mBinding;
	}

	private FieldBinding getInternalUnknownFieldBinding(char[] name,
			BindingResolver resolver) {
		PPATypeBinding unknown = getInternalUnknownBinding(resolver);

		return new FieldBinding(name, unknown, ClassFileConstants.AccPublic,
				unknown, null);
	}

	public MethodBinding getInternalUnknownMethodBinding(char[] name,
			int numberOfParams, BindingResolver resolver) {

		return createInternalMethodBinding(name,
				getInternalUnknownBinding(resolver),
				getInternalUnknownBinding(resolver), numberOfParams, resolver);
	}

	public ITypeBinding getPrimitiveBinding(String name, ASTNode node) {
		return getPrimitiveBinding(name, node.getAST().getBindingResolver());
	}

	public ITypeBinding getPrimitiveBinding(String name,
			BindingResolver resolver) {
		if (!PPABindingsUtil.isPrimitiveName(name)) {
			return null;
		}

		ITypeBinding tBinding = typeBindings.get(name);

		if (tBinding == null) {
			if (name.equals("int")) {
				tBinding = new TypeBinding(resolver, BaseTypeBinding.INT);
				typeBindings.put(name, tBinding);
			} else if (name.equals("boolean")) {
				tBinding = new TypeBinding(resolver, BaseTypeBinding.BOOLEAN);
				typeBindings.put(name, tBinding);
			} else if (name.equals("void")) {
				tBinding = new TypeBinding(resolver, BaseTypeBinding.VOID);
				typeBindings.put(name, tBinding);
			} else if (name.equals("char")) {
				tBinding = new TypeBinding(resolver, BaseTypeBinding.CHAR);
				typeBindings.put(name, tBinding);
			} else if (name.equals("byte")) {
				tBinding = new TypeBinding(resolver, BaseTypeBinding.BYTE);
				typeBindings.put(name, tBinding);
			} else if (name.equals("short")) {
				tBinding = new TypeBinding(resolver, BaseTypeBinding.SHORT);
				typeBindings.put(name, tBinding);
			} else if (name.equals("long")) {
				tBinding = new TypeBinding(resolver, BaseTypeBinding.LONG);
				typeBindings.put(name, tBinding);
			} else if (name.equals("double")) {
				tBinding = new TypeBinding(resolver, BaseTypeBinding.DOUBLE);
				typeBindings.put(name, tBinding);
			} else if (name.equals("float")) {
				tBinding = new TypeBinding(resolver, BaseTypeBinding.FLOAT);
				typeBindings.put(name, tBinding);
			}
		}

		return tBinding;
	}

	public ITypeBinding getTypeBinding(CompilationUnit cu, String name,
			BindingResolver resolver, boolean isArray,
			PPATypeBindingOptions options) {
		// init(resolver);
		ITypeBinding tBinding = null;
		String fqn = getFullName(name, cu);

		// Is it a primitive?
		if (PPABindingsUtil.isPrimitiveName(name)) {
			tBinding = getPrimitiveBinding(name, resolver);
		}
		// Is it the full name?
		else if (PPABindingsUtil.isComplexName(name)) {
			tBinding = typeBindings.get(name);
		}
		// Else, do we know the full name?
		else {
			tBinding = typeBindings.get(name);
		}

		// Do we know this type in the context of this cu?
		if (tBinding == null) {
			tBinding = getCuTypeBinding(cu, name);
		}

		// We cannot find it in the cache, we need to create the type.
		if (tBinding == null) {
			tBinding = createTypeBinding(name, fqn, resolver, cu, options);
		}

		if (!tBinding.isArray() && isArray) {
			tBinding = getArrayTypeBinding(tBinding, resolver);
		}

		return tBinding;
	}

	public ITypeBinding getUnknownBinding(BindingResolver resolver) {
		ITypeBinding tBinding = typeBindings.get(UNKNOWN_CLASS_FQN);
		if (tBinding == null) {
			tBinding = createTypeBinding(UNKNWON_CLASS, UNKNOWN_CLASS_FQN,
					resolver, null, new PPATypeBindingOptions());
			typeBindings.put(UNKNOWN_CLASS_FQN, tBinding);
		}
		return tBinding;
	}

	public IMethodBinding getUnknownConstructorBinding(ITypeBinding container,
			int numberOfParams, BindingResolver resolver) {
		TypeBinding tBinding = (TypeBinding) container;
		ReferenceBinding rBinding = (ReferenceBinding) tBinding.binding;

		return new org.eclipse.jdt.core.dom.MethodBinding(resolver,
				getInternalUnknownConstructorBinding(rBinding, numberOfParams,
						resolver));
	}

	public IVariableBinding getUnknownFieldBinding(char[] name,
			BindingResolver resolver) {
		return new VariableBinding(resolver, getInternalUnknownFieldBinding(
				name, resolver));
	}

	public IMethodBinding getUnknownMethodBinding(char[] name,
			int numberOfParams, BindingResolver resolver) {
		return new org.eclipse.jdt.core.dom.MethodBinding(resolver,
				getInternalUnknownMethodBinding(name, numberOfParams, resolver));
	}

	private void putCuTypeBinding(CompilationUnit cu, String name,
			ITypeBinding binding) {

		if (!cuTypeBindings.containsKey(cu)) {
			cuTypeBindings.put(cu, new HashMap<String, ITypeBinding>());
		}

		Map<String, ITypeBinding> bindings = cuTypeBindings.get(cu);
		bindings.put(name, binding);
	}

	public IBinding getParameterizedTypeBinding(CompilationUnit cu,
			String name, PPADefaultBindingResolver resolver,
			ParameterizedSingleTypeReference stref,
			PPATypeBindingOptions options) {
		ITypeBinding tBinding = null;
		String fqn = getFullName(name, cu);

		// Is it a primitive?
		if (PPABindingsUtil.isPrimitiveName(name)) {
			tBinding = getPrimitiveBinding(name, resolver);
		}
		// Is it the full name?
		else if (PPABindingsUtil.isComplexName(name)) {
			tBinding = typeBindings.get(name);
		}
		// Else, do we know the full name?
		else {
			tBinding = typeBindings.get(name);
		}

		// Do we know this type in the context of this cu?
		if (tBinding == null) {
			tBinding = getCuTypeBinding(cu, name);
		}

		// We cannot find it in the cache, we need to create the type.
		if (tBinding == null) {
			tBinding = createTypeBinding(name, fqn, resolver, cu, options);
		}

		tBinding = createParameterizedTypeBinding(tBinding, stref, resolver);

		return tBinding;
	}

	public ITypeBinding getPossibleDeclaringType(SimpleName name,
			 ITypeBinding thisType) {
		// TODO Auto-generated method stub
		ITypeBinding iType = null;
		
		if(thisType!=null){
			ITypeBinding parent = thisType.getSuperclass();
			while(parent!=null){
				for(IVariableBinding varB:parent.getDeclaredFields()){
					String name1 = name.toString();
					String name2 = varB.getName();
					if(name1.compareTo(name2)==0){
						iType = parent;
						break;
					}
				}
				parent = parent.getSuperclass();
			}
			if(iType==null){
				iType = thisType;
			}
		}
//		for(ITypeBinding t:this.typeBindings.values()){
//			if(t!=null&&t.getDeclaredFields()!=null){
//				for(IVariableBinding varB:t.getDeclaredFields()){
//					String name1 = name.toString();
//					String name2 = varB.getName();
//					if(name1.compareTo(name2)==0){
//						iType = t;
//						break;
//					}
//				}
//			}
//		}
		
		return iType;
	}

	// private ITypeBinding createTypeBinding(String fqn,BindingResolver
	// resolver) {
	// String com = "com";
	// String prologique = "prologique";
	// PPATypeBinding stBinding = new PPATypeBinding(new char[][]
	// {com.toCharArray(),prologique.toCharArray(),fqn.toCharArray()},prologiquePackage);
	// TypeBinding tBinding = new TypeBinding(resolver, stBinding);
	// return tBinding;
	// }

}
