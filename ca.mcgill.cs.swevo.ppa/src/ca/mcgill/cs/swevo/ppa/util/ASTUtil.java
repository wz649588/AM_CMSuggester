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
package ca.mcgill.cs.swevo.ppa.util;

import static org.eclipse.jdt.core.dom.PPABindingsUtil.getTypeString;

import org.eclipse.jdt.core.dom.IAnnotationBinding;
import org.eclipse.jdt.core.dom.IBinding;
import org.eclipse.jdt.core.dom.IMemberValuePairBinding;
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.eclipse.jdt.core.dom.PPATypeRegistry;


/**
 * <p>
 * Various AST-related utilities based on SemDiff ASTUtil.
 * </p>
 * 
 * <p>
 * <strong>Type Handle</strong>
 * </p>
 * <p>
 * T:TYPE_NAME or <br>
 * T:TYPE_NAME$INTERNAL_TYPE_NAME
 * </p>
 * 
 * <p>
 * <strong>Field Handle</strong>
 * </p>
 * <p>
 * F:TYPE_NAME:FIELD_TYPE_NAME:FIELD_NAME
 * </p>
 * 
 * <p>
 * <strong>Method Handle</strong>
 * </p>
 * <p>
 * M:TYPE_NAME:METHOD_NAME:PARAM_TYPE1:PARAM_TYPE2:etc.
 * </p>
 * 
 * 
 * @author barthelemy
 * 
 */
public class ASTUtil {
	// public final static String CONSTRUCTOR = "<init>";

	public final static String HANDLE_SEPARATOR = ":";

	public final static String TYPE_SEPARATOR = "$";

	public final static String TYPE_KIND = "T";

	public final static String METHOD_KIND = "M";

	public final static String FIELD_KIND = "F";

	public final static String CU_KIND = "C";

	public final static String CALL_KIND = "Z";

	// Only for augmented handles

	public final static String AUGMENTED_HANDLE_SEPARATOR = "!";

	public final static String ANNOTATION_KIND = "A";

	public final static String ANNOTATION_PARAMETER_KIND = "P";

	public final static String ENUM_KIND = "E";

	public final static String ENUM_VALUE_KIND = "V";

	// private final static Logger logger = Logger.getLogger(ASTUtil.class);

	public static String getHandle(IBinding binding) {
		return getHandle(binding, false);
	}

	public static String getHandle(IBinding binding, boolean augmented) {
		StringBuffer handle = new StringBuffer();

		if (binding instanceof IMethodBinding) {
			getMethodBindingHandle(binding, augmented, handle);
		} else if (binding instanceof ITypeBinding) {
			getTypeBindingHandle(binding, augmented, handle);
		} else if (binding instanceof IAnnotationBinding) {
			IAnnotationBinding aBinding = (IAnnotationBinding) binding;
			getTypeBindingHandle(aBinding.getAnnotationType(), augmented, handle);
		} else if (binding instanceof IVariableBinding) {
			getFieldBindingHandle(binding, augmented, handle);
		} else if (binding instanceof IMemberValuePairBinding) {
			IMemberValuePairBinding vBinding = (IMemberValuePairBinding) binding;
			getMethodBindingHandle(vBinding.getMethodBinding(), augmented, handle);
		}

		return handle.toString();
	}

	private static void getFieldBindingHandle(IBinding binding,
			boolean augmented, StringBuffer handle) {
		IVariableBinding vBinding = (IVariableBinding) binding;
		handle.append(FIELD_KIND);
		if (augmented) {
			handle.append(AUGMENTED_HANDLE_SEPARATOR);
			if (vBinding.isEnumConstant()) {
				handle.append(ENUM_VALUE_KIND);
			} else {
				handle.append(FIELD_KIND);
			}
		}
		handle.append(HANDLE_SEPARATOR);
		handle.append(getNonEmptyTypeString(getTypeString(vBinding
				.getDeclaringClass())));
		handle.append(HANDLE_SEPARATOR);
		handle.append(getNonEmptyTypeString(getTypeString(vBinding
				.getType())));
		handle.append(HANDLE_SEPARATOR);
		handle.append(getNonEmptyName(vBinding.getName()));
	}

	private static void getTypeBindingHandle(IBinding binding,
			boolean augmented, StringBuffer handle) {
		ITypeBinding tBinding = (ITypeBinding) binding;
		handle.append(TYPE_KIND);
		if (augmented) {
			handle.append(AUGMENTED_HANDLE_SEPARATOR);
			if (tBinding.isAnnotation()) {
				handle.append(ANNOTATION_KIND);
			} else if (tBinding.isEnum()) {
				handle.append(ENUM_KIND);
			} else {
				handle.append(TYPE_KIND);
			}
		}
		handle.append(HANDLE_SEPARATOR);
		handle.append(getNonEmptyTypeString(getTypeString(tBinding)));
	}

	private static void getMethodBindingHandle(IBinding binding,
			boolean augmented, StringBuffer handle) {
		IMethodBinding methodBinding = (IMethodBinding) binding;
		handle.append(METHOD_KIND);
		if (augmented) {
			handle.append(AUGMENTED_HANDLE_SEPARATOR);
			if (methodBinding.isAnnotationMember()) {
				handle.append(ANNOTATION_PARAMETER_KIND);
			} else {
				handle.append(METHOD_KIND);
			}
		}
		handle.append(HANDLE_SEPARATOR);
		handle.append(getNonEmptyTypeString(getTypeString(methodBinding
				.getDeclaringClass())));
		handle.append(HANDLE_SEPARATOR);
		handle.append(getNonEmptyName(methodBinding.getName()));
		for (ITypeBinding param : methodBinding.getParameterTypes()) {
			handle.append(HANDLE_SEPARATOR);
			handle.append(getNonEmptyTypeString(getTypeString(param)));
		}
	}

	public static String getNonEmptyTypeString(String type) {
		String newType = type;
		if (newType == null || newType.trim().length() == 0) {
			newType = PPATypeRegistry.UNKNOWN_CLASS_FQN;
		}
		return newType;
	}

	public static String getNonEmptyName(String name) {
		String newName = name;
		if (newName == null || newName.trim().length() == 0) {
			newName = "unknown";
		}
		return newName;
	}

}
