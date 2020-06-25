package org.eclipse.jdt.core.dom;

public class JdtTool {

	public static boolean isSubTypeCompatible(ITypeBinding paraType,
			ITypeBinding argType) {
		// TODO Auto-generated method stub
		 if(paraType.isArray()){
		      return argType.isSubTypeCompatible(paraType.getElementType());
		 }else{
		     return argType.isSubTypeCompatible(paraType);
		 }
	}

}
