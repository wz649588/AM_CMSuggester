package com.ibm.wala.cast.java.translator.jdt;

import org.eclipse.jdt.core.dom.ITypeBinding;

public class JdtTool {

  public static boolean isSubTypeCompatible(ITypeBinding argType, ITypeBinding paraType) {
    // TODO Auto-generated method stub
    if(paraType.isArray()){
      return argType.isSubTypeCompatible(paraType.getElementType());
    }else{
      return argType.isSubTypeCompatible(paraType);
    }
  }

}
