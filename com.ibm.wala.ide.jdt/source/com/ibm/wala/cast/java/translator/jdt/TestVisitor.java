package com.ibm.wala.cast.java.translator.jdt;

import java.util.List;

import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.ClassInstanceCreation;
import org.eclipse.jdt.core.dom.IBinding;
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.MethodInvocation;
import org.eclipse.jdt.core.dom.QualifiedName;
import org.eclipse.jdt.core.dom.SimpleName;

public class TestVisitor extends ASTVisitor {

  @Override
  public boolean visit(ClassInstanceCreation node) {
    // TODO Auto-generated method stub
    String t = node.toString();
    if(t.indexOf("addIndexes")>=0){
      System.out.println(node);
    }
    return super.visit(node);
  }

  @Override
  public boolean visit(QualifiedName node) {
    // TODO Auto-generated method stub
    if(node.toString().indexOf("JDBC30Translation.SQL_TYPES_BOOLEAN")>=0){
      IBinding nodeB = node.resolveBinding();
      System.out.println(node);
    }
    return super.visit(node);
  }

  @Override
  public boolean visit(MethodDeclaration node) {
    // TODO Auto-generated method stub
    if(node.toString().indexOf("assertUnorderedResultSet")>=0){
      IMethodBinding nodeB = node.resolveBinding();
      ITypeBinding typeB = nodeB.getDeclaringClass();
      System.out.println(typeB.getQualifiedName());
    }
    return super.visit(node);
  }
  
  @Override
  public boolean visit(MethodInvocation node) {
    // TODO Auto-generated method stub
    String t = node.toString();
    if(t.indexOf("registerService")>=0){
      IMethodBinding nodeB = node.resolveMethodBinding();
      
      ITypeBinding[] args = nodeB.getParameterTypes();
      for(Object arg:args){
        System.out.println(arg);
      }
    }
    return super.visit(node);
  }
  
  public void test(String... t){
    
  }
  
  public void test1(){
     test("");
  }

}
