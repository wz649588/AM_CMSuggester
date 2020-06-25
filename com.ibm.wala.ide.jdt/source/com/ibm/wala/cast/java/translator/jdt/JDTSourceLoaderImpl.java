/*
 * This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html.
 * 
 * This file is a derivative of code released by the University of
 * California under the terms listed below.  
 *
 * WALA JDT Frontend is Copyright (c) 2008 The Regents of the
 * University of California (Regents). Provided that this notice and
 * the following two paragraphs are included in any distribution of
 * Refinement Analysis Tools or its derivative work, Regents agrees
 * not to assert any of Regents' copyright rights in Refinement
 * Analysis Tools against recipient for recipient's reproduction,
 * preparation of derivative works, public display, public
 * performance, distribution or sublicensing of Refinement Analysis
 * Tools and derivative works, in source code and object code form.
 * This agreement not to assert does not confer, by implication,
 * estoppel, or otherwise any license or rights in any intellectual
 * property of Regents, including, but not limited to, any patents
 * of Regents or Regents' employees.
 * 
 * IN NO EVENT SHALL REGENTS BE LIABLE TO ANY PARTY FOR DIRECT,
 * INDIRECT, SPECIAL, INCIDENTAL, OR CONSEQUENTIAL DAMAGES,
 * INCLUDING LOST PROFITS, ARISING OUT OF THE USE OF THIS SOFTWARE
 * AND ITS DOCUMENTATION, EVEN IF REGENTS HAS BEEN ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *   
 * REGENTS SPECIFICALLY DISCLAIMS ANY WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
 * FOR A PARTICULAR PURPOSE AND FURTHER DISCLAIMS ANY STATUTORY
 * WARRANTY OF NON-INFRINGEMENT. THE SOFTWARE AND ACCOMPANYING
 * DOCUMENTATION, IF ANY, PROVIDED HEREUNDER IS PROVIDED "AS
 * IS". REGENTS HAS NO OBLIGATION TO PROVIDE MAINTENANCE, SUPPORT,
 * UPDATES, ENHANCEMENTS, OR MODIFICATIONS.
 */
package com.ibm.wala.cast.java.translator.jdt;

import java.io.IOException;
import java.util.List;

import com.ibm.wala.cast.java.loader.JavaSourceLoaderImpl;
import com.ibm.wala.cast.java.translator.SourceModuleTranslator;
import com.ibm.wala.classLoader.IClass;
import com.ibm.wala.classLoader.IClassLoader;
import com.ibm.wala.classLoader.Module;
import com.ibm.wala.ipa.cha.IClassHierarchy;
import com.ibm.wala.types.ClassLoaderReference;
import com.ibm.wala.types.TypeName;
import com.ibm.wala.util.config.SetOfClasses;

public class JDTSourceLoaderImpl extends JavaSourceLoaderImpl {
  private final boolean dump;
  
  //added by nameng in order to create a translator for all source code
  private JDTSourceModuleTranslator translator = null;
  @Override 
  public void init(List<Module> modules) throws IOException {
    translator = new JDTSourceModuleTranslator(cha.getScope(), this, dump);
    translator.init();
    super.init(modules);
  }
  
  public JDTSourceLoaderImpl(ClassLoaderReference loaderRef, IClassLoader parent, SetOfClasses exclusions, IClassHierarchy cha) throws IOException {
    this(loaderRef, parent, exclusions, cha, false);
  }
  
  public JDTSourceLoaderImpl(ClassLoaderReference loaderRef, IClassLoader parent, SetOfClasses exclusions, IClassHierarchy cha, boolean dump) throws IOException {
    super(loaderRef, parent, exclusions, cha);
    this.dump = dump;
  }

  @Override
  protected SourceModuleTranslator getTranslator() {//modified by nameng: since this method can be invoked multiple times
    // each time a source file is loaded, it is invoked once
//    return new JDTSourceModuleTranslator(cha.getScope(), this, dump);
    return translator;
  }

  public IClass lookupOwenClass(TypeName className) {
    // TODO Auto-generated method stub
    if (className == null) {
      throw new IllegalArgumentException("className is null");
    }
    if (DEBUG_LEVEL > 1) {
      System.err.println(this + ": lookupClass " + className);
    }

    // treat arrays specially:
    if (className.isArrayType()) {
      return arrayClassLoader.lookupClass(className, this, cha);
    }
    // Try our own namespace.
    IClass result = loadedClasses.get(className);
//    for(TypeName t:loadedClasses.keySet()){
//        String tt = t.toString();
//        if(tt.indexOf("MasterReceiverThread")>0){
//          System.out.println(t);
//        }
//    }
    // try delegating first.
    if(result==null){
      IClassLoader parent = getParent();
      if (parent != null) {
        result = parent.lookupClass(className);
        if (result != null) {
          return result;
        }
      }
    }
    return result;
  }
}
