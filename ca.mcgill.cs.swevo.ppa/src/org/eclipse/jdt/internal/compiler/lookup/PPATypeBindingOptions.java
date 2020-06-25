package org.eclipse.jdt.internal.compiler.lookup;

import org.eclipse.jdt.core.dom.Name;

import ca.mcgill.cs.swevo.ppa.PPAASTUtil;

public class PPATypeBindingOptions {

	private boolean isAnnotation;

	public PPATypeBindingOptions() {
		
	}
	
	public PPATypeBindingOptions(boolean isAnnotation) {
		super();
		this.isAnnotation = isAnnotation;
	}

	public boolean isAnnotation() {
		return isAnnotation;
	}

	public void setAnnotation(boolean isAnnotation) {
		this.isAnnotation = isAnnotation;
	}
	
	public static PPATypeBindingOptions parseOptions(Name name) {
		return new PPATypeBindingOptions(PPAASTUtil.isAnnotation(name));
	}
	
	
	
}
