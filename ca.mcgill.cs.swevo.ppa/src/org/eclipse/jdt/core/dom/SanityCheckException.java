package org.eclipse.jdt.core.dom;

//added by nameng, to indicate failure of sanity check
public class SanityCheckException extends Exception{

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	public SanityCheckException(String msg) {
		super(msg);
	}
}
