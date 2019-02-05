package edu.vt.cs.prediction;

public enum ChunkAtom {
	/**
	 * one or more digits, like "1", "12"
	 */
	NUMBER,
	
	/**
	 * all uppercase letters
	 */
	UPPER,
	
	/**
	 * all lowercase letters
	 */
	LOWER,
	
	/**
	 * "Name", at least 2 letters
	 */
	CAPITAL,
	
	ANY,
	
	/**
	 * a definite string
	 */
	DEFINITE
}
