package edu.vt.cs.graph;

public class TypeNameConverter {

	public static String binaryToQualified(String name) {
		name = name.substring(1);
		return name.replaceAll("/", ".");
	}
	
	public static String qualifiedToBinary(String name) {
		return "L" + name.replaceAll("\\.", "/");
	}
}
