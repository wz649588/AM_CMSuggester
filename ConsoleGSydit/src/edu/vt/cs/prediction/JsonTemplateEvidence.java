package edu.vt.cs.prediction;

import java.util.ArrayList;
import java.util.List;

public class JsonTemplateEvidence {
	/**
	 * Method signature
	 */
	public String name;
	
	public List<JsonTemplateContent> evidence;
	
	/**
	 * Names of local variables. Some names may appear more than once. 
	 */
	public List<String> localNameList;
	
	/**
	 * Names of fields used in the method. Some names may appear more than once.
	 */
	public List<String> fieldNameList;
	
	/**
	 * Names of methods invoked. Some names may appear more than once.
	 */
	public List<String> methodNameList;
	
	
	public JsonTemplateEvidence(String name) {
		this.name = name;
		evidence = new ArrayList<JsonTemplateContent>();
	}
	
	public void addTemplate(JsonTemplateContent t) {
		evidence.add(t);
	}
}
