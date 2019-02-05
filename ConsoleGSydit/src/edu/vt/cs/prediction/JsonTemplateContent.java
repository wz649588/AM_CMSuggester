package edu.vt.cs.prediction;

import java.util.List;

public class JsonTemplateContent {
	List<String> template;
	List<String> vars;
	String rating;
	
	public JsonTemplateContent(List<String> template, List<String> vars, String rating) {
		this.template = template;
		this.vars = vars;
		this.rating = rating;
	}
	
	public JsonTemplateContent(List<String> template, List<String> vars) {
		this.template = template;
		this.vars = vars;
		this.rating = null;
	}
}
