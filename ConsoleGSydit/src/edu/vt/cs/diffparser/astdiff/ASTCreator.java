package edu.vt.cs.diffparser.astdiff;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;

import org.apache.commons.io.FileUtils;
import org.eclipse.jdt.core.dom.AST;
import org.eclipse.jdt.core.dom.ASTParser;
import org.eclipse.jdt.core.dom.CompilationUnit;

public class ASTCreator {

	public CompilationUnit createCU(String dir, String fileName) {
		File f = new File(dir + fileName);
		try {
			char[] source = FileUtils.readFileToString(f).toCharArray();
			ASTParser parser = ASTParser.newParser(AST.JLS8);
			parser.setSource(source);
			parser.setKind(ASTParser.K_COMPILATION_UNIT);
			parser.setResolveBindings(true);
			parser.setBindingsRecovery(true);
			parser.setStatementsRecovery(true);
			parser.setEnvironment(null, new String[]{dir}, null, true);
			CompilationUnit cu = (CompilationUnit)parser.createAST(null);
			return cu;
		} catch (FileNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
			consolegsydit.ExceptionHandler.process(e);
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
			consolegsydit.ExceptionHandler.process(e);
		} 
		return null;
	}

}

