package edu.vt.cs.editscript.common;

import java.io.BufferedReader;
import java.io.IOException;
import java.nio.charset.Charset;
import java.nio.file.DirectoryIteratorException;
import java.nio.file.DirectoryStream;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Scanner;

public class CodeLineCounter {
	
	private Path root;
	
	private List<Path> javaFiles = new ArrayList<>();
	
	private int line = 0;
	
	public CodeLineCounter(String folder) {
		root = FileSystems.getDefault().getPath(folder);
	}

	private void listJavaFiles(Path p) {
		try (DirectoryStream<Path> stream = Files.newDirectoryStream(p)) {
		    for (Path file: stream) {
		    	if (Files.isDirectory(file)) {
		    		listJavaFiles(file);
		    	} else if (file.getFileName().toString().endsWith(".java")) {
		    		javaFiles.add(file);
//		    		System.out.println("Add File: " + file.toString());
		    	}
		    }
		} catch (IOException | DirectoryIteratorException x) {
		    // IOException can never be thrown by the iteration.
		    // In this snippet, it can only be thrown by newDirectoryStream.
		    System.err.println(x);
		}
	}
	
	public int getCodeLine() {
		listJavaFiles(root);
		
		for (Path javaFile: javaFiles) {
//			System.out.println("Processing File: " + javaFile.toString());
			Charset charset = Charset.forName("UTF-8");
			int currentLine = 0;
			try (BufferedReader reader = Files.newBufferedReader(javaFile, charset)) {
			    while (reader.readLine() != null) {
			    	currentLine++;
			    }
			} catch (IOException x) {
			    System.err.format("IOException: %s%n", x);
			}
//			System.out.println(currentLine);
			line += currentLine;
//			System.out.println(line);
			
		}
		
		return line;
	}
	
	
	
	public static void main(String[] args) {
		String root = "/Users/Vito/Documents/VT/2017spring/SE/LOC/";
		String[] projects = {"aries", "cassandra", "derby", "mahout"};
		for (String project: projects) {
			String folder = root + project;
			System.out.println(project);
			CodeLineCounter counter = new CodeLineCounter(folder);
			int codeLine = counter.getCodeLine();
			System.out.println(codeLine);
		}
	}
}
