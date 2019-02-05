package edu.vt.cs.diffparser.textdiff;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import edu.vt.cs.diffparser.util.Range;

public class DiffFileInterpreter {

	static boolean DEBUG = true;
	
	static Pattern digitPattern = Pattern.compile("\\d+"); 
	
	String diffFile;
	
	List<FileRecord> fileRecords;
	
	public DiffFileInterpreter(String diffFile) {
		this.diffFile = diffFile;
		fileRecords = new ArrayList<FileRecord>();
	}
	
	public List<FileRecord> getTextDiff() {
		// read file
		File f = new File(diffFile);
		List<String> lines = new ArrayList<String>();
		String line = null;
		String line2 = null;
		BufferedReader in = null;
		try {
			in = new BufferedReader(new FileReader(f));
			while ((line = in.readLine()) != null) {
				lines.add(line);
			}
		} catch (FileNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
			consolegsydit.ExceptionHandler.process(e);
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
			consolegsydit.ExceptionHandler.process(e);
		} finally {
			try {
				in.close();
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
				consolegsydit.ExceptionHandler.process(e);
			}
		}
		
		FileRecord r = null;
		// interpret changes at file level
		for (int i = 0; i < lines.size() - 1; i++) {
			line = lines.get(i);
			if (line.startsWith("---")) { // interpret changes at range levels
				line2 = lines.get(++i);
				line = line.substring("--- a".length());				
				line2 = line.substring("--- b".length());
				if (line2.contains("null")) {
					r = new DeletedFileRecord(line);					
				} else if (line.contains("null")) {
					r = new InsertedFileRecord(line2);					
				} else {
					r = new UpdatedFileRecord(line, line2);	
				}	
				fileRecords.add(r);					
			} 
		}			
		refineRecords();
		// print changes
		if (DEBUG) {
			System.out.println("File records: ");
			for ( FileRecord fr : fileRecords) {
				System.out.println(fr);
			}
		}
		return fileRecords;
	}
	
	private void refineRecords() {
		List<FileRecord> newRecords = new ArrayList<FileRecord>();
		for (FileRecord fr : fileRecords) {
			if (isIncluded(fr.fileName)) {
				newRecords.add(fr);
			}
		}
		fileRecords = newRecords;
	}
	
	private boolean isIncluded(String name) {
		return name.endsWith(".java");
	}
}
