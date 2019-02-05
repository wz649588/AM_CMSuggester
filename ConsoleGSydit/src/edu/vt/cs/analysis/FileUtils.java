package edu.vt.cs.analysis;

import java.io.File;
import java.io.FileReader;
import java.io.IOException;

public class FileUtils {
	 public static String getContent(File file) {
	        char[] b = new char[1024];
	        StringBuilder sb = new StringBuilder();
	        try {
	            FileReader reader = new FileReader(file);
	            int n = reader.read(b);
	            while (n > 0) {
	                sb.append(b, 0, n);
	                n = reader.read(b);
	            }
	            reader.close();
	        } catch (IOException e) {
	            throw new RuntimeException(e);
	        }
	        return sb.toString();
	    }
}
