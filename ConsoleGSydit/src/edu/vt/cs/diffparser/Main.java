package edu.vt.cs.diffparser;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;

public class Main {

	public static void main(String[] args) {
		String diffFile = "/Users/nm8247/Software/nuxeo/41bf3f_9cbf49.txt";
		String dir1 = "/Users/nm8247/Software/nuxeo/nuxeo41bf3f/nuxeo";
		String dir2 = "/Users/nm8247/Software/nuxeo/nuxeo9cbf49/nuxeo";
		
//		ChangeParser parser = new ChangeParser(diffFile, dir1, dir2);
//		parser.parseChanges();
		
		try {
			Process p = Runtime.getRuntime().exec("java -jar plugins/org.eclipse.equinox.launcher_1.3.100.v20150511-1540.jar"
					+ " -consoleLog -console -nosplash -application consoleDataflowAPIMining.Application"
					+ " " + dir1 + " " + dir2);
			String line = null;
			BufferedReader in = new BufferedReader(
			         new InputStreamReader(p.getInputStream()) );
			     while ((line = in.readLine()) != null) {
			         System.out.println(line);
			     }
			     in.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
			consolegsydit.ExceptionHandler.process(e);
		}
	}
	
}
