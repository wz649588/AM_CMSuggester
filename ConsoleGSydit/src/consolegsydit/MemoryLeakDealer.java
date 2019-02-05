package consolegsydit;

import java.io.IOException;

public class MemoryLeakDealer {

	public static void main(String[] args) throws IOException {
		
//		String eclipseExec = "/Users/Vito/eclipse/eclipse-rcp-luna-R-macosx-cocoa-x86_64/Eclipse.app/Contents/MacOS/eclipse";
//		String eclipseExec = "/Users/Vito/eclipse/eclipse-rcp-luna-R-macosx-cocoa-x86_64/Eclipse.app";
		String eclipseExec = "/Users/Vito/eclipse/eclipse-rcp-luna-R-macosx-cocoa-x86_64/eclipse";


		
		String workspacePath = "/Users/Vito/Documents/workspaces/neo";
		
//		String command = eclipseExec + " -data " + workspacePath;
//				+ " -application consolesydit.Application";
		String command = eclipseExec + " -nosplash -application gsydit -data /Users/Vito/Documents/workspaces/neo/../runtime-consolesydit.Application -dev file:/Users/Vito/Documents/workspaces/neo/.metadata/.plugins/org.eclipse.pde.core/consolesydit.Application/dev.properties -os macosx -ws cocoa -arch x86_64 -consoleLog";
		
		Process p = Runtime.getRuntime().exec(command);

	}

}
