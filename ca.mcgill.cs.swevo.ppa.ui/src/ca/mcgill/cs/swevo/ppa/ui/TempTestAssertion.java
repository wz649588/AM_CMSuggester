package ca.mcgill.cs.swevo.ppa.ui;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.Map;

import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.dom.AST;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTParser;

import ca.mcgill.cs.swevo.ppa.PPAOptions;

/**
 * This class can be deleted at any time.
 * @author Ye Wang
 *
 */
public class TempTestAssertion {

	public static void main(String[] args) throws IOException {
		byte[] bytes = Files.readAllBytes(Paths.get("/Users/Vito/TestAssertion.java"));
		String string = new String(bytes);
		
		
		ASTParser parser = ASTParser.newParser(AST.JLS8);
		parser.setSource(string.toCharArray());
		parser.setKind(ASTParser.K_COMPILATION_UNIT);
		parser.setIgnoreMethodBodies(false);
		parser.setStatementsRecovery(true);
		Map options = JavaCore.getOptions();
		Map options2 = JavaCore.getOptions();
		
//		JavaCore.setComplianceOptions(JavaCore.VERSION_1_8, options);
		
		for (Object key: options.keySet()) {
			if (!options.get(key).equals(options2.get(key))) {
				System.out.println(key.toString() + ": " + options.get(key));
				System.out.println(key.toString() + ":" + options2.get(key));
			}
				
		}
		
		parser.setCompilerOptions(options);
		ASTNode result = parser.createAST(null);
		
//		PPAOptions option = new PPAOptions();
//	    option.setAllowMemberInference(true);
//	    option.setAllowCollectiveMode(true);
//	    option.setAllowTypeInferenceMode(true);
//	    option.setAllowMethodBindingMode(true);
//	    ASTNode result = PPAUtil.getCU(new File("/Users/Vito/TestAssertion.java"), option);
		System.out.println(result);
	}

}
