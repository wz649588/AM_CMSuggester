package edu.vt.cs.diffparser;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.List;

import org.eclipse.core.resources.IWorkspace;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.MethodDeclaration;

import partial.code.grapa.dependency.graph.DataFlowAnalysisEngine;
import edu.vt.cs.diffparser.astdiff.ASTCreator;
import edu.vt.cs.diffparser.astdiff.edits.HighlevelEditscript;
import edu.vt.cs.diffparser.astdiff.edits.LowlevelEditscript;
import edu.vt.cs.diffparser.astdiff.edits.UpdateOperation;
import edu.vt.cs.diffparser.differencer.FineTreeDifferencer;
import edu.vt.cs.diffparser.differencer.MatchSkeletonFinder;
import edu.vt.cs.diffparser.differencer.StructureDifferencer;
import edu.vt.cs.diffparser.textdiff.DiffFileInterpreter;
import edu.vt.cs.diffparser.textdiff.FileRecord;
import edu.vt.cs.diffparser.tree.JavaCUNode;
import edu.vt.cs.treebuilders.JavaStructureTreeBuilder;

public class ChangeParser {
	
	public static final boolean DEBUG = true; 

	private String diffFile;
	private String dir1;
	private String dir2;
	private IWorkspace workspace;
	
	private DataFlowAnalysisEngine leftEngine;
	private DataFlowAnalysisEngine rightEngine;
	
	public ChangeParser(String diffFile, String dir1, String dir2, 
			IWorkspace workspace) {
		this.diffFile = diffFile;
		this.dir1 = dir1;
		this.dir2 = dir2;
		this.workspace = workspace;
		leftEngine = new DataFlowAnalysisEngine();
		rightEngine = new DataFlowAnalysisEngine();
	}
	
	public void parseChanges() {
	   DiffFileInterpreter diffInterpreter = new DiffFileInterpreter(diffFile);
	   List<FileRecord> records = diffInterpreter.getTextDiff();
	   
	   for (FileRecord r : records) {
		   
	   }
	   
/*		
		ASTCreator creator = new ASTCreator();
		CompilationUnit oldAST = null;
		CompilationUnit newAST = null;
		JavaStructureTreeBuilder builder = new JavaStructureTreeBuilder();
		String fileName = null;
		StructureDifferencer differencer = new StructureDifferencer();
		JavaCUNode oldRoot = null;
		JavaCUNode newRoot = null;
		for (FileRecord r : records) {
			fileName = r.getName();
			oldAST = creator.createCU(dir1, fileName);
			newAST = creator.createCU(dir2, fileName);	
			builder.init(fileName);
			oldAST.accept(builder);
			oldRoot = (JavaCUNode)builder.getRoot();
			builder.init(fileName);
			newAST.accept(builder);
			newRoot = (JavaCUNode)builder.getRoot();
			differencer.calculateEditScript(oldRoot, newRoot);
			DataFlowAnalysisEngine engine = new DataFlowAnalysisEngine(workspace);
			ArrayList<File> fileList = new ArrayList<File>();
			fileList.add(new File(dir1 + fileName));
			ArrayList<ASTNode> trees = engine.addtoScope("source", new Hashtable<File, String>(), null, null, null, null, fileList);
			engine.initClassHierarchy();
			for (ASTNode tree : trees) {
				System.out.println(tree.toString());
			}
		*/	
			
			
			
			
			
			
//			HighlevelEditscript script = (HighlevelEditscript)differencer.getEditscript();
//			List<LowlevelEditscript> methodScripts = new ArrayList<LowlevelEditscript>();
//			LowlevelEditscript lowScript = null;
//			Iterator<UpdateOperation> updates = script.getMethodUpdates();//to continue here...
//			UpdateOperation<JavaMethodDeclarationNode> update = null;
//			ASTMethodFinder finder = new ASTMethodFinder();
//			MethodDeclaration mdLeft = null, mdRight = null;
//			
//			JavaMethodTreeBuilder builder2 = new JavaMethodTreeBuilder();
//			FineTreeDifferencer stmtDiff = new FineTreeDifferencer();
//			JavaImplementationNode mLeft = null, mRight = null;
//			while(updates.hasNext()) {
//				update = updates.next();
//				mdLeft = finder.lookForMethod(oldAST, update.getCurrent().getRange());
//				builder2.init(mdLeft);
//				mdLeft.accept(builder2);
//				mLeft = builder2.getRoot();
//				builder2.init(mdRight);
//				mdRight = finder.lookForMethod(newAST, update.getNewCurrent().getRange());
//				mdRight.accept(builder2);
//				mRight = builder2.getRoot();
//				stmtDiff.calculateEditScript(mLeft, mRight);
//				lowScript = (LowlevelEditscript) stmtDiff.getEditscript();
//				methodScripts.add(lowScript);
//				if (DEBUG) {
//					System.out.println(lowScript);
//				}
//			}
			
/*		}*/
		
	}
}
