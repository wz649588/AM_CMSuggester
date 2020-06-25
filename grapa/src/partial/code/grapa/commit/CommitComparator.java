package partial.code.grapa.commit;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Hashtable;
import java.util.List;
import java.util.Map;

import org.eclipse.core.resources.IFile;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.CompilationUnit;

import partial.code.grapa.commit.DependenceGraph;
import partial.code.grapa.delta.graph.AbstractEdit;
import partial.code.grapa.delta.graph.ChangeGraphBuilder;
import partial.code.grapa.delta.graph.DeleteNode;
import partial.code.grapa.delta.graph.GraphEditScript;
import partial.code.grapa.delta.graph.InsertNode;
import partial.code.grapa.delta.graph.UpdateNode;
import partial.code.grapa.delta.graph.data.AbstractNode;
import partial.code.grapa.delta.graph.data.Edge;
import partial.code.grapa.dependency.graph.DataFlowAnalysisEngine;
import partial.code.grapa.dependency.graph.StatementEdge;
import partial.code.grapa.dependency.graph.StatementNode;
import partial.code.grapa.mapping.AstTreeComparator;
import partial.code.grapa.mapping.ClientMethod;
import partial.code.grapa.tool.GraphUtil;
import partial.code.grapa.version.detect.VersionDetector;
import partial.code.grapa.version.detect.VersionPair;
import ca.mcgill.cs.swevo.ppa.ui.PPAUtil;

import com.ibm.wala.cast.java.translator.jdt.JDTSourceModuleTranslator;
import com.ibm.wala.examples.drivers.PDFTypeHierarchy;
import com.ibm.wala.ipa.slicer.SDG;
import com.ibm.wala.ipa.slicer.Statement;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.util.collections.Pair;
import com.thoughtworks.xstream.XStream;
import com.thoughtworks.xstream.io.xml.StaxDriver;

import edu.uci.ics.jung.graph.DirectedSparseGraph;
import edu.vt.cs.graph.GraphDotUtil;
import edu.vt.cs.graph.GraphUtil2;
import edu.vt.cs.graph.SourceMapper;

public class CommitComparator {

	private String pName;
	private String elementListDir;
	private String commitDir;
	private String libDir;
	private String j2seDir;
	//modified by Na Meng to public
	public VersionDetector detector;
	public static String resultDir;
	
	private DataFlowAnalysisEngine leftEngine;
	private DataFlowAnalysisEngine rightEngine;
	private String otherLibDir;
	private String exclusionsFile;
	//modified by Na meng to public
	public static String bugName;
	private Map<IFile, CompilationUnit> leftMap = null;
	private Map<IFile, CompilationUnit> rightMap = null;

	private boolean bVisited = false;		
	
	public void run() {
		// TODO Auto-generated method stub
		detector = new VersionDetector();
		detector.setProject(pName);
		detector.readElementList(elementListDir);
		File d = new File(commitDir); 
		for(File c:d.listFiles()){
			if(c.isDirectory()){
				bugName = c.getName();
				System.out.println(bugName);
				if(bVisited){
					analyzeCommit(c);
//					break;
				}
				if(bugName.compareTo("2f5f0c2_CASSANDRA-1804")==0){
					bVisited = true;
				}
			}
		}
		System.out.println("Done!");
	}

	
	// modified by nameng to public
	public void analyzeCommit(File d) {
		// TODO Auto-generated method stub
		File fd = new File(d.getAbsolutePath()+"/from");
		ArrayList<File> oldfiles = new ArrayList<File>();
		for(File f:fd.listFiles()){
			if(f.getName().endsWith(".java")&&f.getName().indexOf("Test")<0){
				oldfiles.add(f);
			}
		}
		fd = new File(d.getAbsolutePath()+"/to");
		ArrayList<File> newfiles = new ArrayList<File>();
		for(File f:fd.listFiles()){
			if(f.getName().endsWith(".java")&&f.getName().indexOf("Test")<0){
				newfiles.add(f);
			}
		}
		VersionPair pair = detector.run(oldfiles, newfiles);
		
		for(int i=oldfiles.size()-1; i>=0; i--){
			File file = oldfiles.get(i);
			if(pair.left.testFiles.contains(file)){
				oldfiles.remove(i);
			}
		}
		
		for(int i=newfiles.size()-1; i>=0; i--){
			File file = newfiles.get(i);
			if(pair.right.testFiles.contains(file)){
				newfiles.remove(i);
			}
		}
		
		
		if(pair.left.versions.size()!=0&&pair.right.versions.size()!=0){
			compareVersions(pair, oldfiles, newfiles);
		}
	}

	public void clear() {
		try {
			leftEngine.clearAnalysisScope();
			rightEngine.clearAnalysisScope();
		} catch (JavaModelException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
			exdist.ExceptionHandler.process(e);
		}		
	}
	
	private void writeToLog(String version, String name) {
		// TODO Auto-generated method stub
		File file = new File(this.resultDir+"/bugNames.txt");
		FileWriter fw = null;
		BufferedWriter writer = null;
		try{
	         fw = new FileWriter(file, true);
	         writer = new BufferedWriter(fw);
	         writer.write(version+"\t"+name);
	         writer.newLine();
	         writer.flush();
        } catch (FileNotFoundException e) {
            e.printStackTrace();
        }catch (IOException e) {
            e.printStackTrace();
        }finally{
            try {
                writer.close();
                fw.close();
            } catch (IOException e) {
                e.printStackTrace();
            }
        }
	}


	public void setDotExe(String dotExe) {
		GraphUtil.dotExe = dotExe;
	}
	//modified by nameng to public
	public void compareVersions(VersionPair pair, ArrayList<File> oldfiles,
			ArrayList<File> newfiles) {
		// TODO Auto-generated method stub\
		
		boolean bLeftSuccess = false;
		ArrayList<ASTNode> leftTrees = null; 
		for(String oldVersion:pair.left.versions){
			System.out.print(oldVersion+",");
			try{
				leftEngine = new DataFlowAnalysisEngine();
				leftEngine.setExclusionsFile(this.exclusionsFile);
				leftTrees = leftEngine.addtoScope("left", pair.left.pTable, j2seDir, libDir, otherLibDir, oldVersion, oldfiles);				
				leftEngine.initClassHierarchy();
				
				bLeftSuccess = true;
			}catch(Exception e){
				e.printStackTrace();
				bLeftSuccess = false;
				exdist.ExceptionHandler.process(e);
			}
			if(bLeftSuccess){
				break;
			}
		}
		
		if(!bLeftSuccess){
			System.out.println("Fail to parse the left side project");
		}
		
		boolean bRightSuccess = false;
		System.out.print("->");
		
		ArrayList<ASTNode> rightTrees = null;
		for(String newVersion:pair.right.versions){
			System.out.print(newVersion+",");
			try{
				rightEngine = new DataFlowAnalysisEngine();
				rightEngine.setExclusionsFile(this.exclusionsFile);	
				rightTrees = rightEngine.addtoScope("right", pair.right.pTable, j2seDir, libDir, otherLibDir,  newVersion, newfiles);
				rightEngine.initClassHierarchy();
				bRightSuccess = true;
			}catch(Exception e){
				e.printStackTrace();
				bRightSuccess = false;
				exdist.ExceptionHandler.process(e);
			}
			if(bRightSuccess){
				break;
			}
		}
		
		if(!bRightSuccess){
			System.out.println("Fail to parse the right side project");
		}
		try {
			Thread.sleep(200);
		} catch (InterruptedException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
			exdist.ExceptionHandler.process(e);
		}
		
		if(bLeftSuccess&&bRightSuccess){
//			File file = new File(resultDir+this.bugName+"/");
//			if(!file.exists()){
//				file.mkdir();
//			}
			// added by nameng
			String dirName = resultDir + bugName + "/";
			File dir = new File(dirName);
			if (!dir.exists()) {
				  dir.mkdirs();
			}
			AstTreeComparator comparator = new AstTreeComparator(leftTrees, rightTrees);
			List<Pair<ClientMethod, ClientMethod>> mps = comparator.extractMappings();
			try {
				List<Pair<DependenceGraph, DependenceGraph>> dgPairs = getDependenceGraphs(mps);
			} catch (InterruptedException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
				exdist.ExceptionHandler.process(e);
			}
		}else{
			System.out.println("Error:"+bugName);
		}
	}
	
	//added by nameng[
	public boolean initializeAnalysis(ArrayList<File> oldfiles, ArrayList<File> newfiles) {
		boolean bLeftSuccess = false;
		try {
			leftEngine = new DataFlowAnalysisEngine();
			leftEngine.setExclusionsFile(this.exclusionsFile);
			leftEngine.addtoScope("left", null, j2seDir, libDir, otherLibDir, null, oldfiles);
			leftEngine.initClassHierarchy();
			leftMap = new HashMap<IFile, CompilationUnit>(JDTSourceModuleTranslator.fileToCu);
			// if (!leftMap.isEmpty()) {
			if (!leftMap.isEmpty() || oldfiles.isEmpty()) { // Ye Wang
				bLeftSuccess = true;
			}			
		} catch (Exception e) {
			bLeftSuccess = false;
			e.printStackTrace(); // added by Ye Wang
			exdist.ExceptionHandler.process(e, "Fail to parse the left side project");
		}
		if (!bLeftSuccess) {
			System.out.println("Fail to parse the left side project");
//			return bLeftSuccess;  // commented by Ye Wang
		}
		
		boolean bRightSuccess = false;
		try{
			rightEngine = new DataFlowAnalysisEngine();
			rightEngine.setExclusionsFile(this.exclusionsFile);	
			rightEngine.addtoScope("right", null, j2seDir, libDir, otherLibDir, null, newfiles);
			rightEngine.initClassHierarchy();
			rightMap = new HashMap<IFile, CompilationUnit>(JDTSourceModuleTranslator.fileToCu);
			// if (!rightMap.isEmpty()) {
			if (!rightMap.isEmpty() || newfiles.isEmpty()) { // Ye Wang
				bRightSuccess = true;
			}
		}catch(Exception e){
			e.printStackTrace();
			bRightSuccess = false;
			exdist.ExceptionHandler.process(e, "Fail to parse the right side project");
		}
		if (!bRightSuccess) {
			System.out.println("Fail to parse the right side project");
//			return bRightSuccess; // commented by Ye Wang
		}
		
		// commented by Ye Wang
//		String dirName = resultDir + bugName + "/";
//		File dir = new File(dirName);
//		if (!dir.exists()) {
//			  dir.mkdirs();
//		}
//		return true;
		return bLeftSuccess && bRightSuccess; // added by Ye Wang
	}//]
	
	// added by nameng[
	public boolean initializeAnalysis(VersionPair pair, ArrayList<File> oldfiles, ArrayList<File> newfiles) {
		boolean bLeftSuccess = false;
		for(String oldVersion:pair.left.versions){
			System.out.print(oldVersion+",");
			try{
				leftEngine = new DataFlowAnalysisEngine();
				leftEngine.setExclusionsFile(this.exclusionsFile);
				leftEngine.addtoScope("left", pair.left.pTable, j2seDir, libDir, otherLibDir, oldVersion, oldfiles);
				leftEngine.initClassHierarchy();
				leftMap = new HashMap<IFile, CompilationUnit>(JDTSourceModuleTranslator.fileToCu);
				bLeftSuccess = true;
			}catch(Exception e){
				e.printStackTrace();
				bLeftSuccess = false;
				exdist.ExceptionHandler.process(e);
			}
			if(bLeftSuccess){
				break;
			}
		}
		
		if(!bLeftSuccess){
			System.out.println("Fail to parse the left side project");
		}
		
		boolean bRightSuccess = false;
		System.out.print("->");
		
		for(String newVersion:pair.right.versions){
			System.out.print(newVersion+",");
			try{
				rightEngine = new DataFlowAnalysisEngine();
				rightEngine.setExclusionsFile(this.exclusionsFile);	
				rightEngine.addtoScope("right", pair.right.pTable, j2seDir, libDir, otherLibDir,  newVersion, newfiles);
				rightEngine.initClassHierarchy();
				rightMap = new HashMap<IFile, CompilationUnit>(JDTSourceModuleTranslator.fileToCu);
				bRightSuccess = true;
			}catch(Exception e){
				e.printStackTrace();
				bRightSuccess = false;
				exdist.ExceptionHandler.process(e);
			}
			if(bRightSuccess){
				break;
			}
		}
		
		if(!bRightSuccess){
			System.out.println("Fail to parse the right side project");
		}
		boolean success = bLeftSuccess & bRightSuccess;
//		if (success) { // commented by Ye Wang, because we don't use that folder to save output file. Instead we use SQLite
//			String dirName = resultDir + bugName + "/";
//			File dir = new File(dirName);
//			if (!dir.exists()) {
//				  dir.mkdirs();
//			}
//		}
		return success;
	}	
	
	public DataFlowAnalysisEngine getLeftAnalysisEngine() {
		return leftEngine;
	}
	
	public Map<IFile, CompilationUnit> getLeftTreeMap() {
		return leftMap;
	}

	public DataFlowAnalysisEngine getRightAnalysisEngine() {
		return rightEngine;
	}
	
	public Map<IFile, CompilationUnit> getRightTreeMap() {
		return rightMap;
	}
	//]end added by nameng
	// modified by nameng to become public
	public List<Pair<DependenceGraph, DependenceGraph>> getDependenceGraphs(List<Pair<ClientMethod, ClientMethod>> mps) throws InterruptedException {
		SourceMapper oldMapper = new SourceMapper();
		SourceMapper newMapper = new SourceMapper();
		List<Pair<DependenceGraph, DependenceGraph>> gPairs = new ArrayList<Pair<DependenceGraph, DependenceGraph>>();
		
		for (Pair<ClientMethod, ClientMethod> p : mps) {
			ClientMethod oldMethod = p.fst;
			ClientMethod newMethod = p.snd;
			oldMapper.add(oldMethod.ast);
			newMapper.add(newMethod.ast);
		}

		String dirName = resultDir + bugName + "/";
		for (Pair<ClientMethod, ClientMethod> p : mps) {
			ClientMethod oldMethod = p.fst;
			ClientMethod newMethod = p.snd;
			
			System.out.println(oldMethod.methodName);
			SDG lfg2 = leftEngine.buildSystemDependencyGraph2(oldMethod);
			IR lir = leftEngine.getCurrentIR();
			System.out.print("");
			DirectedSparseGraph<StatementNode, StatementEdge> leftGraph = 
					GraphUtil2.translateToJungGraph(lfg2, oldMethod, 
							oldMapper, StatementNode.LEFT);//modified by nameng			
			if (leftGraph == null)
				continue;
			
			DirectedSparseGraph<AbstractNode, Edge> gl = GraphUtil2.translateGraphToASTGraph(leftGraph, lir);
//			GraphUtil2.writeSDGraph(gl, dirName + "left_"+oldMethod.getTypeName()+"_"+oldMethod.methodName);			
			
			SDG rfg2 = rightEngine.buildSystemDependencyGraph2(newMethod);
			IR rir = rightEngine.getCurrentIR();
			DirectedSparseGraph<StatementNode, StatementEdge> rightGraph = 
					GraphUtil2.translateToJungGraph(rfg2, newMethod,
							newMapper, StatementNode.RIGHT);
			DirectedSparseGraph<AbstractNode, Edge> gr = GraphUtil2.translateGraphToASTGraph(rightGraph, rir);
//			GraphUtil2.writeSDGraph(gr, dirName + "right_"+newMethod.getTypeName()+"_"+oldMethod.methodName);
			
			Pair<DependenceGraph, DependenceGraph> pair = new Pair<DependenceGraph, DependenceGraph>(
					new DependenceGraph(lfg2, gl), 
					new DependenceGraph(rfg2, gr));
			gPairs.add(pair);
		}
		return gPairs;
	}
	
	private void compareGraph2(DirectedSparseGraph<StatementNode, StatementEdge> leftGraph,
			IR lir, DirectedSparseGraph<StatementNode, StatementEdge> rightGraph, IR rir) {		
		Collection<StatementNode> vertices = leftGraph.getVertices();
		for (StatementNode sn : vertices) {
			Statement st = sn.statement;
			Collection<StatementEdge> edges = leftGraph.getEdges();
			for (StatementEdge se : edges) {
				System.out.print(se.from);
				System.out.print("->");
				System.out.println(se.to);
			}
		}
	}	
	
	private void  writeDependencyGraph(
			DirectedSparseGraph<StatementNode, StatementEdge> graph, IR lir,
			IR rir, String filename) {
		// TODO Auto-generated method stub
		GraphUtil.writeDeltaGraphXMLFile(graph, rir, rir, filename);
		GraphUtil.writePdfDeltaGraph(graph, lir, rir, filename);
	}

	private ArrayList<DirectedSparseGraph<StatementNode, StatementEdge>> compareGraphs(
			DirectedSparseGraph<StatementNode, StatementEdge> leftGraph,
			IR lir, DirectedSparseGraph<StatementNode, StatementEdge> rightGraph, IR rir) {
		// TODO Auto-generated method stub
		GraphEditScript script = new GraphEditScript(leftGraph, lir, rightGraph, rir);

		ArrayList<AbstractEdit> edits = script.extractChanges();
		for(AbstractEdit edit:edits){
			if(edit instanceof UpdateNode||edit instanceof DeleteNode||edit instanceof InsertNode)
			System.out.println(edit);
		}
		System.out.println("---------------------------------------------");
		
		ChangeGraphBuilder builder = new ChangeGraphBuilder(leftGraph, lir, rightGraph, rir);
		ArrayList<DirectedSparseGraph<StatementNode, StatementEdge>> graphs = builder.extractChangeGraph();
		return graphs;
	}


	public void setProject(String name) {
		// TODO Auto-generated method stub
		pName = name;	
	}

	public void setElementListDir(String eld) {
		// TODO Auto-generated method stub
		elementListDir = eld+pName+"/";
	}

	public void setCommitDir(String cd) {
		// TODO Auto-generated method stub
		commitDir = cd+pName+"/";
	}

	public void setLibDir(String dir) {
		// TODO Auto-generated method stub
		libDir = dir+pName+"/";
	}

	public void setLibDirForMigration(String dir) {
		libDir = dir;
	}
	
	public void setJ2seDir(String dir) {
		// TODO Auto-generated method stub
		j2seDir = dir;
	}

	public void setResultDir(String dir) {
		// TODO Auto-generated method stub
		resultDir = dir+pName+"/";
	}

	public void setOtherLibDir(String dir) {
		// TODO Auto-generated method stub
		otherLibDir = dir+pName+"/";
	}

	public void setExclusionFile(String file) {
		// TODO Auto-generated method stub
		exclusionsFile = file;
	}

}
