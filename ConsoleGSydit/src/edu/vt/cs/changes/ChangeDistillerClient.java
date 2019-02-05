package edu.vt.cs.changes;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import ch.uzh.ifi.seal.changedistiller.ChangeDistiller;
import ch.uzh.ifi.seal.changedistiller.distilling.FileDistiller;
import ch.uzh.ifi.seal.changedistiller.model.entities.SourceCodeEntity;
import ch.uzh.ifi.seal.changedistiller.model.entities.StructureEntityVersion;
import ch.uzh.ifi.seal.changedistiller.treedifferencing.TreeEditOperation;
import edu.vt.cs.editscript.EditScriptRecorder;
import edu.vt.cs.editscript.TreeMatchRecorder;

public class ChangeDistillerClient {
	
	public static final String VERSION = "default";

	public List<ChangeFact> parseChanges(String filePath) throws IOException {
		
		// Added by Ye Wang, 03/23/2017
		EditScriptRecorder.init();
		
		// Ye Wang, 06/05/2017
		TreeMatchRecorder.init();
		
		File d = new File(filePath);
		File fd = new File(d.getAbsolutePath()+"/from");
		Map<String, File> oldfiles = new HashMap<String, File>();
		String fileName = null;
		for(File f:fd.listFiles()){
			fileName = f.getName();
			if(fileName.endsWith(".java")&&fileName.indexOf("Test")<0){
				oldfiles.put(fileName, f);
			}
		}
		fd = new File(d.getAbsolutePath()+"/to");
		Map<String, File> newfiles = new HashMap<String, File>();
		for(File f:fd.listFiles()){
			fileName = f.getName();
			if(fileName.endsWith(".java")&&fileName.indexOf("Test")<0){
				newfiles.put(fileName, f);
			}
		}
		FileDistiller distiller = ChangeDistiller.createFileDistiller();
		FileDistiller.setIgnoreComments();
		Set<String> visited = new HashSet<String>();
		File oFile = null, nFile = null;
		ChangeFact cf = null;
		List<ChangeFact> cfList = new ArrayList<ChangeFact>();
		for (Entry<String, File> entry: oldfiles.entrySet()) {
			fileName = entry.getKey();
			visited.add(fileName);
			oFile = entry.getValue();
			nFile = newfiles.get(fileName);			
			distiller.extractClassifiedSourceCodeChanges(oFile, nFile);
			
			cf = new ChangeFact(oFile, nFile, distiller.getSourceCodeChanges());
			cfList.add(cf);
		}
		oFile = null;
		for (Entry<String, File> entry : newfiles.entrySet()) {
			fileName = entry.getKey();
			if(!visited.add(fileName)) {
				continue;
			}// all newly added files			
			nFile = entry.getValue();
			distiller.extractClassifiedSourceCodeChanges(oFile, nFile);
			cf = new ChangeFact(oFile, nFile, distiller.getSourceCodeChanges());
			cfList.add(cf);
		}
		
		return cfList;
	}
}
