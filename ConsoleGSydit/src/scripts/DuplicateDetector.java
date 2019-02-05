package scripts;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.FilenameFilter;
import java.io.IOException;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import edu.vt.cs.analysis.FileUtils;
import edu.vt.cs.changes.ChangeDistillerClient;
import edu.vt.cs.changes.ChangeFact;
import edu.vt.cs.changes.CommitComparatorClient;

public class DuplicateDetector {

	public static void main(String[] args) {
		File bugFile = new File("/Users/nm8247/Software/workspaceForGrapa/grapa/bugNames_copy.txt");
		BufferedReader reader = null;
		try {
			reader = new BufferedReader(new FileReader(bugFile));
			String line = null;
			Map<String, Map<Integer, String>> map = new HashMap<String, Map<Integer, String>>();
			while ( (line = reader.readLine()) != null) {				
				String folderName = line.trim();
				if (!folderName.contains("-")) {
					continue;
				}
				String bugId = folderName.substring(folderName.indexOf('-') + 1); 
				Map<Integer, String> bugMap = map.get(bugId);
				if (bugMap == null) {
					bugMap = new HashMap<Integer, String>();
					map.put(bugId, bugMap);
				}
				File d = new File("/Users/nm8247/Documents/experiment_data/zhonghao/derby/derby/" + folderName);
				File fd = new File(d.getAbsolutePath() + "/from");
				File[] files = fd.listFiles(new FilenameFilter() {
					public boolean accept(File dir, String name) {
						if (name.endsWith(".java")) {
							return true;
						} else {
							return false;
						}
					}
				});				
				int hashcode = 0;
				for (int i = 0; i < files.length; i++) {					
					hashcode = hashcode * 3 + FileUtils.getContent(files[i]).hashCode();
				}
				hashcode = hashcode * 31;
				File td = new File(d.getAbsolutePath() + "/to");
				files = td.listFiles(new FilenameFilter() {
					public boolean accept(File dir, String name) {
						if (name.endsWith(".java")) {
							return true;
						} else {
							return false;
						}
					}
				});
				for (int i = 0; i < files.length; i++) {
					hashcode = hashcode * 3 + FileUtils.getContent(files[i]).hashCode();
				}
				String uniqueFilename = bugMap.get(hashcode);
				if (uniqueFilename == null) {
					uniqueFilename = folderName;
					bugMap.put(hashcode, uniqueFilename);
				}
			}
			reader.close();
			BufferedWriter out = new BufferedWriter(new FileWriter("/Users/nm8247/Software/workspaceForGrapa/grapa/bugNames2.txt"));
			for (Map<Integer, String> mentry : map.values()) {
				for (Entry<Integer, String> entry : mentry.entrySet()) {
					out.write(entry.getValue() + "\n");
				}
			}
			out.close();
		} catch (FileNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		
	}
}
