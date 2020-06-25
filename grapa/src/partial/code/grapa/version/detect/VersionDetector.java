package partial.code.grapa.version.detect;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Hashtable;

import org.eclipse.jdt.core.dom.AST;
import org.eclipse.jdt.core.dom.ASTParser;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.Name;
import org.eclipse.jdt.core.dom.PackageDeclaration;

import partial.code.grapa.tool.FileUtils;
import ca.mcgill.cs.swevo.ppa.PPAOptions;
import ca.mcgill.cs.swevo.ppa.ui.PPAUtil;

public class VersionDetector {

	private String pName;
	private Hashtable<String, ArrayList<String>> typeTable = new Hashtable<String, ArrayList<String>>();
	private Hashtable<String, ArrayList<String>> methodTable = new Hashtable<String, ArrayList<String>>();
	private Hashtable<String, ArrayList<String>> fieldTable = new Hashtable<String, ArrayList<String>>();
	private Hashtable<String, Integer> versionTable = new Hashtable<String, Integer>();
	
	public void setProject(String pName) {
		// TODO Auto-generated method stub
		this.pName = pName;		
	}

	public void readElementList(String elementListDir) {
		// TODO Auto-generated method stub
		String filename = elementListDir+pName+"_type.txt";
		File file = new File(filename);
        BufferedReader reader = null;
        try {
            reader = new BufferedReader(new FileReader(file));
            String line = null;
            while ((line = reader.readLine()) != null) {            	
                int mark = line.indexOf("\t");
                String key = line.substring(0, mark);
                line = line.substring(mark+1);
                mark = line.indexOf("\t");
                String value = line.substring(0, mark);
                line = line.substring(mark+1);
                ArrayList<String> versions = new ArrayList<String>();
            	mark = line.indexOf("\t");
            	while(mark>0){
            		value = line.substring(0,mark);
            		line = line.substring(mark+1);
            		versions.add(value);
            		mark = line.indexOf("\t");
            	}
            	this.typeTable.put(key, versions);
            }
            reader.close();
        } catch (IOException e) {
            e.printStackTrace();
            exdist.ExceptionHandler.process(e);
        } finally {
            if (reader != null) {
                try {
                    reader.close();
                } catch (IOException e1) {
                }
            }
        }
        
        filename = elementListDir+pName+"_method.txt";
		file = new File(filename);
        reader = null;
        try {
            reader = new BufferedReader(new FileReader(file));
            String line = null;
            while ((line = reader.readLine()) != null) {
                int mark = line.indexOf("\t");
                String key = line.substring(0, mark);
                line = line.substring(mark+1);
                mark = line.indexOf("\t");
                String value = line.substring(0, mark);
                line = line.substring(mark+1);
                int v = Integer.parseInt(value);
            	ArrayList<String> versions = new ArrayList<String>();
            	mark = line.indexOf("\t");
            	while(mark>0){
            		value = line.substring(0,mark);
            		line = line.substring(mark+1);
            		versions.add(value);
            		mark = line.indexOf("\t");
            	}
            	this.methodTable.put(key, versions);
            }
            reader.close();
        } catch (IOException e) {
            e.printStackTrace();
            exdist.ExceptionHandler.process(e);
        } finally {
            if (reader != null) {
                try {
                    reader.close();
                } catch (IOException e1) {
                }
            }
        }
        
        filename = elementListDir+pName+"_field.txt";
		file = new File(filename);
        reader = null;
        try {
            reader = new BufferedReader(new FileReader(file));
            String line = null;
            while ((line = reader.readLine()) != null) {
                int mark = line.indexOf("\t");
                String key = line.substring(0, mark);
                line = line.substring(mark+1);
                mark = line.indexOf("\t");
                String value = line.substring(0, mark);
                line = line.substring(mark+1);
              ArrayList<String> versions = new ArrayList<String>();
            	mark = line.indexOf("\t");
            	while(mark>0){
            		value = line.substring(0,mark);
            		line = line.substring(mark+1);
            		versions.add(value);
            		mark = line.indexOf("\t");
            	}
            	this.fieldTable.put(key, versions);
            }
            reader.close();
        } catch (IOException e) {
            e.printStackTrace();
            exdist.ExceptionHandler.process(e);
        } finally {
            if (reader != null) {
                try {
                    reader.close();
                } catch (IOException e1) {
                }
            }
        }
        
        filename = elementListDir+pName+"_version.txt";
		file = new File(filename);
        reader = null;
        try {
            reader = new BufferedReader(new FileReader(file));
            String line = null;
            int count = 1;
            while ((line = reader.readLine()) != null) {
            	this.versionTable.put(line, count);
            	count++;
            }
            reader.close();
        } catch (IOException e) {
            e.printStackTrace();
            exdist.ExceptionHandler.process(e);
        } finally {
            if (reader != null) {
                try {
                    reader.close();
                } catch (IOException e1) {
                }
            }
        }
	}

	public VersionPair run(ArrayList<File> oldfiles, ArrayList<File> newfiles) {
		// TODO Auto-generated method stub
		VersionPair pair = new VersionPair();
		pair.left = detectVersions(oldfiles);
		pair.right = detectVersions(newfiles);
		return pair;
	}

	public Versions detectVersions(ArrayList<File> files) {
		ArrayList<String> typeElements = new ArrayList<String>();
		ArrayList<String> methodElements = new ArrayList<String>();
		ArrayList<String> fieldElements = new ArrayList<String>();
		
		ArrayList<String> shortTypes = new ArrayList<String>();
		ArrayList<String> shortMethods = new ArrayList<String>();
		ArrayList<String> shortFields = new ArrayList<String>();
		Versions vs = new Versions();
		
		for(File f:files){
//			PPAOptions option = new PPAOptions();
//			option.setAllowMemberInference(true);
//			option.setAllowCollectiveMode(true);
//			option.setAllowTypeInferenceMode(true);
//			option.setAllowMethodBindingMode(true);
			String sourcecode = FileUtils.getContent(f); //removed by nameng
//			CompilationUnit tree = PPAUtil.getCU(f, option);
			ASTParser parser = ASTParser.newParser(AST.JLS8);
			parser.setSource(sourcecode.toCharArray());
			CompilationUnit tree = (CompilationUnit) parser.createAST(null);
			
			CodeElementVisitor visitor = new CodeElementVisitor(pName);
			tree.accept(visitor);
			if(visitor.bUnit){
				vs.testFiles.add(f);
			}else{
				PackageDeclaration p = tree.getPackage();
				String paName = "";
				if(p!=null){
					paName = p.getName().getFullyQualifiedName();
				}
				vs.pTable.put(f, paName);
				addUniqueElements(typeElements, visitor.typeElements);
				addUniqueElements(methodElements, visitor.methodElements);
				addUniqueElements(fieldElements, visitor.fieldElements);
				
				addUniqueElements(shortTypes, visitor.shortTypes);
				addUniqueElements(shortMethods, visitor.shortMethods);
				addUniqueElements(shortFields, visitor.shortFields);
			}
//			PPAUtil.cleanUp(tree);
		}
//		PPAUtil.cleanUpAll(); //removed by nameng
		vs.versions = detectVersions(typeElements, 
		           methodElements, fieldElements, shortTypes, shortMethods, shortFields);
		return vs;
	}

	private void addUniqueElements(ArrayList<String> es1,
			ArrayList<String> es2) {
		// TODO Auto-generated method stub
		for(String ele:es2){
			if(!es1.contains(ele)){
				es1.add(ele);
			}
		}
	}

	private ArrayList<String> detectVersions(ArrayList<String> typeElements,
			ArrayList<String> methodElements, ArrayList<String> fieldElements, 
			ArrayList<String> shortTypes, ArrayList<String> shortMethods, ArrayList<String> shortFields) {
		// TODO Auto-generated method stub
		ArrayList<ArrayList<String>> vlist = new ArrayList<ArrayList<String>>();
		for(String type:typeElements){
			ArrayList<String> versions = typeTable.get(type);
			if(versions!=null&&versions.size()>0){
				ArrayList<String> vcp = new ArrayList<String>();
				vcp.addAll(versions);
				vlist.add(vcp);
			}
		}
		
		ArrayList<String> results = new ArrayList<String>();
		if(vlist.size()==0){
			return new ArrayList<String>();
		}else if(vlist.size()==1){
			results.addAll(vlist.get(0));
		}else{
			ArrayList<String> versions = vlist.get(0);
			for(int i=versions.size()-1; i>=0; i--){
				String v1 = versions.get(i);
				boolean bAllFound = true;
				for(ArrayList<String> vs:vlist){
					if(!vs.contains(v1)){
						bAllFound = false;
						break;
					}
				}
				if(!bAllFound){
					versions.remove(i);
				}
				if(versions.size()==1){
					break;
				}
			}
			results.addAll(versions);
		}
//		System.out.println();
		if(results.size()>1){
			for(String type:shortTypes){
				ArrayList<String> versions = new ArrayList<String>();
				for(String key:typeTable.keySet()){
					if(key.endsWith("."+type)){
						ArrayList<String> vs = typeTable.get(key);
						this.addUniqueElements(versions, vs);
					}
				}
				removeValidSubSet(results, versions);
			}
		}
		
		if(results.size()>1){
			for(String method:methodElements){
				ArrayList<String> versions = methodTable.get(method);
				removeValidSubSet(results, versions);
			}
		}
		
		if(results.size()>1){
			for(String field:fieldElements){
				ArrayList<String> versions = fieldTable.get(field);
				removeValidSubSet(results, versions);
			}
		}
		
		
		
		
		if(results.size()>1){
			for(String method:shortMethods){
				ArrayList<String> versions = new ArrayList<String>();
				for(String key:methodTable.keySet()){
					if(key.endsWith("."+method)){
						ArrayList<String> vs = methodTable.get(key);
						this.addUniqueElements(versions, vs);
					}
				}
				removeValidSubSet(results, versions);
			}
		}
		
		if(results.size()>1){
			for(String field:shortFields){
				ArrayList<String> versions = new ArrayList<String>();
				for(String key:fieldTable.keySet()){
					if(key.endsWith("."+field)){
						ArrayList<String> vs = fieldTable.get(key);
						this.addUniqueElements(versions, vs);
					}
				}
				removeValidSubSet(results, versions);
			}
		}
		return results;
	}

	private void removeValidSubSet(ArrayList<String> set,
			ArrayList<String> subset) {
		// TODO Auto-generated method stub
		if(subset==null){
			return;
		}
		boolean bValid = false;
		for(String item:subset){
			if(set.contains(item)){
				bValid = true;
				break;
			}
		}
		if(bValid){
			for(int i=set.size()-1; i>=0; i--){
				String version = set.get(i);
				if(!subset.contains(version)){						
					set.remove(i);
				}
			}
		}
	}

}
