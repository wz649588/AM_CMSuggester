package edu.vt.cs.prediction.neo;

import java.io.IOException;
import java.nio.charset.Charset;
import java.nio.file.DirectoryIteratorException;
import java.nio.file.DirectoryStream;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.dom.AST;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTParser;
import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.FieldAccess;
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.IPackageBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.PackageDeclaration;
import org.eclipse.jdt.core.dom.QualifiedName;
import org.eclipse.jdt.core.dom.SimpleName;
import org.eclipse.jdt.core.dom.SuperFieldAccess;
import org.eclipse.jdt.core.dom.TypeDeclaration;

import edu.vt.cs.sql.SqliteManager;

/**
 * Find the changes that developers missed in earlier revisions
 * The process is as follows:
 * - List all java files in the newest Derby source code
 * - For every .java file, parse it and extract all classes
 *   in it (including nested classes)
 * - For every class, list all method
 * - For every method, generate its signature and check
 *   whether it exists in the fp_old_ver or fp_new_ver column
 *   of table false_positives
 * - If it exists in the table, check every field in this method
 * 
 * 
 * @author Ye Wang
 * @since 08/01/2017
 *
 */
public class DeveloperMissedChangeFinder {
	private String sourceCodeFolder;

	private String falsePositiveTable;
	
	private String resultTable;
	
	private List<Path> javaFiles = new ArrayList<>();
	
	private Path currentProcessingFile;
	
	private void listJavaFiles(Path p) {
		try (DirectoryStream<Path> stream = Files.newDirectoryStream(p)) {
		    for (Path file: stream) {
		    	if (Files.isDirectory(file)) {
		    		listJavaFiles(file);
		    	} else if (file.getFileName().toString().endsWith(".java")) {
		    		javaFiles.add(file);
		    		System.out.println("Add File: " + file.toString());
		    	}
		    }
		} catch (IOException | DirectoryIteratorException x) {
		    // IOException can never be thrown by the iteration.
		    // In this snippet, it can only be thrown by newDirectoryStream.
		    System.err.println(x);
		}
	}
	
	private void processCompilationUnit(ASTNode cu) {
		CompilationUnit unit = (CompilationUnit) cu;
		PackageDeclaration packageDeclaration = unit.getPackage();
		if (packageDeclaration == null)
			return;
		String packageName = packageDeclaration.getName().toString();
		
		TypeVisitor typeVisitor = new TypeVisitor();
		cu.accept(typeVisitor);
		List<ASTNode> types = typeVisitor.getTypes();
		for (ASTNode klass: types) {
			String className = ((TypeDeclaration) klass).getName().toString();
			MethodVisitor methodVisitor = new MethodVisitor();
			klass.accept(methodVisitor);
			List<ASTNode> methods = methodVisitor.getMethods();
			for (ASTNode method: methods) {
				String methodName = ((MethodDeclaration) method).getName().toString();
				Connection conn = SqliteManager.getConnection();
				try {
					PreparedStatement ps = conn.prepareStatement(
							"SELECT bug_name, fp_sig, fp_used_cm, af_class, af_name, af_sig FROM " + falsePositiveTable
							+ " WHERE fp_package=? AND fp_class=? AND fp_method=?");
					ps.setString(1, packageName);
					ps.setString(2, className);
					ps.setString(3, methodName);
					ResultSet rs = ps.executeQuery();
					List<Map<String, String>> queryResultList = new ArrayList<>();
					while (rs.next()) {
						String bugName = rs.getString("bug_name");
						String fpSig = rs.getString("fp_sig");
						String fpUsedCm = rs.getString("fp_used_cm");
						String afClass = rs.getString("af_class");
						String afName = rs.getString("af_name");
						String afSig = rs.getString("af_sig");
						
						Map<String, String> queryResult = new HashMap<>();
						queryResult.put("bug_name", bugName);
						queryResult.put("fp_sig", fpSig);
						queryResult.put("fp_used_cm", fpUsedCm);
						queryResult.put("af_class", afClass);
						queryResult.put("af_name", afName);
						queryResult.put("af_sig", afSig);
						queryResultList.add(queryResult);
					}
					rs.close();
					ps.close();
					
					for (Map<String, String> queryResult: queryResultList) {
						FieldVisitor fieldVisitor = new FieldVisitor();
						method.accept(fieldVisitor);
						List<String> fields = fieldVisitor.getFields();
						String afName = queryResult.get("af_name");
						if (fields.contains(afName)) {
							PreparedStatement ps2 = conn.prepareStatement("INSERT INTO " + resultTable
									+ " (bug_name, fp_package, fp_class, fp_method, fp_sig, fp_used_cm,"
									+ "af_class, af_name, af_sig, file_path) VALUES "
									+ "(?,?,?,?,?,?,?,?,?,?)");
							ps2.setString(1, queryResult.get("bug_name"));
							ps2.setString(2, packageName);
							ps2.setString(3, className);
							ps2.setString(4, methodName);
							ps2.setString(5, queryResult.get("fp_sig"));
							ps2.setString(6, queryResult.get("fp_used_cm"));
							ps2.setString(7, queryResult.get("af_class"));
							ps2.setString(8, queryResult.get("af_name"));
							ps2.setString(9, queryResult.get("af_sig"));
							ps2.setString(10, this.currentProcessingFile.toString());
							ps2.executeUpdate();
							ps2.close();
						}
					}
					
					
					
					conn.close();
				} catch (SQLException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			}
			
		}
		
		
	}
	
	public void execute() {
		createTable();
		
		Path rootFolder = FileSystems.getDefault().getPath(sourceCodeFolder);
		listJavaFiles(rootFolder);
		
		for (Path p: javaFiles) {
			this.currentProcessingFile = p;
			
			System.out.println("Process: " + p.toString());
			String source = null;
			try {
				byte[] allBytes = Files.readAllBytes(p);
				source = new String(allBytes, Charset.forName("US-ASCII"));
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			ASTParser parser = ASTParser.newParser(AST.JLS8);
			parser.setSource(source.toCharArray());
			parser.setKind(ASTParser.K_COMPILATION_UNIT);
			parser.setResolveBindings(true);
			parser.setBindingsRecovery(true);
			parser.setCompilerOptions(JavaCore.getOptions());
			ASTNode cu = parser.createAST(null);
			processCompilationUnit(cu);
		}
	}
	
	private void createTable() {
		Connection conn = SqliteManager.getConnection();
		try {
			java.sql.Statement stmt = conn.createStatement();
			stmt.executeUpdate("DROP TABLE IF EXISTS " + resultTable);
			stmt.executeUpdate("CREATE TABLE IF NOT EXISTS " + resultTable
					+ " (bug_name TEXT, fp_package TEXT, fp_class TEXT, fp_method TEXT,"
					+ "fp_sig TEXT, fp_used_cm TEXT,"
					+ "af_class TEXT, af_name TEXT, af_sig TEXT, file_path TEXT)");
			stmt.close();
			conn.close();
		} catch (SQLException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
	}
	
	public static void main(String[] args) {
		DeveloperMissedChangeFinder finder = new DeveloperMissedChangeFinder();
		String project = "mahout";
		if (project == "derby") {
			finder.sourceCodeFolder = "/Users/Vito/Documents/VT/2017spring/SE/db-derby-10.13.1.1-src/db-derby-10.13.1.1-src";
			finder.falsePositiveTable = "false_positives";
			finder.resultTable = "developer_missed_derby";
		} else if (project == "aries") {
			finder.sourceCodeFolder = "/Users/Vito/Documents/VT/2017spring/SE/aries";
			finder.falsePositiveTable = "false_positives_aries";
			finder.resultTable = "developer_missed_aries";
		} else if (project == "cassandra") {
			finder.sourceCodeFolder = "/Users/Vito/Documents/VT/2017spring/SE/cassandra/src/java";
			finder.falsePositiveTable = "false_positives_cassandra";
			finder.resultTable = "developer_missed_cassandra";
		} else if (project == "mahout") {
			finder.sourceCodeFolder = "/Users/Vito/Documents/VT/2017spring/SE/mahout";
			finder.falsePositiveTable = "false_positives_mahout";
			finder.resultTable = "developer_missed_mahout";
		}
		
		finder.execute();
	}
}

class MethodVisitor extends ASTVisitor {
	
	private List<ASTNode> methods = new ArrayList<>();
	
	@Override
	public boolean visit(MethodDeclaration node) {
		methods.add(node);
		return false;
	}
	
	List<ASTNode> getMethods() {
		return methods;
	}
}

class TypeVisitor extends ASTVisitor {
	private List<ASTNode> types = new ArrayList<>();
	
	@Override
	public boolean visit(TypeDeclaration node) {
		types.add(node);
		return false;
	}
	
	List<ASTNode> getTypes() {
		return types;
	}
}

class FieldVisitor extends ASTVisitor {
	
	private List<String> fields = new ArrayList<>();
	
	@Override
	public boolean visit(FieldAccess node) {
		String field = node.getName().toString();
		fields.add(field);
		return false;
	}
	
	@Override
	public boolean visit(SuperFieldAccess node) {
		String field = node.getName().toString();
		fields.add(field);
		return false;
	}
	
	@Override
	public boolean visit(QualifiedName node) {
		String field = node.getName().toString();
		fields.add(field);
		return false;
	}
	
	@Override
	public boolean visit(SimpleName node) {
		String field = node.getIdentifier().toString();
		fields.add(field);
		return false;
	}
	
	public List<String> getFields() {
		return fields;
	}
}
