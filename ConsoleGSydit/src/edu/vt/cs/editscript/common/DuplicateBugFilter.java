package edu.vt.cs.editscript.common;

import java.io.IOException;
import java.nio.file.DirectoryIteratorException;
import java.nio.file.DirectoryStream;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.vt.cs.sql.SqliteManager;

/**
 * This class tried to find a duplicate bug pair whose files are totally same, but it failed.
 * Therefore this is not a useful class.
 * @author Ye Wang
 * @since March 31, 2017
 */
public class DuplicateBugFilter {
	
	/**
	 * 427237_DERBY-1462 to 1462
	 * @param bugName 427237_DERBY-1462
	 * @return 1462
	 */
	public static String getBugId(String bugName) {
		int dashPos = bugName.indexOf('-');
		int begin = dashPos + 1;
		int end = begin;
		while(end < bugName.length() && Character.isDigit(bugName.charAt(end)))
			end++;
		return bugName.substring(begin, end);
	}
	
	public static void insertBugIdToDatabase() throws SQLException {
		Connection conn = SqliteManager.getConnection();
		Statement stmt = conn.createStatement();
		ResultSet rs = stmt.executeQuery("SELECT name FROM bug");
		List<String> names = new ArrayList<>();
		while (rs.next()) {
			String name = rs.getString(1);
			names.add(name);
		}
		rs.close();
		PreparedStatement pstmt = conn.prepareStatement("UPDATE bug SET bug_id=? WHERE name=?");
		for (String name: names) {
			String bugId = getBugId(name);
			pstmt.setString(1, bugId);
			pstmt.setString(2, name);
			pstmt.executeUpdate();
		}
		conn.close();
	}
	
	public static void main(String[] args) throws Exception {
		Connection conn = SqliteManager.getConnection();
		Statement stmt = conn.createStatement();
		stmt.executeUpdate("CREATE TABLE IF NOT EXISTS unique_bug (bug_name TEXT)");
		
		ResultSet rs = stmt.executeQuery("SELECT DISTINCT bug_id FROM bug");
		List<String> idList = new ArrayList<>();
		while (rs.next()) {
			String bugId = rs.getString(1);
			idList.add(bugId);
		}
		rs.close();
		for (String bugId: idList) {
			rs = stmt.executeQuery(String.format("SELECT name FROM bug WHERE bug_id=\"%s\"", bugId));
			rs.next();
			String uniqueName = rs.getString(1);
			PreparedStatement pstmt = conn.prepareStatement("INSERT INTO unique_bug (bug_name) VALUES (?)");
			pstmt.setString(1, uniqueName);
			pstmt.executeUpdate();
			pstmt.close();
		}
		stmt.close();
		conn.close();
	}
	
	public static void main1(String[] args) throws Exception {
		Connection conn = SqliteManager.getConnection();
		Statement stmt = conn.createStatement();
		stmt.executeUpdate("CREATE TABLE IF NOT EXISTS duplicate_bug (bug_id, name1, name2)");
		ResultSet rs = stmt.executeQuery("SELECT DISTINCT bug_id FROM bug");
		List<String> idList = new ArrayList<>();
		while (rs.next()) {
			String bugId = rs.getString(1);
			idList.add(bugId);
		}
		rs.close();
		System.out.println("Total ID: " + idList.size());
		
		int counter = 0;
		for (String bugId: idList) {
			System.out.println(++counter);
			rs = stmt.executeQuery(String.format("SELECT name FROM bug WHERE bug_id=\"%s\"", bugId));
			List<String> nameList = new ArrayList<>();
			while (rs.next()) {
				String bugName = rs.getString(1);
				nameList.add(bugName);
			}
			rs.close();
			if (nameList.size() < 2)
				continue;
			for (int i = 0; i < nameList.size(); i++) {
				for (int j = i + 1; j < nameList.size(); j++) {
					boolean twoBugsIdentical = isTwoBugSame(nameList.get(i), nameList.get(j));
					if (twoBugsIdentical) {
						PreparedStatement pstmt = conn.prepareStatement("INSERT INTO duplicate_bug (bug_id, name1, name2) VALUES (?,?,?)");
						pstmt.setString(1, bugId);
						pstmt.setString(2, nameList.get(i));
						pstmt.setString(3, nameList.get(j));
						pstmt.executeUpdate();
						pstmt.close();
					}
					
				}
			}
			
		}
		conn.close();
	}

	private static boolean isTwoBugSame(String bug1, String bug2) {
		// TODO
		String rootDir = "/Users/Vito/Documents/VT/2016fall/SE/20160828OriginalData/derby/derby";
		
		// get the "from" path of two bugs
		Path from1 = FileSystems.getDefault().getPath(rootDir, bug1, "from");
		Path from2 = FileSystems.getDefault().getPath(rootDir, bug2, "from");
		
		if (!twoFoldersSame(from1, from2))
			return false;
		
		Path to1 = FileSystems.getDefault().getPath(rootDir, bug1, "to");
		Path to2 = FileSystems.getDefault().getPath(rootDir, bug2, "to");
		
		if (!twoFoldersSame(to1, to2))
			return false;
		
		return true;
	}
	
	private static boolean twoFoldersSame(Path f1, Path f2) {
		try {
			Set<String> names1 = new HashSet<>();
			Map<String, Path> nameToPath1 = new HashMap<>();
			DirectoryStream<Path> stream1 = Files.newDirectoryStream(f1, "*.java");
		    for (Path file: stream1) {
		        names1.add(file.getFileName().toString());
		        nameToPath1.put(file.getFileName().toString(), file);
		    }
		    Set<String> names2 = new HashSet<>();
		    Map<String, Path> nameToPath2 = new HashMap<>();
			DirectoryStream<Path> stream2 = Files.newDirectoryStream(f2, "*.java");
		    for (Path file: stream2) {
		    	names2.add(file.getFileName().toString());
		    	nameToPath2.put(file.getFileName().toString(), file);
		    }
		    if (!names1.equals(names2))
		    	return false;
		    
		    for (String name: names1) {
		    	Path p1 = nameToPath1.get(name);
		    	Path p2 = nameToPath2.get(name);
		    	if (!twoFilesSame(p1, p2))
		    		return false;
		    }
		    
		} catch (IOException | DirectoryIteratorException x) {
		    // IOException can never be thrown by the iteration.
		    // In this snippet, it can only be thrown by newDirectoryStream.
		    System.err.println(x);
		}
		
		return true;
	}
	
	private static boolean twoFilesSame(Path p1, Path p2) {
		boolean result = false;
		try {
			byte[] content1 = Files.readAllBytes(p1);
			byte[] content2 = Files.readAllBytes(p2);
			result = Arrays.equals(content1, content2);
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return result;
	}

}
