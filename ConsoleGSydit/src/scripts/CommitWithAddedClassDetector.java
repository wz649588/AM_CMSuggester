package scripts;

import java.io.IOException;
import java.nio.file.DirectoryIteratorException;
import java.nio.file.DirectoryStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;

/**
 * This is a one-time class, which can be deleted at any time.
 * It detects the commit with added class
 * @author Ye Wang
 * @since 02/25/2018
 *
 */
public class CommitWithAddedClassDetector {
	private static String parentFolder = "/Users/Vito/Documents/VT/2017spring/SE/ZhongData/cassandra/cassandra";

	public static void main(String[] args) {
		// list the parent folder
		Path parentPath = Paths.get(parentFolder);
		try (DirectoryStream<Path> stream = Files.newDirectoryStream(parentPath)) {
		    for (Path path: stream) {
		    	if (!Files.isDirectory(path))
		    		continue;
		    	Path fromPath = Paths.get(parentFolder, path.getFileName().toString(), "from");
		    	Path toPath = Paths.get(parentFolder, path.getFileName().toString(), "to");
		    	List<String> fromNames = new ArrayList<>();
		    	try (DirectoryStream<Path> fromStream = Files.newDirectoryStream(fromPath)) {
		    		for (Path p: fromStream) {
		    			fromNames.add(p.getFileName().toString());
		    		}
		    	} catch (IOException | DirectoryIteratorException x) {
		    		System.err.println(x);
		    	}
		    	List<String> toNames = new ArrayList<>();
		    	try (DirectoryStream<Path> toStream = Files.newDirectoryStream(toPath)) {
		    		for (Path p: toStream) {
		    			toNames.add(p.getFileName().toString());
		    		}
		    	} catch (IOException | DirectoryIteratorException x) {
		    		System.err.println(x);
		    	}
//		        System.out.println(path.getFileName());
		    	boolean hasAddedClass = false;
		    	String addedClassFileName = null;
		    	for (String toName: toNames) {
		    		if (!fromNames.contains(toName)) {
		    			hasAddedClass = true;
		    			addedClassFileName = toName;
		    			break;
		    		}
		    	}
		    	if (hasAddedClass) {
		    		System.out.println(path.getFileName());
		    		System.out.println(addedClassFileName);
//		    		break;
		    	}
		    	
		    }
		} catch (IOException | DirectoryIteratorException x) {
		    // IOException can never be thrown by the iteration.
		    // In this snippet, it can only be thrown by newDirectoryStream.
		    System.err.println(x);
		}

	}
}
