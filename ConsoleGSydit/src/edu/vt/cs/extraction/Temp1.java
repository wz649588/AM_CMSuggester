package edu.vt.cs.extraction;

import java.io.IOException;
import java.nio.file.DirectoryStream;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;

import org.jgrapht.Graph;

import edu.vt.cs.graph.ReferenceEdge;
import edu.vt.cs.graph.ReferenceNode;

/**
 * Finding patterns having AF 
 * @author Ye Wang
 * @since 01/09/2017
 */
public class Temp1 {

	public static void main(String[] args) throws IOException {
		String patternSet = "/Users/Vito/Documents/VT/2016fall/SE/pattern_set";
		Path path = FileSystems.getDefault().getPath(patternSet);
		DirectoryStream<Path> stream = Files.newDirectoryStream(path, "*.xml");
		for(Path filePath: stream) {
			Graph<ReferenceNode, ReferenceEdge> graph = PatternExtractor.readJgraphtFromXml(filePath);
			boolean hasFieldAccess = false;
			for (ReferenceEdge edge: graph.edgeSet()) {
				if (edge.type == ReferenceEdge.FIELD_ACCESS) {
					hasFieldAccess = true;
					break;
				}
			}
			if (hasFieldAccess) {
				String number = filePath.getFileName().toString().replaceFirst("[.][^.]+$", "");
				System.out.println(number);
			}
		}
	}
}
