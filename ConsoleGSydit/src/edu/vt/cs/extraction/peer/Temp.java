package edu.vt.cs.extraction.peer;

import java.io.IOException;
import java.nio.file.DirectoryStream;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Scanner;

public class Temp {

	public static void main(String[] args) throws IOException {
		// TODO Auto-generated method stub
		String dir = "/Users/Vito/Documents/VT/2016fall/SE/grapa_results22/derby";
		Path resultPath = FileSystems.getDefault().getPath(dir);
		DirectoryStream<Path> stream = Files.newDirectoryStream(resultPath);
		for (Path subDir: stream) {
			String bugName = subDir.getFileName().toString();
			if (!Files.isDirectory(subDir))
				continue;
			DirectoryStream<Path> stream2 = Files.newDirectoryStream(subDir, "*.txt");
			List<String> targetList = new ArrayList<String>();
			for (Path text: stream2) {
				String textName = text.getFileName().toString();
				Scanner scanner = new Scanner(text);
				while (scanner.hasNextLine()) {
					String line = scanner.nextLine();
					if (line.startsWith("~~~L")) {
						String localLine = scanner.nextLine();
						Scanner localScanner = new Scanner(localLine);
						localScanner.useDelimiter("; ");
						if (localScanner.hasNext("id\\d*")) {
							String target = localScanner.next("id\\d*");
							targetList.add(textName + ":" + target);
							break;
						}
					}
				}
			}
			if (!targetList.isEmpty()) {
				System.out.println(bugName);
				System.out.print("  ");
				for (String s: targetList)
					System.out.print(s + ";");
				System.out.println();
			}
		}
	}

}
