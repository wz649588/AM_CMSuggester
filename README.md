# AM_CMSuggester
This is the implementation for the paper "Automatic Method Change Suggestion to Complement Multi-Entity Edits".

## Requirements
This repository contains several Eclipse Plugin projects. The program can run normally under the following conditions:
* JDK 7 (or use the JDK 7 compatible mode of JDK 8, since JDK 7 is hard to find now)
* Eclipse for RCP and RAP Developers, Version: Luna Release (4.4.0)
* Copying the Jar file org.apache.log4j_1.2.13.v200903072027.jar to plugins/ folder of EClipse.
* SQLite

## Installation
Users need to import the projects into Eclipse. Note that these projects should be imported as Eclipse Plugin projects.

## Downloading Input Files
Users can download the program's input files from [Mendeley](https://data.mendeley.com/datasets/tmv2pp964r/3). The files includes the input Java source code commits, the element list, the project libraries, and exported database tables.

## Configuration
Users need to download necessary input files for the program, and save the files in the file system. 
Before running the program, users need to do some configurations in the code.

### Path of the Java source code commits
In the ConsoleGSydit project, the locations for configurations for input source code changes are in the Application.java in the consolegsydit package.
* Aries: line 71
* Cassandra: line 74
* Derby: line 77
* Mahout: line 80
* ActiveMQ: line 83
* Uima: line 92

Please modify the above code to match the paths of the according files saved in your computer.

### Path of Element List
In the ConsoleGSydit, the code location for configuration for input element list is in line 75 of the CommitComparatorClient.java file in the edu.vt.cs.changes package.

### Path of Java Library
The library files in this path will be used for analysis purpose. Users can set it in the line 76 of the CommitComparatorClient.java file in the edu.vt.cs.changes package.

### Path of Project Library
The project library in this path will also be used for analysis purpose. Users can set it in the line 77 of the CommitComparatorClient.java file in the edu.vt.cs.changes package.

### Path of SQLite Database file
The program uses SQLite as its database. Users need to first create an empty SQLite database and change the code to set the database file path. The path setting is in the edu.vt.cs.sql package's SqliteManager.java file's line 12 in the ConsoleGSydit project.

### Import Database Tables
Users should import the database tables to the created SQLite database from the downloaded SQL files.

## Running
Users should run the program in Eclipse, since the projects are Eclipse Plugin projects. The repository includes multiple projects, and users should run the ConsoleGSydit project as an Eclipse Application.
