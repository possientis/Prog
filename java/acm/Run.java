// Run.java
// this is an attempt at translating the scripts run.sh, run.py, run.scm and
// run.c (compiled as 'run') in java

import java.io.*;
import java.lang.Runtime;
import java.nio.file.*;

public class Run {

  public static void main(String[] argv)
    throws IOException, InterruptedException {

    /* checking a single argument has been passed */
    if(argv.length != 1){
      System.err.println("Usage: java Run filename[.java]");
      System.exit(0);
    }

    /* retrieving filename */
    String filename = argv[0];

    /* removing the .java extension if applicable */
    int len = filename.length();
    if(len > 5){  // no ".java" extension otherwise
      String last5Char = filename.substring(len-5,len);
      if(last5Char.equals(".java")){
        filename = filename.substring(0,len-5);
      }
    }

    /* setting up various strings */
    String filename_class = filename + ".class";
    String filename_jar = filename + ".jar";
    String filename_html = filename + ".html";
    String filename_java = filename + ".java";

    /* retrieving Runtime object */
    Runtime run = Runtime.getRuntime();


    /* cleaning up previously created files, if any */
    Process p1,p2,p3;
    p1 = run.exec("rm -f " + filename_class);
    p2 = run.exec("rm -f " + filename_jar);
    p3 = run.exec("rm -f " + filename_html);
    p1.waitFor();
    p2.waitFor();
    p3.waitFor();


    /* compiling filename.java */
    p1 = run.exec("javac -classpath acm.jar " + filename_java);

    /* copying acm.jar as filename.jar */
    p2 = run.exec("cp acm.jar " + filename_jar);

    /* need to wait before proceeding to next step */
    p1.waitFor();
    p2.waitFor();

    /* adding filename.class to filename.jar */
    p1 = run.exec("jar uf " + filename_jar + " " + filename_class);
    p1.waitFor();

    /* creating html file */
    PrintWriter writer = new PrintWriter(filename_html, "UTF-8");
    String str = "<html><applet archive=" + filename_jar
               + " code=" + filename_class
               + " width=1000 height=600></applet></html>";
    writer.write(str);
    writer.close();

    /* launching applet */
    p1 = run.exec("appletviewer " + filename_html);
    p1.waitFor();

    /* final clean up */
    p1 = run.exec("rm -f " + filename_class);
    p2 = run.exec("rm -f " + filename_jar);
    p3 = run.exec("rm -f " + filename_html);
    p1.waitFor();
    p2.waitFor();
    p3.waitFor();

    System.exit(0);

  }

}
