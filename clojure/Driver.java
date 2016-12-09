// calling clojure code from java

// remember to compile using javac -classpath /usr/share/java/clojure-1.6.0.jar
// for these imports to be successful. Also you need to launch as 
// java -cp .:/usr/share/java/clojure-1.6.0.jar Driver
// see java.sh ....


import clojure.lang.RT;
import clojure.lang.Var;

public class Driver {
  public static void main(String[] args) throws Exception {
    RT.loadResourceScript("clojure_script.clj");
    Var report = RT.var("clj.script.example", "print-report");
    long result =  (long) report.invoke("Siva");
    System.out.println("Result: " + result);
  }
}


