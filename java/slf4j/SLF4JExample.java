// Simple Logging Facade For Java
// simple logging facade for java

// NO BINDING
//
// This code is not going to compile unless you include the appropriate jar

// javac -cp /usr/share/java/slf4j-api.jar SLF4Example.java

// and it is not going to run either without the appropriate jar

// java -cp /usr/share/java/slf4j-api.jar:. SLF4JExample

// However, if you simply use slf4j-api.jar, you are including the generic 
// facade code, but missing a binding to a concrete logging framework

// SLF4J: Failed to load class "org.slf4j.impl.StaticLoggerBinder".
// SLF4J: Defaulting to no-operation (NOP) logger implementation
// SLF4J: See http://www.slf4j.org/codes.html#StaticLoggerBinder for ...

// in this case, all your logging actions default to 'no-op'

// WITH BINDING TO CONCRETE LOGGIN FRAMEWORK
// The binding needs to take place at compile time. Do not include
// more than one jar (beyond slf4j-api) in your class path.
// You can choose among the following:

// /usr/share/java/slf4j-jcl.jar    
// /usr/share/java/slf4j-jdk14.jar     
// /usr/share/java/slf4j-log4j12.jar  
// /usr/share/java/slf4j-migrator.jar
// /usr/share/java/slf4j-nop.jar    
// /usr/share/java/slf4j-simple.jar
//
// Note that not all of the above options will work immediately. There is
// probably a need to add more dependency jars on your classpath, or some 
// configuration xml file may be required somewhere etc. 
//
// Only the bindings 'simple' 'jdk14' and 'nop' work immediately.


import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class SLF4JExample {
  public static void main(String[] args) {
    Logger logger = LoggerFactory.getLogger("<SomeMessageCategoryName>");
    logger.info("Hello World");
  }
}




