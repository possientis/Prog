Test.jar : Test.class acm.jar
	cp acm.jar  Test.jar
	jar uf Test.jar Test.class
Test.class : Test.java
	javac -classpath acm.jar Test.java
clean :
	rm Test.class Test.jar
