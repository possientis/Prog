import java.io.*;
import java.util.*;
//import java.math.*;
//import java.util.List;
//import java.util.ArrayList;
//import java.util.Random;

public class MyHashMap {

  public static void main(String[] args) throws IOException {

    //HashMap<K,V> implements interface Map<K,V>
    Map<String,Integer> dict = new HashMap<String,Integer>();

    dict.put("if",0);
    dict.put("else",1);
    dict.put("then",2);
    dict.put("elseif",3);

    Integer value = dict.get("notthere");

    if(value == null){
      System.out.println("The key was not found\n");
    }

    System.out.println("The value for 'if' is: " + dict.get("if") + '\n');

    dict.remove("if");

    value = dict.get("if");

    if(value == null){
      System.out.println("The key 'if' is no longer in dictionary");
    }

    Set<String> s = dict.keySet();

    Iterator<String> it = s.iterator();

    while(it.hasNext()){

      System.out.println(it.next());

    }

    Set<Map.Entry<String,Integer>> entries = dict.entrySet();
    Iterator<Map.Entry<String,Integer>> itt = entries.iterator();

    // dont even bother constructing iterator
    for(Map.Entry<String,Integer> entry :dict.entrySet()){

      System.out.println(entry.getKey() + ":" + entry.getValue());

    }





  }
}
