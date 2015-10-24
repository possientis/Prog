import java.io.*;
import java.util.*;
import java.util.concurrent.*;


public class Pascal{

  private static List<Integer> newList(){
    // choice of List<E> implementation goes here
    
    return new Vector<Integer>();
    //return new ArrayList<Integer>();
    //return new CopyOnWriteArrayList<Integer>();
    //return new LinkedList<Integer>();
    //return new Stack<Integer>();
  }

  public static List<Integer> pascal(int n){
    if(n == 1){
      List<Integer> list = newList(); 
      list.add(1); 
      return list;
    } 
    else{
      return addList(shiftLeft(pascal(n - 1)),shiftRight(pascal(n - 1)));
    }
  }

  public static List<Integer> fastPascal(int n){
    if(n == 1){
      List<Integer> list = newList();
      list.add(1);
      return list;
    }
    else{
      List<Integer> list = pascal(n - 1);
      return addList(shiftLeft(list),shiftRight(list));
    }
  }


  private static List<Integer> shiftLeft(List<Integer> list){
    List<Integer> temp = newList();
    temp.addAll(list);
    temp.add(0,0);  // adding 0 to the left
    return temp;
  }

  private static List<Integer> shiftRight(List<Integer> list){
    List<Integer> temp = newList();
    temp.addAll(list);
    temp.add(0);  // adding 0 to the end (right)
    return temp;
  }

  private static List<Integer> addList(List<Integer> list1, List<Integer> list2){
    List<Integer> temp = newList();
    Iterator<Integer> iter1 = list1.iterator();
    Iterator<Integer> iter2 = list2.iterator();
    while(iter1.hasNext()){
      temp.add(iter1.next()+iter2.next());
    }
    return temp;
  }

  public static void main(String[] args){
    List<Integer> list = fastPascal(20);
    System.out.println(list);
  }
}
