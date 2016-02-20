import java.util.*;
// generics
// generic array creation
public class Generics <E> {
  private final E[] _items;

  public Generics(int capacity){
    // not very good solution generates warning
    _items = (E[]) new Object[capacity];

  } 

  public void main(String[] args){
  }
}
