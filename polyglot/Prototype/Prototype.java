// Prototype design pattern
// Imagine that in order to instantiate certain objects we need to carry out
// expensive database queries. In order to improve performance, it would 
// be beneficial to cache whatever object is created from the database
// and return a copy of the cached object whenever a subsequent request
// for object instantiation arises.

import java.util.*;

abstract class Shape implements Cloneable {

  private String id;

  abstract public void draw();


  public String getId(){
    return id;
  }

  public void setId(String id){
   this.id = id;
  }

  @Override
  public Object clone(){

    Object clone = null;

    try{
      clone = super.clone();
    } catch (CloneNotSupportedException e){
      e.printStackTrace();
    }

    return clone;
  }
}

class Rectangle extends Shape {

  @Override
  public void draw(){
    System.out.println("Inside Rectangle::draw() method.");
  }
}

class Square extends Shape {

  @Override
  public void draw(){
    System.out.println("Inside Square::draw() method.");
  }
}

class Circle extends Shape {

  @Override
  public void draw(){
    System.out.println("Inside Circle::draw() method.");
  }
}


class PrototypeManager {

  public PrototypeManager(){
    shapeMap = new Hashtable<String,Shape>();
  }

  public Shape getShape(String shapeId){
    Shape cachedShape = shapeMap.get(shapeId);
    return (Shape) cachedShape.clone();
  }

  // for each shape, run database query and create shape prototype
  // to be saved in cache
  public void loadCache(){

    Rectangle rect = new Rectangle();
    rect.setId("1");
    shapeMap.put(rect.getId(),rect);

    Square square = new Square();
    square.setId("2");
    shapeMap.put(square.getId(),square);

    Circle circle = new Circle();
    circle.setId("3");
    shapeMap.put(circle.getId(),circle);

  }

  private Hashtable<String,Shape> shapeMap;
}

public class Prototype {


  public static void main(String[] args){

    // need a prototype manager
    PrototypeManager manager = new PrototypeManager();
    // prototype manager registers a few prototype
    manager.loadCache();
    // prototype manager can now be used as factory object
    Shape clonedShape1 = manager.getShape("1");
    clonedShape1.draw();

    Shape clonedShape2 = manager.getShape("2");
    clonedShape2.draw();

    Shape clonedShape3 = manager.getShape("3");
    clonedShape3.draw();
  }

}
