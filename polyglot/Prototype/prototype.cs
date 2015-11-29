// Prototype design pattern
// Imagine that in order to instantiate certain objects we need to carry out
// expensive database queries. In order to improve performance, it would 
// be beneficial to cache whatever object is created from the database
// and return a copy of the cached object whenever a subsequent request
// for object instantiation arises.

using System;
using System.Collections.Generic;

abstract class Shape : ICloneable {

  private string id;

  abstract public void Draw();

  public string ID{
    get{return id;}
    set{id = value;}
  }

  abstract public object Clone();
}


class Rectangle : Shape {

  public override void Draw(){
    Console.WriteLine("Inside Rectangle::Draw() method.");
  }

  public override object Clone(){

    Rectangle clone = new Rectangle();
    clone.ID = this.ID;
    return clone;
  }
}

class Square : Shape {

  public override void Draw(){
    Console.WriteLine("Inside Square::Draw() method.");
  }

  public override object Clone(){

    Square clone = new Square();
    clone.ID = this.ID;
    return clone;
  }
}

class Circle : Shape {

  public override void Draw(){
    Console.WriteLine("Inside Circle::Draw() method.");
  }

  public override object Clone(){

    Circle clone = new Circle();
    clone.ID = this.ID;
    return clone;
  }
}


class PrototypeManager {

  public PrototypeManager(){
    shapeMap = new Dictionary<string,Shape>();
  }

  public Shape GetShape(string shapeId){
    Shape cachedShape = shapeMap[shapeId];
    return (Shape) cachedShape.Clone();
  }

  // for each shape, run database query and create shape prototype
  // to be saved in cache
  public void loadCache(){

    Rectangle rect = new Rectangle();
    rect.ID = "1";
    shapeMap[rect.ID] = rect;

    Square square = new Square();
    square.ID = "2";
    shapeMap[square.ID] = square;

    Circle circle = new Circle();
    circle.ID = "3";
    shapeMap[circle.ID] = circle;

  }

  private Dictionary<string,Shape> shapeMap;
}

public class Prototype {


  public static void Main(string[] args){

    // need a prototype manager
    PrototypeManager manager = new PrototypeManager();
    // prototype manager registers a few prototype
    manager.loadCache();
    // prototype manager can now be used as factory object
    Shape clonedShape1 = manager.GetShape("1");
    clonedShape1.Draw();

    Shape clonedShape2 = manager.GetShape("2");
    clonedShape2.Draw();

    Shape clonedShape3 = manager.GetShape("3");
    clonedShape3.Draw();
  }

}
