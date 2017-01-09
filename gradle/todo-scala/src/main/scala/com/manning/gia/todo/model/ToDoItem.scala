package com.manning.gia.todo.model

class ToDoItem extends Ordered[ToDoItem] {
  var id: Long = _
  var name: String = _
  var completed: Boolean = _

  def getId: Long = {
    id
  }

  def setId(id: Long) = {
    this.id = id
  }

  def getName: String = {
    name
  }

  def setName(name: String) = {
    this.name = name
  }

  def isCompleted: Boolean = {
    completed
  }

  def setCompleted(completed: Boolean) = {
    this.completed = completed
  }

  override def hashCode : Int = {
    var result = id match {
      case t: Long  => t.hashCode
//      case _        => 0
    }

    result = 31 * result + (name match {
      case t: String  => t.hashCode()
//      case _          => 0
    })

    result = 31 * result + (completed match {
      case true    => 1
      case false   => 0
    })

    result
  }

  override def compare(that: ToDoItem) = {
    this.id compare that.id
  }

  override def equals(that: Any) = {
    that match {
      case t: ToDoItem => t.id == id && t.name == name && t.completed == completed
      case _ => false
    }
  }

  override def toString: String = {
    id + ": " + name + " [completed: " + completed + "]"
  }

}
