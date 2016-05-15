import scala.actors._
import java.net.InetAddress
import java.net.UnknownHostException

//println(InetAddress.getByName("yahoo.com"))
// I dont get this,
// there seems to be a deadlock anyway...

/*
Writing an actor to use react instead of receive is challenging, but pays
off in performance. Because react does not return, the calling actor’s call
stack can be discarded, freeing up the thread’s resources for a different actor.
At the extreme, if all of the actors of a program use react , then they can be
implemented on a single thread.
*/

object NameResolver extends Actor {
  def act() {
    react { // the react method (like 'receive') expects a handler
      case (name: String, actor: Actor) => 
        actor ! (name, getip(name))
        act()
      case msg =>
        println("Unhandled message: " + msg)
        act()
    }
  }

  def getip(name: String): Option[InetAddress] = {
    try {
      Some(InetAddress.getByName(name))
    } catch {
      case _:UnknownHostException => None
    }
  }
}

NameResolver.start()
NameResolver ! ("www.scala-lang.org", Actor.self)
Actor.self.receiveWithin(2000){ case x => x }
