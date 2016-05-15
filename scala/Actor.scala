import scala.actors._

object sillyActor extends Actor {
  def act() {
    for (i <- 1 to 5) {
      println("I'm acting!")
      Thread.sleep(1000)
    }
  }
}


sillyActor.start()
seriousActor.start()
Thread.sleep(2000)
println("I am the main thread")


object seriousActor extends Actor {
  def act() {
    for (i <- 1 to 5) {
      println("To be or not to be.")
      Thread.sleep(1000)
    }
  }
}

/* this should work on more recent scala version?
val seriousActor2 = actor {
  for (i <- 1 to 5){
    println("That is the question.")
    Thread.sleep(1000)
  }
}
*/

// sending message to an actor
sillyActor ! "hi there"

/* failing too :(
val echoActor = actor {
  while (true) {
    receive {
    case msg => println("received message: " + msg)
    }
  }
}
*/

object echoActor extends Actor {
  def act(){
    println("echoActor is starting now")
    while(true) {
      receive {
        case msg  => println("received message: " + msg)
      }
    }
  }
}

echoActor.start()

echoActor ! "hi there!"
Thread.sleep(1000)
echoActor ! 15

Actor.self ! "hello"
Actor.self.receive { case x => x }




