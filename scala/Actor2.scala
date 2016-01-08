import scala.actors.Actor
// cant make this work

object Actor2 {

  def main(args: Array[String]){
    println("Actor running...")
    
    val echoServer = actor(new Act {
      become {
        case msg => println("echo" + msg)
      }
    })


  }
}
