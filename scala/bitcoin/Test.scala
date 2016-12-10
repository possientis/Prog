// Don't understand why this fails to compile
import org.bitcoins.core.crypto._

object Test {
  def main(args: Array[String]){
    val key =  new ECKey()
    println("This is running")
  }
}
