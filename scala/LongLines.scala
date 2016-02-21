import scala.io.Source
object LongLines {
  def processFile(filename: String, width: Int) {
    val source = Source.fromFile(filename)
    for (line <- source.getLines)
    processLine(filename, width, line)
  }
  def processLine(filename: String, width: Int, line: String) {
    if (line.length > width)
    println(filename+": "+line.trim)
  }
  def main(args: Array[String]) {
    val width = args(0).toInt
    for (arg <- args.drop(1))
    processFile(arg, width)
  }
}

