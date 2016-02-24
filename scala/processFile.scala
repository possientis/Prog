import scala.io.Source

def processFile1(filename: String, width: Int) {
  def processLine(filename: String, width: Int, line: String) {
    if (line.length > width) print(filename+": "+line)
  }
  val source = Source.fromFile(filename)
  for (line <- source.getLines) {
    processLine(filename, width, line)
  }
}

def processFile2(filename: String, width: Int) {
  def processLine(line: String) {
    if (line.length > width) print(filename+": "+line)
  }
  val source = Source.fromFile(filename)
  for (line <- source.getLines) {
    processLine(line)
  }
}
