import java.io._

def withPrintWriter(file: File, op: PrintWriter => Unit) {
  val writer = new java.io.PrintWriter(file)
  try {
    op(writer)
  } finally {
    writer.close()
  }
}


println(new java.util.Date) // current data and time

withPrintWriter(new File("log"), writer => writer.println(new java.util.Date))


/* This fails, but should work (page 200 scala book)
// using curly braces to invoke function is only allowed when 
// function takes one argument only ???

// this supports curly braces syntax
withPrintWriter {
  new File("log"),
  writer => writer.println(new java.util.Date)
}
*/


def withPrintWriter2(file: File)(op: PrintWriter => Unit) {
  val writer = new java.io.PrintWriter(file)
  try {
    op(writer)
  } finally {
    writer.close()
  }
}

// this one works, for some reason
val file = new File("log2")
// this supports curly braces syntax
withPrintWriter2(file) {
  writer => writer.println(new java.util.Date)
}








