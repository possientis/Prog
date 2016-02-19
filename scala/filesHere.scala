// printing all file names in current directory
val filesHere = (new java.io.File(".")).listFiles
for (file <- filesHere)
  println(file)

println("----------------------------------------------------------------")
// adding a guard to iteration
for (file <- filesHere; if !file.getName.endsWith(".scala"))
  println(file)

println("----------------------------------------------------------------")
//you need the semi-colon ';' when using syntax with parentheses
for (
  file <- filesHere;
  if file.isFile;
  if file.getName.endsWith(".scala")
) println(file)

println("----------------------------------------------------------------")
//you do not need the semi-colon ';' when using syntax with curly braces
for {
  file <- filesHere
  if file.isFile
  if !file.getName.endsWith(".scala")
} println(file)

println("----------------------------------------------------------------")

def fileLines(file: java.io.File) =
  scala.io.Source.fromFile(file).getLines

def grep(pattern: String) =
  for {
    file <- filesHere
    if file.getName.endsWith(".scala")
    line <- fileLines(file)
    trimmed = line.trim // this is a val, but no val keyword
    if trimmed.matches(pattern)
  } println(file + ": " + line.trim)


grep(".*point.*") // looks like you need syntax .*blahblah.*
