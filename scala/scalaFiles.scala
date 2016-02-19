val filesHere = (new java.io.File(".")).listFiles

// creating a new collection with the for expression and 'yield' keyword.
// careful with syntax of for-yield expression:
// for <clauses> yield <body>
def scalaFiles =
  for {
    file <- filesHere
    if file.getName.endsWith(".scala")
  } yield file

// wrong syntax !!!!
//for(file <- filesHere; if file.getName.endsWith("blah")){ yield file }


for {
  file <- scalaFiles
} println(file)
