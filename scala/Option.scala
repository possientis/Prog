// scala's Option type, similar to Haskell Maybe

val capitals = Map("France"->"Paris", "Japan"->"Tokyo")

val query1 = capitals get "France"
val query2 = capitals.get("France")

println(query1) // Some(Paris)
println(query2) // Some(Paris)

val query3 = capitals get "North Pole"
println(query3) // None

def show(x :Option[String]) = x match {
  case Some(s)  => s
  case None     => "?"
}

println(show(query1)) // Paris
println(show(query3)) // ?
