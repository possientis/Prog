val words = List("the","quick","brown","fox")


println(words map (_.toList))     // List(List(t, h, e), List(q, u, i, c, k), List(b, r, o, w, n), List(f, o, x))
println(words flatMap (_.toList)) // List(t, h, e, q, u, i, c, k, b, r, o, w, n, f, o, x)


// list of pairs (i,j) such that 1 <= j < i < 5
println (List.range(1, 5) flatMap (i => List.range(1,i) map (j => (i,j))))  // List((2,1), (3,1), (3,2), (4,1), (4,2), (4,3))

