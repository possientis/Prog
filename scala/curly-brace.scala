def func(x:Int) = x * 2

println(func(4))
println(func{4})  // curly braces one argument

def func2(x:Int, y:Int) = x + y
println(func2(4,3))
//println(func2{4,3}) // curly braces two arguments fail


