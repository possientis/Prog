def containsZero(nums: List[Int]) = nums.exists(_ == 0)

println(containsZero(Nil))
println(containsZero(List(1,3,0,5)))
