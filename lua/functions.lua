function DoMath(n)
  return n*2
end

function Foo1 (arg1, arg2)
  print(arg1)
  print(arg2)
end

Foo2 = function(arg1,arg2)
  print(arg1)
  print(arg2)
end

local function foo()
  return 1,2,3,4,5
end
print(foo())
