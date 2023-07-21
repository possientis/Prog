-- You can have as many '==' between '[' and matching ']' to create a string
local str = [==[Hello world,
  This is a long multi-line string that can contain quotation marks: " '
  as well as box brackets: [[ ]] ]=] [=[
  ]==]
print(str)

-- concatenation
print("Hello ".."World!")
print(5 .. 0) -- 50
-- length
print(#"Hello") -- 5
