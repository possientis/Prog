Table =
  { key1                  = "a"   -- key is 'key1"
  , ["a key with spaces"] = "b"   -- key is "a key with spaces"
  , [5]                   = "c"   -- key is 5, not "5"
  , [print]               = "d"   -- key is a refererence to function print
  }

Table.newKey = "e"
-- you cannot use nil as a key...

print(Table["key1"])
print(Table["a key with spaces"])
print(Table[5])
print(Table[print])
print(Table["newKey"])
print(Table["key does not exist"])
print(Table.newKey)

for k,v in pairs(Table) do
  print(k,v)
end

local function foo(t)
  t[1] = 5
end

local myTable = {}

print(myTable[1]) -- nil
foo(myTable)
print(myTable[1]) -- nil

local table1 = {}
local table2 = table1
table2[1] = 5
print(table1[1])  -- 5

