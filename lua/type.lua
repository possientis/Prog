print(type("Hello"))  -- string
print(type(5))        -- number
print(type(type))     -- function
print(type(nil))      -- nil
print(type({}))       -- table
print(type(string))   -- table
print(type(table))    -- table

print("****string****")
for k,v in pairs(string) do
  print(k,v)
end

print("****table****")
for k,v in pairs(table) do
  print(k,v)
end

