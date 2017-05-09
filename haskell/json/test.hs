import Test.HUnit
import JLexer
import JParser
import JValue

value1 = JObject [JKeyVal ("foo",JNumber 1),   JKeyVal ("bar", JBool False)]
value2 = JObject [JKeyVal ("foo",JNumber 3),   JKeyVal ("bar", JBool True)]
value3 = JObject [JKeyVal ("foo",JNumber 4.5), JKeyVal ("bar", JBool True)]
value4 = JArray [value1, value2, value3]
value5 = JObject [JKeyVal ("foo", value4), JKeyVal ("bar", value1)]

test1 = TestCase $ assertEqual "test1" value1 $ jparse (show value1)
test2 = TestCase $ assertEqual "test2" value2 $ jparse (show value2)
test3 = TestCase $ assertEqual "test3" value3 $ jparse (show value3)
test4 = TestCase $ assertEqual "test4" value4 $ jparse (show value4)
test5 = TestCase $ assertEqual "test5" value5 $ jparse (show value5)

tests = TestList [ test1, test2, test3, test4, test5]

main = do 
  print $ jparse (show value5)
  runTestTT tests



