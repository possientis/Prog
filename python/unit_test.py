import unittest

class TestOfUnitTesting(unittest.TestCase):
    def setUp(self):
        pass

    def testExample1(self):
        self.assertEqual("abc","abc")
        self.assertEqual("def","def")

    def testExample2(self):
        self.assertEqual("ghi","ghi")




if __name__ ==  '__main__':
    unittest.main()



