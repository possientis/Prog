#python2 only

import ZODB
import ZODB.FileStorage
import transaction
import persistent_class 

filestorage = ZODB.FileStorage.FileStorage('zodb_filestorage.db')
db = ZODB.DB(filestorage)
conn = db.open()

root = conn.root()
noah = root['noah']
print "BEFORE WITHDRAWAL"
print "================="
print(noah)

jeremy = root['jeremy']
print(jeremy)
print("-----------------")


flag = True

while flag:
    try:
        transaction.begin()
        jeremy.deposit(300)
        noah.withdraw(300)
        transaction.commit()
        flag = False
    except persistent_class.OutOfFunds:
        print("OutOfFunds Error")
        print("Current account information:")
        print(noah)
        print(jeremy)
        transaction.abort()
        break

print("AFTER WITHDRAWAL")
print("================")
print(noah)
print(jeremy)
print("----------------")

conn.close()



