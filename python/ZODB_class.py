# only python2
import ZODB
import ZODB.FileStorage
import transaction
import persistent_class

filestorage = ZODB.FileStorage.FileStorage('zodb_filestorage.db')
db = ZODB.DB(filestorage)
conn = db.open()

root = conn.root()

noah = persistent_class.Account('noah', 1000)
print(noah)
root['noah'] = noah

jeremy = persistent_class.Account('jeremy', 1000)
print(jeremy)
root['jeremy'] = jeremy

transaction.commit()

conn.close()




