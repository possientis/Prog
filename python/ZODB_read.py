#python2 only

import ZODB
import ZODB.FileStorage

filestorage = ZODB.FileStorage.FileStorage('zodb_filestorage.db')

db = ZODB.DB(filestorage)

conn = db.open()

root = conn.root()

print(root)


