# python2 only
import ZODB
import ZODB.FileStorage
import transaction

# writing to database, serialize

filestorage = ZODB.FileStorage.FileStorage('zodb_filestorage.db')

db = ZODB.DB(filestorage)

conn = db.open()

root = conn.root()

root['list'] = ['this', 'is', 'a', 'list']
root['dict'] = {'this': 'is', 'a': 'dict'}


transaction.commit()
conn.close()


# reading from database, deserialize

conn = db.open()

root = conn.root()

print(root.items)

conn.close()



