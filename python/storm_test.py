# python2 only

import storm.locals
import os
import storm_model

operating_system = storm_model.OperatingSystem()
operating_system.name = u'Windows'          # unicode values
operating_system.description = u'3.1.1'     # unicode values

# inventory.db is sqlite3 database file
path = 'sqlite:///%s' % os.path.join(os.getcwd(),'inventory.db')
print(path)

db = storm.locals.create_database(path)

store = storm.locals.Store(db)
store.add(operating_system)
store.commit()


