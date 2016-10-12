# python2 only

import storm.locals
import os
import storm_model

path = 'sqlite:///%s' % os.path.join(os.getcwd(),'inventory.db')

db = storm.locals.create_database(path)

store = storm.locals.Store(db)

for o in store.find(storm_model.OperatingSystem):
    print o.id, o.name, o.description

