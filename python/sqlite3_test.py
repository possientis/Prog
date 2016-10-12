import sqlite3

conn = sqlite3.connect('inventory.db');

cursor = conn.execute(  # returns a database cursor object
    """
    insert into inventory_operatingsystem (name,description) 
    values ('Linux', '2.0.34 kernel');
    """
    )

print(cursor.fetchall())    # []

conn.commit()

conn.close()


conn = sqlite3.connect('inventory.db');

cursor = conn.execute('select * from inventory_operatingsystem;')

print(cursor.fetchall())


conn.close()


