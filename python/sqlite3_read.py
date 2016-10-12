import sqlite3

conn = sqlite3.connect('inventory.db');

cursor = conn.execute('select * from inventory_operatingsystem;')

print(cursor.fetchall())

conn.close()


