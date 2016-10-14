
import os
from sqlalchemy import create_engine
from sqlalchemy import Table, Column, Integer, Text, VARCHAR, MetaData
from sqlalchemy.orm import mapper
from sqlalchemy.orm import sessionmaker

path = 'sqlite:///%s' % os.path.join(os.getcwd(), 'inventory.db')

engine = create_engine(path)

metadata = MetaData()

os_table = Table(
    'inventory_operatingsystem', 
    metadata,
    Column('id', Integer, primary_key=True),
    Column('name', VARCHAR(50)),
    Column('description', Text()),
)


class OperatingSystem(object):
    def __init__(self, name, description):
        self.name = name
        self.description = description
    def __repr__(self):
        return "<OperatingSystem('%s','%s')>" % (self.name, self.description)

mapper(OperatingSystem, os_table)
Session = sessionmaker(bind=engine, autoflush=True)
session = Session()

# reading a table
for os in session.query(OperatingSystem):
    print(os)

# writing into the table
ubuntu_710 = OperatingSystem(name='Linux', description='2.6.22-14 kernek')
#session.save(unbuntu_710)   # probably new API in python3, failure
session.commit
