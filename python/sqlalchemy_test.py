import os
from sqlalchemy import create_engine
from sqlalchemy import Table, Column, Integer, Text, VARCHAR, MetaData
from sqlalchemy.orm import mapper
from sqlalchemy.orm import sessionmaker

path = 'sqlite:///%s' % os.path.join(os.getcwd(), 'inventory.db')

engine = create_engine(path)
