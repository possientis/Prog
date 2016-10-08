import pickle
import custom_class


my_obj = custom_class.MyClass()
my_obj.add_item(1)
my_obj.add_item(2)
my_obj.add_item(3)

print(my_obj)

# serialize
pickle_file = open('custom_class.pkl', 'wb')
pickle.dump(my_obj,pickle_file)
pickle_file.close()

# deserialize
pickle_file = open('custom_class.pkl', 'rb')
new_obj = pickle.load(pickle_file)
pickle_file.close()

print(new_obj)




