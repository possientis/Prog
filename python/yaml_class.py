import yaml
import custom_class


my_obj = custom_class.MyClass()
my_obj.add_item(1)
my_obj.add_item(2)
my_obj.add_item(3)

print(my_obj)

# serialize
yaml_file = open('custom_class.yaml', 'w')
yaml.dump(my_obj,yaml_file)
yaml_file.close()

# deserialize
yaml_file = open('custom_class.yaml', 'r')
new_obj = yaml.load(yaml_file)
yaml_file.close()

print(new_obj)


