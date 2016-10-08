import yaml

# serializing object with yaml 

yaml_file = open('test.yaml', 'w')

d = {'foo': 'a', 'bar': 'b', 'bam': [1, 2, 3]} 

print(d)

yaml.dump(d, yaml_file, default_flow_style=False)

yaml_file.close()

# deserializing with yaml

yaml_file = open('test.yaml', 'r')

d2 = yaml.load(yaml_file) 

yaml_file.close()

print(d2)

# serializing in non-block mode

yaml_file = open('non_block.yaml', 'w')

d = {'foo': 'a', 'bar': 'b', 'bam': [1, 2, 3]} 
print(d)

yaml.dump(d, yaml_file)

yaml_file.close()


# deserializing

yaml_file = open('non_block.yaml', 'r')

d2 = yaml.load(yaml_file) 

yaml_file.close()

print(d2)

