import pickle

# serializing a dictionary
some_dict = {'a': 1, 'b': 2}

pickle_file = open('some_dict.pkl', 'wb')

pickle.dump(some_dict, pickle_file)

pickle_file.close()


# deserializing
pickle_file = open('some_dict.pkl', 'rb')

new_dict = pickle.load(pickle_file)

pickle_file.close()

print(new_dict)


# even better
list_of_dicts = [{str(i): i} for i in range(5)]

print(list_of_dicts)

pickle_file = open('list_of_dict.pkl', 'wb')

for d in list_of_dicts:
    pickle.dump(d, pickle_file)

pickle_file.close()

# what happens when deserializing?
pickle_file = open('list_of_dict.pkl', 'rb')

while True:
    try:
        new_dict = pickle.load(pickle_file)
        print(new_dict)
    except EOFError:
        print("end-of-file")
        break


