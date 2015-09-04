def city_generator():
    yield("London")
    yield("Paris")
    yield("Berlin")
    yield("Rome")
    yield("Madrid")

def main():
    print('Main is now running...\n')
    city = city_generator()
    print(next(city))
    print(next(city))
    print(next(city))
    print(next(city))
    print(next(city))
