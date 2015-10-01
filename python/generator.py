def city_generator():
    yield("London")
    yield("Paris")
    yield("Berlin")
    yield("Rome")
    yield("Madrid")

def intgen():
    x = 0
    while True:
        yield(x);
        x += 1

def main():
    print('Main is now running...\n')
    city = city_generator()
    print(next(city))
    print(next(city))
    print(next(city))
    print(next(city))
    print(next(city))
    integers = intgen()
    print(next(integers))
    print(next(integers))
    print(next(integers))
    print(next(integers))
    print(next(integers))
    print(next(integers))

if __name__ == "__main__":
    main()
