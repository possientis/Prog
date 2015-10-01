def echo(value=None):
    print("Execution starts when 'next()' is called for the first time.")
    try:
        while True:
            try:
                value = (yield value)
            except Exception as e:
                value = e
    finally:
        print("Don't forget to clean up when 'close()' is called.")


def main():
    generator = echo(1)
    print(next(generator))
    print(next(generator))
    print(next(generator))
    print(generator.send(2))
    print(next(generator))
    generator.throw(TypeError,"spam")
    print(next(generator))
    generator.close()
    print("Final message")


if __name__ == "__main__":
    main()
