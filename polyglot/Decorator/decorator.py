# Decorator Design Pattern

# The implementation of the decorator pattern in python does not follow
# the pattern encountered in other languages, due to python support for
# multiple inheritance


class Pizza(object):
    @property
    def description(self):
        raise NotImplementedError("Pizza::description is not implemented")
    @property
    def cost(self):
        raise NotImplementedError("Pizza::cost is not implemented")


class PlainPizza(Pizza):
    @property
    def description(self): return "Plain pizza"
    @property
    def cost(self): return 3.0

class WithExtraCheese(object):
    @property
    def description(self): return super().description + " + extra cheese" 
    @property
    def cost(self): return super().cost + 0.5

class WithExtraOlives(object):
    @property
    def description(self): return super().description + " + extra olives" 
    @property
    def cost(self): return super().cost + 0.7

class WithExtraAnchovies(object):
    @property
    def description(self): return super().description + " + extra anchovies" 
    @property
    def cost(self): return super().cost + 0.8

class NicePizza(WithExtraCheese, PlainPizza)    : pass
class SuperPizza(WithExtraOlives, NicePizza)    : pass
class UltraPizza(WithExtraAnchovies, SuperPizza): pass

plainPizza  = PlainPizza()
nicePizza   = NicePizza()
superPizza  = SuperPizza()
ultraPizza  = UltraPizza()


print(  "Plain Pizza: "     +
        "\tCost: "          + str(plainPizza.cost) +
        "\tDescription: "   + plainPizza.description)

print(  "Nice Pizza: "      +
        "\tCost: "          + str(nicePizza.cost) +
        "\tDescription: "   + nicePizza.description)

print(  "Super Pizza: "     +
        "\tCost: "          + str(superPizza.cost) +
        "\tDescription: "   + superPizza.description)

print(  "Ultra Pizza: "     +
        "\tCost: "          + str(ultraPizza.cost) +
        "\tDescription: "   + ultraPizza.description)



