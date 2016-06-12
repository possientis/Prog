const food = {
  init: function(type){
    this.type = type;
  },
  eat: function() {
      print('you ate the ' + this.type);
  }
};

const waffle = Object.create(food);
waffle.init('waffle');

const carrot = Object.create(food);
carrot.init('carrot');


print('waffle is food: ' + food.isPrototypeOf(waffle));
print('int is food: ' + food.isPrototypeOf(56254612546));
print('carrot is food: ' + food.isPrototypeOf(carrot));



