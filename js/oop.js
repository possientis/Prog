function A(a){
  this.a = a;
};

function B(a,b){
  this.b = b;
  A.call(this.__proto__, a);
};

B.prototype = new A();

a = new A(2);
b = new A(5);
c = new B(3,8);


function debugObject(x){
  print("Object is of type: " + typeof(x));
  print("its list of properties is as follows:")
  for(i in x){
    print(i + " : " + x[i]);
  }
  if(x.__proto__ == A.prototype){
    print("object was constructed by A");
  }
}


