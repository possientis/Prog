// Singleton design pattern
function SingleObject(){

};
SingleObject.prototype.showMessage = function(){
   print("The single object is alive and well")
};
SingleObject.getInstance =function(){
  return SingleObject.prototype;
}


object1 = SingleObject.getInstance();
object1.showMessage();

object2 = SingleObject.getInstance();
if(object1 === object2){
  print("The two objects are the same");
}

