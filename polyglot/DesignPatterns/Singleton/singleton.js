// Singleton design pattern
function SingleObject(){

};
SingleObject.prototype.showMessage = function(){
   console.log("The single object is alive and well")
};
SingleObject.getInstance =function(){
  return SingleObject.prototype;
}


object1 = SingleObject.getInstance();
object1.showMessage();

object2 = SingleObject.getInstance();
if(object1 === object2){
  console.log("The two objects are the same");
}

