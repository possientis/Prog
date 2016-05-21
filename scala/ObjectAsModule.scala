// by using modules as object, classes become templates for modules
// 
abstract class Food(val name: String) {
  override def toString() = name
}
object Apple extends Food("Apple")
object Orange extends Food("Orange")
object Cream extends Food("Cream")
object Sugar extends Food("Sugar")

abstract class Recipe(val name: String,
                      val ingredients: List[Food],
                      val instructions: String) {
  override def toString() = name
}

object FruitSalad extends Recipe(
  "fruit salad",
  List(Apple, Orange, Cream, Sugar),
  "Stir it all together.")


object SimpleDatabase extends Database with SimpleFoods with SimpleRecipes {
  // first 
  def allFoods = List(Apple, Orange, Cream, Sugar)
  def allRecipes: List[Recipe] = List(FruitSalad)
  // second
  private var categories = List(
    FoodCategory("fruits", List(Apple, Orange)),
    FoodCategory("misc", List(Cream, Sugar)))
  def allCategories = categories  // does not compile here for some reason
}



val apple = SimpleDatabase.foodNamed("Apple")
println(apple)  //  Some(Apple)

println(SimpleBrowser.recipesUsing(apple.get))  // List(fruit salad)

abstract class Database extends FoodCategories{
  def allFoods: List[Food]
  def allRecipes: List[Recipe]
  def foodNamed(name: String) = 
    allFoods.find(f => f.name == name)
  def allCategories
}

abstract class Browser {
  val database: Database
  def recipesUsing(food: Food) =
    database.allRecipes.filter(recipe => recipe.ingredients.contains(food))
  def displayCategory(category: database.FoodCategory) {
    //...
  }
}

object SimpleBrowser extends Browser {
  val database = SimpleDatabase
}

object StudentDatabase extends Database {
  object FrozenFood extends Food("FrozenFood")
  object HeatItUp extends Recipe(
    "heat it up",
    List(FrozenFood),
    "Microwave the 'food' for 10 minutes.")
  def allFoods = List(FrozenFood)
  def allRecipes = List(HeatItUp)
  def allCategories = List(
    FoodCategory("edible", List(FrozenFood)))
}

object SillyBrowser extends Browser {
  val database = StudentDatabase
}

trait FoodCategories {
  case class FoodCategory(name: String, foods: List[Food])
}

trait SimpleFoods {
  object Pear extends Food("Pear")
  def allFoods = List(Apple, Pear)
  def allCategories = Nil
}


trait SimpleRecipes {
  self: SimpleDatabase.type => 
  object FruitSalad extends Recipe(
    "fruit salad",
    List(Apple, Pear), // now Pear is in scope
    "Mix it all together.")
    def allRecipes = List(FruitSalad)
}




