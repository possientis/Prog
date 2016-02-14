(* interface , typeclass *)
signature MAG_OBJ =
  sig
     type object
     val mag : object -> int
  end

(*implementing an interface, declaring a type to 
* be an instance of a tyepclass *)

structure IntMag : MAG_OBJ = 
  struct
    type object = int
    fun mag(x) = if x >= 0 then x else ~x
  end

local open IntMag in
  val y = ~7
  val z = mag(y)
end

signature DIST_OBJ =
  sig
    type object
    val dist: object * object -> int
  end

(* an ML functor is a normal function which takes
* arguments of type belonging to an interface and returns
* a value of type belonging to an interface.
* So a functor is a function between interfaces, or so it seems *)

functor MakeDistObj(structure MAG: MAG_OBJ) =
  struct
    type object = MAG.object
    val dist = fn (x, y) => 
      let
        val v = MAG.mag(x) - MAG.mag(y)
      in
        if v > 0 then v else ~v 
      end
end


signature CATEGORY =
  sig
    type object
    type arrow
    exception uncomposable

    val source: arrow -> object
    val target: arrow -> object
    val identity: object -> arrow
    val composable: arrow * arrow -> bool
    val compose: arrow * arrow -> arrow
end
