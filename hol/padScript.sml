1 :: [2,3,4,5];
val l = it;
tl l;
hd it;
tl(tl(tl(tl(tl l))));
val l1 = [1,2,3];
val l2 = ["a","b","c"];
explode "a b c";
val triple1 = (1,true,"abc");
#2 triple1;
val triple2 = (1,(true,"abc"));
#2 triple2;
(* zip; *)
fun zip(l1,l2) =
  if null l1 orelse null l2 
    then []
    else (hd l1, hd l2) :: zip (tl l1, tl l2);
zip ([1,2,3],["a","b","c"]);
fun curried_zip l1 l2 = zip (l1,l2);
fun zip_num l2 = curried_zip [0,1,2] l2;
zip_num ["a","b","c"];
(* 3 div 0; *)
3 div 0 handle _ => 0;


