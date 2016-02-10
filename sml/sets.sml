exception empty

fun listRemove(item)(aList) = List.filter(fn x => x <> item)(aList)
fun listMember(item)(aList) = List.exists(fn x => x = item)(aList)

abstype 'a Set = set of 'a list
  with val emptyset = set([])
  fun fromList(L) = set(L)
  fun isEmpty(set(s)) = List.length(s)=0
  fun singleton(x) = set([x])
  fun union(set(s))(set(t)) = set(s @ t)
  fun member(x)(set(L)) = listMember(x)(L)
  fun remove(x)(set(L)) = set(listRemove(x)(L))
  fun split(set(nil)) = raise empty
    | split(set(head::rest)) = (head, remove(head)(set(rest)))
end

fun subset(s)(t) = if isEmpty(s) then true else 
  let val (item, rest) = split(s) in
    member(item)(t) andalso subset(rest)(t)
  end

fun setEq(s)(t) = subset(s)(t) andalso subset(t)(s)




