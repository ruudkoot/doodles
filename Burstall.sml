(** 2.1  Expressions, values and environments **)
(3+4)*5;
not(true andalso false);
val m = (3+4)*5;
val x = not(true andalso false);
val m = (3+4)*5 and n = 6*7;
val m = (3+4)*5; val n = 6*m;
let val m = (3+4)*5 in m*m + (m+1)*(m+1) end;
let val x = 1 in if x=1 then 0 else 2+x end;

(** 2.2  Functions **)
infix 4 +;
fun f(x) = 2*x;
fn x => 2*x;
(fn x => 2*x)(3);
val f = fn x => 2*x;

(* 2.2.1  Recursive definitions *)
fun factorial(x) = if x = 0 then 1 else x*factorial(x-1);
factorial(10);
fun even(x) = if x=0 then true else
                      if x > 0 then not(even(x-1))
                               else not(even(x+1));
even(1000);
even(3333);

(* 2.2.2  Higher order functions *)
fun eval_at_one(f) = f(1);
eval_at_one(factorial);
eval_at_one(fn x => if x > 0 then true else false);
fun poly_eval(f) = f(f(3)) + f(3) + 3;
poly_eval(factorial);
fun add_on(m) = fn n => m + n;
add_on(3);
fun add_on(m)(n) = m + n;
fun poly(f)(x) = f(f(x)) + f(x) + x;
poly_eval(f);

(** 2.3  Types **)

(* 2.3.1  Primitive types *)

fun add(x:int,y:int) = x+y;
"the quick brown fox" ^ "jumps over the lazy dog";
size "the quick brown fox";
size;
();

(* 2.3.2  Compund types *)
(2,true,"brown");
{name="fred", salary=10000, gender=true};

(* 2.3.3  Type abbreviation *)
type Fcn_and_Int = (int -> int) * int;

(** 2.4  Type polymorphism **)
fun first(x,y) = x;
first(2,4);
first(2,true);
fun twice(f) = fn x => f(f(x));
fun square(x) = x*x;
twice(square)(3);
square(square(3));
[1,2,3];
[true,false,true,false];
(* [1,true,6]; *)
nil;
op ::;
1::(2::(3::nil));

(** 2.5 Patterns **)
val v = (3,false,4);
val (x,y,z) = v;
z;
val (x,y,_) = v;
(* val (x,x,z) = v; *)
val x = 3;
val r = {name = ("joe","smith"), age = 40};
val {name = (_,surname), age = _} = r;
val v = ((1,2),3);
val (x as (_,y),_) = v; (* @-pattern in Haskell *)

(* 2.6  Defining types *)
datatype Colour = red | blue | green;
fun warm(red)   = true
  | warm(blue)  = false
  | warm(green) = false;
warm(red);
warm(green);
fun warm (x) = case x of red => true | blue => false | green => false;
warm(red);
warm(green);
datatype Plant = flower of string*int*Colour |
                 foliage of string*int;
flower("rose",3,red);
foliage("ferm",2);
fun height(flower(_,n,_)) = n
  | height(foliage(_,n)) = n;
datatype Num = zero | succ of Num;
fun even(zero) = true
  | even(succ(n)) = not(even(n));
fun add(zero,n) = n
  | add(succ(m),n) = succ(add(m,n));
datatype 'a Pair = pair of ('a * 'a);
pair(3,4);
pair(true,false);
fun first(pair(x,y)) = x;
datatype 'a mylist = mynil | mycons of 'a * ('a mylist);
mycons(true,mycons(false,mynil));
fun length nil = 0
  | length (h :: t) = 1 + length t;
length [1,2,3,4];
fun member(e,nil) = false
  | member(e,h::t) = if e=h then true else member(e,t);
member(3,[1,2,3,4,5,6,7]);
member(9,[1,2,3,4,5]);
fun append(nil,y) = y
  | append(h::t,y) = h :: append(t,y);
append([1,2,4],[8,6,4]);
fun reverse(x) =
    let
        fun reverse'(acc,nil)  = acc
          | reverse'(acc,h::t) = reverse'(h::acc,t)
    in
        reverse'(nil, x)
    end;
reverse([1,2,3,4,5]);

(** 2.7  Abstract types **)
abstype Mixture = mix of int*int*int
    with val cement = mix(6,0,0)
         and sand   = mix(0,6,0)
         and gravel = mix(0,0,6)
         and mortar = mix(1,5,0)
         and infill = mix(1,2,3)
         fun compound( parts  : int, mix(c , s , g )
                     , parts' : int, mix(c', s', g') ) =
               let val p  = parts + parts'
                   val cp = (parts*c+parts'*c') div p
                   and sp = (parts*s+parts'*s') div p
                   and gp = (parts*g+parts'*g') div p
               in mix(cp,sp,gp) end
end;
cement;
gravel;
compound(2, cement, 2, compound(2, sand, 3, gravel));
val list_member = member;
fun list_remove(x,nil) = nil
  | list_remove(x,h::t) = if x=h then list_remove(x,t) else h::list_remove(x,t);
list_remove(3,[1,2,3,4,5,6]);
list_remove(2,[1,2,3,4,1,2,3,1,123,2]);
exception empty_set;
abstype 'a Set = set of 'a list
    with val emptyset = set([])
         fun is_empty(set(s)) = length(s)=0
         fun singleton(x) = set([x])
         fun union(set(s),set(t)) = set(append(s,t))
         fun member(x,set(l)) = list_member(x,l)
         fun remove(x,set(l)) = set(list_remove(x,l))
         fun singleton_split(set(nil)) = raise empty_set
           | singleton_split(set(x::s)) = (x,remove(x,set(s)))
         fun split(s) =
                let val (x,s') = singleton_split(s) in
                    (singleton(x),s') end
end;
emptyset;
is_empty(emptyset);
is_empty(singleton(5));
is_empty(union(emptyset,emptyset));
singleton_split(emptyset);
fun cardinality(s) = if is_empty(s) then 0 else
        let val (x,s') = singleton_split(s) in
                1 + cardinality(s') end;
cardinality(emptyset);
cardinality(singleton(5));
cardinality(union(singleton(5),singleton(6)));
cardinality(union(singleton(5),singleton(5)));

(** 2.8  Exceptions **)
(* exception empty_list: unit; *)
exception empty_list;
empty_list;
fun head(nil)  = raise empty_list
  | head(a::s) = a;
head(nil);
head([1,2,3]);
fun tail(nil)  = raise empty_list
  | tail(a::s) = s;
fun append(s,t) =
        head(s)::append(tail(s),t) handle empty_list => t;
append([1,2,3],[6,7,8]);
10 div 0;
exception div_by_zero of int;
div_by_zero;
fun divide(n,d) = if d=0
    then raise div_by_zero(n) else op div(n,d);
divide(10,0) handle div_by_zero(x) => x*x;

(** 2.9  Other facilities **)

(** 2.10  Exercise **)

(* Exercise 1. Values and environments *)
val x = 3; val y = 4 and z = x+1;
let val x = 3; val y = 4 and z = x+1 in (x,y,z) end;
let val x =1 and y =2 in x+y end;
let val q = let val x =1 and y =2 in x+y end in q end;
(* val p = 3 and q = p+1 *)
let val (x,y) = (2,3) in 2*x + y end;
let val x = 1 in let val y = x+2 in let val x = 5 in x+y end end end;
val (x,y as (_,p)) = ((2,3),(4,(5,6)));

(* Exercise 2. Defining functions *)
fun sign(x) = x > 0;
sign(5); sign(0); sign(~5);
fun absvalue(x) = if x < 0 then ~x else x;
absvalue(5); absvalue(0); absvalue(~5);
fun max(x,y) = if x > y then x else y;
max(2,7); max(7,2);
fun fib(1) = 1
  | fib(2) = 1
  | fib(n) = fib(n-1) + fib(n-2);
fib(1); fib(2); fib(3); fib(4); fib(5); fib(6); fib(7); fib(8);

(* Exercise 3. Natural numbers *)
datatype Num = zero | succ of Num;
fun numprint(zero)    = 0
  | numprint(succ(n)) = 1 + numprint(n);
numprint(zero); numprint(succ(zero)); numprint(succ(succ(succ(succ(zero)))));
fun add(zero, m)   = m
  | add(succ(n),m) = succ(add(n,m));
add(succ(succ(zero)),succ(succ(zero)));
fun mul(zero, m)   = zero
  | mul(succ(n),m) = add(m, mul(n,m));
fun inj(0) = zero
  | inj(n) = succ(inj(n-1));
inj(10);
numprint(mul(inj(10),inj(10)));

(* Exercise 4. Higher order and polymorphic functions *)
fun apply(f)(x) = f(x);
fun compose(g,f) = fn x => g(f(x));

(* Exercise 5. List processing *)
fun maximum([s]) = s
  | maximum(h::t) = max(h,maximum(t));
maximum([1,56,34,3,45,345,3,5,5,2]);
fun sum(nil) = 0
  | sum(h::t) = h + sum(t);
sum([1,2,3,4,5]);
fun poly(nil, x) = 0
  | poly(h::t,x) = h + poly(map (fn y => x * y) t,x);
poly([1,2,3],5);
1 + 2 * 5 + 3 * 5 * 5;
append([1,2,3],[4,5,6]);
fun reverse(nil) = nil
  | reverse(h::t) = append(reverse(t),[h]);
reverse [1,2,3,4];
fun maplist(f,nil)  = nil
  | maplist(f,h::t) = f(h) :: maplist(f,t);
maplist(fn x => x * x,[1,2,3,4,5]);
fun accumulate f e nil    = e
  | accumulate f e (h::t) = f(h,accumulate f e t);
fun sum(l) = accumulate (op +) 0 l;
sum([1,2,3,4,5]);

(* Exercise 6. Binary trees *)
datatype 'a BinTree =
    tip of 'a | node of ('a BinTree)*('a BinTree);
val tree = node(node(tip(1),tip(2)),tip(3));
fun breadth(tip(_))    = 1
  | breadth(node(l,r)) = breadth(l) + breadth(r);
breadth(tree);
fun depth(tip(_)) = 0
  | depth(node(l,r)) = 1 + max(depth(l),depth(r));
depth(tree);
fun collect(tip(n)) = [n]
  | collect(node(l,r)) = append(collect(l),collect(r));
collect(tree);

(* Exercise 7. Data abstraction *)(*
abstype Rational = rational of int * int
    with fun normalize(rational(n,d)) = rational(n,d) (* divide by gdc here *)
         fun construct(n,d) = normalize(rational(n,d))
         fun mul(rational(n1,d1),rational(n2,d2)) = rational(n1*n2,d1*d2)
         fun add(rational(n1,d1),rational(n2,d2)) = rational(n1*d2+n2*d1,d1*d2)
end;
construct(2,7);
add(construct(2,7),construct(3,7));

abstype Rational = repeating_fraction of int * int * int
    with 
*)

(* Exercise 8. More list processing *)
fun delete(x,nil) = nil
  | delete(x,a::s) = if x=a then delete(x,s) else a::delete(x,s);
delete(7,[2,4,5,7,8,5,5,6,7,8,8,3,3]);
(*
fun delete_nth(_,_,nil)  = nil
  | delete_nth(x,1,a::s) = if x=a then delete(x,0,s) else a::delete(x,1,s);
  | delete_nth(x,n,a::s) = if x=a then 
*)

fun sublist(nil,_) = true
  | sublist(_,nil) = false
  | sublist(a::s,b::t) = if a=b then sublist(s,t) else sublist(a::s,t);
sublist([3,6,7],[1,2,3,4,5,6,7,8,9]);
sublist([3,7,6],[1,2,3,4,5,6,7,8,9]);
sublist([1,2,3],[]);
fun number_of_sublists(nil,_)     = 1
  | number_of_sublists(_,nil)     = 0
  | number_of_sublists(a::s,b::t) =
        if a=b then number_of_sublists(s,t) + number_of_sublists(a::s,t)
               else                           number_of_sublists(a::s,t);
number_of_sublists([1,2],[1,2,2]);
number_of_sublists([1,2],[1,1,2,2]);
number_of_sublists([1,1],[1,1,1]);
number_of_sublists([1,1],[1]);

(* Exercise 9. Operations on finite sets *)
(*
abstype 'a Set = set of 'a list
    with val emptyset = set([])
         fun is_empty(set(s)) = length(s)=0
         fun singleton(x) = set([x])
         fun union(set(s),set(t)) = set(append(s,t))
         fun member(x,set(l)) = list_member(x,l)
         fun remove(x,set(l)) = set(list_remove(x,l))
         fun singleton_split(set(nil)) = raise empty_set
           | singleton_split(set(x::s)) = (x,remove(x,set(s)))
         fun split(s) =
                let val (x,s') = singleton_split(s) in
                    (singleton(x),s') end
         fun cartesian_product(set(nil), _) = emptyset
           | cartesian_product(_, set(nil)) = emptyset
           | cartesian_product(x as set(a::s), y as set(b::t)) =
                union(set((a,b)),union(cartesian_product(x, set(t)), cartesian_product(set(s), y)))
end;
*)

(* Exercise 10. Sorting *)
datatype BTree = empty | tip of int | node of BTree*int*BTree;
fun insert(x,empty)       = tip(x)
  | insert(x,tip(y))      = if x < y then node(tip(x),y,empty)
                                else node(empty,y,tip(x))
  | insert(x,node(s,n,t)) = if x < n then node(insert(x,s),n,t)
                                     else node(s,n,insert(x,t));
insert;
fun flatten(empty) = nil
  | flatten(tip(x)) = [x]
  | flatten(node(s,n,t)) = append(flatten(s),n::flatten(t));
fun sort(s) = flatten(accumulate(insert)(empty)(s));
sort([6,4,6,2,7,8,4,4,456,45,645,45,6,345,345,6,43]);

(* Exercise 11. Universal algebra and recursion *)
type 'b monoid = ('b -> 'b -> 'b) * 'b;
    (* See Haskell version *)

(*** Chapter 3: Categories and Functors ***)

(** 3.1  Categories **)

(* 3.1.1  Diagram chasing *)
(* 3.1.2  Subcategorties, isomorphisms, monics and epis *)

(** 3.2  Examples **)

(* 3.2.1  Sets and finite sets *)
(* 3.2.2  Graphs *)
(* 3.2.3  Finite categories *)
(* 3.2.4  Relations and partial orders *)
(* 3.2.5  Partial orders as categories *)
(* 3.2.6  Deductive systems *)
(* 3.2.7  Universal algebra: terms, algebras and equations *)
(* 3.2.8  Sets with structure-preserving arrows *)

(** 3.3  Categories computationally **)

datatype ('o,'a)Cat =
    cat of ('a->'o)*('a->'o)*('o->'a)*('a*'a->'a)
    
(** 3.4  Categories as values **)

exception non_composable_pair

(* 3.4.1  The category of finite sets *)

exception not_implemented
fun seteq(a,b) = raise not_implemented     (* FIXME: implement *)

datatype 'a Set_Arrow =
    set_arrow of ('a Set)*('a->'a)*('a Set)
   
fun set_s(set_arrow(a,_,_)) = a
fun set_t(set_arrow(_,_,b)) = b
fun set_ident(a) = set_arrow(a,fn x => x,a)
fun set_comp(set_arrow(c,g,d),set_arrow(a,f,b)) =
    if seteq(b,c) then set_arrow(a,fn x => g(f(x)),d)
                  else raise non_composable_pair

val FinSet = cat(set_s,set_t,set_ident,set_comp)

(* 3.4.2  Terms and term substitutions: the category T_Omega^Fin *)

type symbol = string
type element = string

datatype opr = opr of symbol * (element Set)

datatype Term = var of element
              | apply of opr * (element -> Term)

datatype Substitution =
    subst of (element Set)*(element -> Term)*(element Set)

fun subst_apply(t)(S as subst(a,f,b)) =
    case t of var(x)       => f(x)
            | apply(psi,s) => apply(psi,fn x => subst_apply(s x)(S))

fun subst_compose(S as subst(c,g,d),subst(a,f,b)) = 
    if seteq(b,c)
        then subst(a,fn x => subst_apply(f x)(S),d)
        else raise non_composable_pair

fun subst_ident(a) = subst(a,fn x => var(x),a)
fun subst_s(subst(a,_,_)) = a
fun subst_t(subst(_,_,b)) = b

val FinKleisli =
    cat(subst_s,subst_t,subst_ident,subst_compose)

(* 3.4.3  A finite category *)



