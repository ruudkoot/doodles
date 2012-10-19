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


