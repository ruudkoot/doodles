type __ = Obj.t

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

type 'a list =
| Nil
| Cons of 'a * 'a list

val beq_nat : int -> int -> bool

type id =
  int
  (* singleton inductive, whose constructor was Id *)

val beq_id : id -> id -> bool

type 'a partial_map = id -> 'a option

val empty : 'a1 partial_map

val extend : 'a1 partial_map -> id -> 'a1 -> id -> 'a1 option

type ty =
| TBool
| TArrow of ty * ty

type tm =
| Tvar of id
| Tapp of tm * tm
| Tabs of id * ty * tm
| Ttrue
| Tfalse
| Tif of tm * tm * tm

val subst : id -> tm -> tm -> tm

type value =
| V_abs of id * ty * tm
| V_true
| V_false

type step =
| ST_AppAbs of id * ty * tm * tm * value
| ST_App1 of tm * tm * tm * step
| ST_App2 of tm * tm * tm * value * step
| ST_IfTrue of tm * tm
| ST_IfFalse of tm * tm
| ST_If of tm * tm * tm * tm * step

type ('x, 'r) multi =
| Multi_refl of 'x
| Multi_step of 'x * 'x * 'x * 'r * ('x, 'r) multi

type ('x, 'p) ex =
| Ex_intro of 'x * 'p

type context = ty partial_map

type has_type =
| T_Var of (id -> ty option) * id * ty
| T_Abs of ty partial_map * id * ty * ty * tm * has_type
| T_App of ty * ty * context * tm * tm * has_type * has_type
| T_True of context
| T_False of context
| T_If of context * tm * tm * tm * ty * has_type * has_type * has_type

val context_invariance :
  context -> (id -> ty option) -> tm -> ty -> has_type -> has_type

val substitution_preserves_typing :
  ty partial_map -> id -> ty -> tm -> tm -> ty -> has_type -> has_type ->
  has_type

val preservation : tm -> tm -> ty -> has_type -> step -> has_type

type halts = (tm, ((tm, step) multi, value) prod) ex

val value_halts : tm -> value -> halts

type r = __

val r_halts : ty -> tm -> r -> halts

val r_typable_empty : ty -> tm -> r -> has_type

type ('p, 'q) iff = ('p -> 'q, 'q -> 'p) prod

val ex_falso_quodlibet : __ -> 'a1

val step_preserves_halting : tm -> tm -> step -> (halts, halts) iff

val step_preserves_R : ty -> tm -> tm -> step -> r -> r

val multistep_preserves_R : ty -> tm -> tm -> (tm, step) multi -> r -> r

val step_preserves_R' : ty -> tm -> tm -> has_type -> step -> r -> r

val multistep_preserves_R' :
  ty -> tm -> tm -> has_type -> (tm, step) multi -> r -> r

type env = (id, tm) prod list

val msubst : env -> tm -> tm

type tass = (id, ty) prod list

val mextend : context -> tass -> context

val drop : id -> (id, 'a1) prod list -> (id, 'a1) prod list

type instantiation =
| V_nil
| V_cons of id * ty * tm * tass * env * value * r * instantiation

val instantiation_R : tass -> env -> instantiation -> id -> tm -> ty -> r

val instantiation_drop : tass -> env -> instantiation -> id -> instantiation

val multistep_App2 :
  tm -> tm -> tm -> value -> (tm, step) multi -> (tm, step) multi

val multistep_If :
  tm -> tm -> tm -> tm -> (tm, step) multi -> (tm, step) multi

val msubst_preserves_typing :
  tass -> env -> instantiation -> context -> tm -> ty -> has_type -> has_type

val multi_trans :
  'a1 -> 'a1 -> 'a1 -> ('a1, 'a2) multi -> ('a1, 'a2) multi -> ('a1, 'a2)
  multi

val multi_R : 'a1 -> 'a1 -> 'a2 -> ('a1, 'a2) multi

val msubst_R : tass -> env -> tm -> ty -> has_type -> instantiation -> r

val normalization : tm -> ty -> has_type -> halts

val beq_ty : ty -> ty -> bool

val type_check : context -> tm -> ty option

val type_checking_sound : context -> tm -> ty -> has_type

