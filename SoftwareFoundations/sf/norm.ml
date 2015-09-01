type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val beq_nat : int -> int -> bool **)

let rec beq_nat = ( = )

type id =
  int
  (* singleton inductive, whose constructor was Id *)

(** val beq_id : id -> id -> bool **)

let beq_id id1 id2 =
  beq_nat id1 id2

type 'a partial_map = id -> 'a option

(** val empty : 'a1 partial_map **)

let empty x =
  None

(** val extend : 'a1 partial_map -> id -> 'a1 -> id -> 'a1 option **)

let extend gamma x t x' =
  if beq_id x x' then Some t else gamma x'

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

(** val subst : id -> tm -> tm -> tm **)

let rec subst x s t = match t with
| Tvar y -> if beq_id x y then s else t
| Tapp (t1, t2) -> Tapp ((subst x s t1), (subst x s t2))
| Tabs (y, t0, t1) -> Tabs (y, t0, (if beq_id x y then t1 else subst x s t1))
| Tif (t0, t1, t2) -> Tif ((subst x s t0), (subst x s t1), (subst x s t2))
| x0 -> x0

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

(** val context_invariance :
    context -> (id -> ty option) -> tm -> ty -> has_type -> has_type **)

let rec context_invariance gamma gamma' t s = function
| T_Var (gamma0, x, t0) -> T_Var (gamma', x, t0)
| T_Abs (gamma0, x, t11, t12, t13, h0) ->
  T_Abs (gamma', x, t11, t12, t13,
    (context_invariance (extend gamma0 x t11) (extend gamma' x t11) t13 t12
      h0))
| T_App (t1, t2, gamma0, t3, t4, h0, h1) ->
  T_App (t1, t2, gamma', t3, t4,
    (context_invariance gamma0 gamma' t3 (TArrow (t1, t2)) h0),
    (context_invariance gamma0 gamma' t4 t1 h1))
| T_True gamma0 -> T_True gamma'
| T_False gamma0 -> T_False gamma'
| T_If (gamma0, t0, t1, t2, t3, h0, h1, h2) ->
  T_If (gamma', t0, t1, t2, t3,
    (context_invariance gamma0 gamma' t0 TBool h0),
    (context_invariance gamma0 gamma' t1 t3 h1),
    (context_invariance gamma0 gamma' t2 t3 h2))

(** val substitution_preserves_typing :
    ty partial_map -> id -> ty -> tm -> tm -> ty -> has_type -> has_type ->
    has_type **)

let rec substitution_preserves_typing gamma x u v t s htypt htypv =
  match t with
  | Tvar i ->
    (match htypt with
     | T_Var (gamma0, x0, t0) ->
       let e = beq_id x i in
       if e
       then context_invariance empty gamma v s htypv
       else T_Var (gamma, i, s)
     | _ -> assert false (* absurd case *))
  | Tapp (t0, t1) ->
    (match htypt with
     | T_App (t2, t3, gamma0, t4, t5, x0, x1) ->
       T_App (t2, s, gamma, (subst x v t0), (subst x v t1),
         (substitution_preserves_typing gamma x u v t0 (TArrow (t2, s)) x0
           htypv),
         (substitution_preserves_typing gamma x u v t1 t2 x1 htypv))
     | _ -> assert false (* absurd case *))
  | Tabs (i, t0, t1) ->
    (match htypt with
     | T_Abs (gamma0, x0, t11, t12, t13, x1) ->
       T_Abs (gamma, i, t0, t12, (if beq_id x i then t1 else subst x v t1),
         (let e = beq_id x i in
         if e
         then context_invariance (extend (extend gamma x u) i t0)
                (extend gamma i t0) t1 t12 x1
         else substitution_preserves_typing (extend gamma i t0) x u v t1 t12
                (context_invariance (extend (extend gamma x u) i t0)
                  (extend (extend gamma i t0) x u) t1 t12 x1) htypv))
     | _ -> assert false (* absurd case *))
  | Ttrue ->
    (match htypt with
     | T_True gamma0 -> T_True gamma
     | _ -> assert false (* absurd case *))
  | Tfalse ->
    (match htypt with
     | T_False gamma0 -> T_False gamma
     | _ -> assert false (* absurd case *))
  | Tif (t0, t1, t2) ->
    (match htypt with
     | T_If (gamma0, t3, t4, t5, t6, x0, x1, x2) ->
       T_If (gamma, (subst x v t0), (subst x v t1), (subst x v t2), s,
         (substitution_preserves_typing gamma x u v t0 TBool x0 htypv),
         (substitution_preserves_typing gamma x u v t1 s x1 htypv),
         (substitution_preserves_typing gamma x u v t2 s x2 htypv))
     | _ -> assert false (* absurd case *))

(** val preservation : tm -> tm -> ty -> has_type -> step -> has_type **)

let preservation t t' t0 hT hE =
  let rec f c t1 t2 h t'0 hE0 =
    match h with
    | T_App (t3, t4, gamma, t5, t6, h0, h1) ->
      (match hE0 with
       | ST_AppAbs (x, t11, t12, v2, h2) ->
         (match hE0 with
          | ST_AppAbs (x0, t7, t8, v3, h3) ->
            substitution_preserves_typing empty x t3 t6 t12 t4
              (match h0 with
               | T_Abs (gamma0, x1, t9, t13, t10, x2) -> x2
               | _ -> assert false (* absurd case *)) h1
          | ST_App1 (t7, t1', t8, h3) ->
            T_App (t3, t4, empty, t1', t6,
              (f gamma t5 (TArrow (t3, t4)) h0 t1' h3), h1)
          | ST_App2 (v1, t7, t2', h3, h4) ->
            T_App (t3, t4, empty, (Tabs (x, t11, t12)), t2', h0,
              (f gamma t6 t3 h1 t2' h4))
          | _ -> assert false (* absurd case *))
       | ST_App1 (t7, t1', t8, h2) ->
         T_App (t3, t4, empty, t1', t6,
           (f gamma t5 (TArrow (t3, t4)) h0 t1' h2), h1)
       | ST_App2 (v1, t7, t2', h2, h3) ->
         T_App (t3, t4, empty, t5, t2', h0, (f gamma t6 t3 h1 t2' h3))
       | _ -> assert false (* absurd case *))
    | T_If (gamma, t3, t4, t5, t6, h0, h1, h2) ->
      (match hE0 with
       | ST_IfTrue (t7, t8) -> h1
       | ST_IfFalse (t7, t8) -> h2
       | ST_If (t7, t0', t8, t9, h3) ->
         T_If (empty, t0', t4, t5, t6, (f gamma t3 TBool h0 t0' h3), h1, h2)
       | _ -> assert false (* absurd case *))
    | _ -> assert false (* absurd case *)
  in f empty t t0 hT t' hE

type halts = (tm, ((tm, step) multi, value) prod) ex

(** val value_halts : tm -> value -> halts **)

let value_halts v h =
  Ex_intro (v, (Pair ((Multi_refl v), h)))

type r = __

(** val r_halts : ty -> tm -> r -> halts **)

let r_halts t t0 x =
  match t with
  | TBool -> let Pair (x0, x1) = Obj.magic x in let Pair (x2, _) = x1 in x2
  | TArrow (t1, t2) ->
    let Pair (x0, x1) = Obj.magic x in let Pair (x2, x3) = x1 in x2

(** val r_typable_empty : ty -> tm -> r -> has_type **)

let r_typable_empty t t0 x =
  match t with
  | TBool -> let Pair (x0, x1) = Obj.magic x in x0
  | TArrow (t1, t2) -> let Pair (x0, x1) = Obj.magic x in x0

type ('p, 'q) iff = ('p -> 'q, 'q -> 'p) prod

(** val ex_falso_quodlibet : __ -> 'a1 **)

let ex_falso_quodlibet _ =
  assert false (* absurd case *)

(** val step_preserves_halting : tm -> tm -> step -> (halts, halts) iff **)

let step_preserves_halting t t' sT =
  Pair ((fun h ->
    let Ex_intro (t'', p) = h in
    let Pair (sTM, v) = p in
    (match sTM with
     | Multi_refl x -> ex_falso_quodlibet __
     | Multi_step (x, y, z, h0, h1) -> Ex_intro (t'', (Pair (h1, v))))),
    (fun h ->
    let Ex_intro (t'0, p) = h in
    let Pair (sTM, v) = p in
    Ex_intro (t'0, (Pair ((Multi_step (t, t', t'0, sT, sTM)), v)))))

(** val step_preserves_R : ty -> tm -> tm -> step -> r -> r **)

let rec step_preserves_R t t0 t' e rt =
  match t with
  | TBool ->
    let Pair (typable_empty_t, p) = Obj.magic rt in
    let Pair (halts_t, _) = p in
    Obj.magic (Pair ((preservation t0 t' TBool typable_empty_t e), (Pair
      ((let Pair (x, x0) = step_preserves_halting t0 t' e in x halts_t),
      __))))
  | TArrow (t1, t2) ->
    let Pair (typable_empty_t, p) = Obj.magic rt in
    let Pair (halts_t, rRt) = p in
    Obj.magic (Pair
      ((preservation t0 t' (TArrow (t1, t2)) typable_empty_t e), (Pair
      ((let Pair (x, x0) = step_preserves_halting t0 t' e in x halts_t),
      (fun s x ->
      step_preserves_R t2 (Tapp (t0, s)) (Tapp (t', s)) (ST_App1 (t0, t', s,
        e)) (rRt s x))))))

(** val multistep_preserves_R :
    ty -> tm -> tm -> (tm, step) multi -> r -> r **)

let rec multistep_preserves_R t t0 t' sTM x =
  match sTM with
  | Multi_refl x0 -> x
  | Multi_step (x0, y, z, y0, m) ->
    multistep_preserves_R t y z m (step_preserves_R t x0 y y0 x)

(** val step_preserves_R' : ty -> tm -> tm -> has_type -> step -> r -> r **)

let rec step_preserves_R' t t0 t' typable_empty_t e rt' =
  match t with
  | TBool ->
    let Pair (typable_empty_t', p) = Obj.magic rt' in
    let Pair (halts_t', _) = p in
    Obj.magic (Pair (typable_empty_t, (Pair
      ((let Pair (x, x0) = step_preserves_halting t0 t' e in x0 halts_t'),
      __))))
  | TArrow (t1, t2) ->
    let Pair (typable_empty_t', p) = Obj.magic rt' in
    let Pair (halts_t', rRt') = p in
    Obj.magic (Pair (typable_empty_t, (Pair
      ((let Pair (x, x0) = step_preserves_halting t0 t' e in x0 halts_t'),
      (fun s x ->
      step_preserves_R' t2 (Tapp (t0, s)) (Tapp (t', s)) (T_App (t1, t2,
        empty, t0, s, typable_empty_t, (r_typable_empty t1 s x))) (ST_App1
        (t0, t', s, e)) (rRt' s x))))))

(** val multistep_preserves_R' :
    ty -> tm -> tm -> has_type -> (tm, step) multi -> r -> r **)

let rec multistep_preserves_R' t t0 t' hT sTM x =
  match sTM with
  | Multi_refl x0 -> x
  | Multi_step (x0, y, z, y0, m) ->
    step_preserves_R' t x0 y hT y0
      (multistep_preserves_R' t y z (preservation x0 y t hT y0) m x)

type env = (id, tm) prod list

(** val msubst : env -> tm -> tm **)

let rec msubst ss t =
  match ss with
  | Nil -> t
  | Cons (p, ss') -> let Pair (x, s) = p in msubst ss' (subst x s t)

type tass = (id, ty) prod list

(** val mextend : context -> tass -> context **)

let rec mextend gamma = function
| Nil -> gamma
| Cons (p, xts') -> let Pair (x, v) = p in extend (mextend gamma xts') x v

(** val drop : id -> (id, 'a1) prod list -> (id, 'a1) prod list **)

let rec drop n = function
| Nil -> Nil
| Cons (p, nxs') ->
  let Pair (n', x) = p in
  if beq_id n' n then drop n nxs' else Cons ((Pair (n', x)), (drop n nxs'))

type instantiation =
| V_nil
| V_cons of id * ty * tm * tass * env * value * r * instantiation

(** val instantiation_R :
    tass -> env -> instantiation -> id -> tm -> ty -> r **)

let rec instantiation_R t e i x' t' t'0 =
  match i with
  | V_nil -> assert false (* absurd case *)
  | V_cons (x, t0, v, c, e0, v0, r0, i0) ->
    let b = beq_id x x' in
    if b then r0 else instantiation_R c e0 i0 x' t' t'0

(** val instantiation_drop :
    tass -> env -> instantiation -> id -> instantiation **)

let rec instantiation_drop t e i x =
  match i with
  | V_nil -> V_nil
  | V_cons (x0, t0, v, c, e0, v0, r0, i0) ->
    let b = beq_id x0 x in
    if b
    then instantiation_drop c e0 i0 x
    else V_cons (x0, t0, v,
           (let rec drop0 n = function
            | Nil -> Nil
            | Cons (p, nxs') ->
              let Pair (n', x1) = p in
              if beq_id n' n
              then drop0 n nxs'
              else Cons ((Pair (n', x1)), (drop0 n nxs'))
            in drop0 x c),
           (let rec drop0 n = function
            | Nil -> Nil
            | Cons (p, nxs') ->
              let Pair (n', x1) = p in
              if beq_id n' n
              then drop0 n nxs'
              else Cons ((Pair (n', x1)), (drop0 n nxs'))
            in drop0 x e0), v0, r0, (instantiation_drop c e0 i0 x))

(** val multistep_App2 :
    tm -> tm -> tm -> value -> (tm, step) multi -> (tm, step) multi **)

let rec multistep_App2 v t t' v0 = function
| Multi_refl x -> Multi_refl (Tapp (v, x))
| Multi_step (x, y, z, y0, m) ->
  Multi_step ((Tapp (v, x)), (Tapp (v, y)), (Tapp (v, z)), (ST_App2 (v, x, y,
    v0, y0)), (multistep_App2 v y z v0 m))

(** val multistep_If :
    tm -> tm -> tm -> tm -> (tm, step) multi -> (tm, step) multi **)

let rec multistep_If t1 t1' t2 t3 = function
| Multi_refl x -> Multi_refl (Tif (x, t2, t3))
| Multi_step (x, y, z, y0, m) ->
  Multi_step ((Tif (x, t2, t3)), (Tif (y, t2, t3)), (Tif (z, t2, t3)), (ST_If
    (x, y, t2, t3, y0)), (multistep_If y z t2 t3 m))

(** val msubst_preserves_typing :
    tass -> env -> instantiation -> context -> tm -> ty -> has_type ->
    has_type **)

let rec msubst_preserves_typing t e i gamma t0 s x =
  match i with
  | V_nil -> x
  | V_cons (x0, t1, v, c, e0, v0, r0, i0) ->
    msubst_preserves_typing c e0 i0 gamma (subst x0 v t0) s
      (substitution_preserves_typing (mextend gamma c) x0 t1 v t0 s x
        (r_typable_empty t1 v r0))

(** val multi_trans :
    'a1 -> 'a1 -> 'a1 -> ('a1, 'a2) multi -> ('a1, 'a2) multi -> ('a1, 'a2)
    multi **)

let rec multi_trans x y z g h =
  match g with
  | Multi_refl x0 -> h
  | Multi_step (x0, y0, z0, y1, m) ->
    Multi_step (x0, y0, z, y1, (multi_trans y0 z0 z m h))

(** val multi_R : 'a1 -> 'a1 -> 'a2 -> ('a1, 'a2) multi **)

let multi_R x y r0 =
  Multi_step (x, y, y, r0, (Multi_refl y))

(** val msubst_R :
    tass -> env -> tm -> ty -> has_type -> instantiation -> r **)

let msubst_R c env0 t t0 hT v =
  let gamma = mextend empty c in
  let rec f c0 t1 t2 h c1 env1 v0 =
    match h with
    | T_Var (gamma0, x, t3) ->
      instantiation_R c1 env1 v0 x (msubst env1 (Tvar x)) t3
    | T_Abs (gamma0, x, t11, t12, t13, h0) ->
      let wT = T_Abs (empty, x, t11, t12, (msubst (drop x env1) t13),
        (msubst_preserves_typing (drop x c1) (drop x env1)
          (instantiation_drop c1 env1 v0 x) (extend empty x t11) t13 t12
          (context_invariance (extend gamma0 x t11)
            (mextend (extend empty x t11) (drop x c1)) t13 t12 h0)))
      in
      Obj.magic (Pair (wT, (Pair
        ((value_halts (Tabs (x, t11, (msubst (drop x env1) t13))) (V_abs (x,
           t11, (msubst (drop x env1) t13)))), (fun s x0 ->
        let h1 = r_halts t11 s x0 in
        let Ex_intro (v1, p) = h1 in
        let Pair (p0, q) = p in
        let x1 = multistep_preserves_R t11 s v1 p0 x0 in
        multistep_preserves_R' t12 (Tapp ((Tabs (x, t11,
          (msubst (drop x env1) t13))), s))
          (msubst (Cons ((Pair (x, v1)), env1)) t13) (T_App (t11, t12, empty,
          (Tabs (x, t11, (msubst (drop x env1) t13))), s, wT,
          (r_typable_empty t11 s x0)))
          (multi_trans (Tapp ((Tabs (x, t11, (msubst (drop x env1) t13))),
            s)) (Tapp ((Tabs (x, t11, (msubst (drop x env1) t13))), v1))
            (msubst (Cons ((Pair (x, v1)), env1)) t13)
            (multistep_App2 (Tabs (x, t11, (msubst (drop x env1) t13))) s v1
              (V_abs (x, t11, (msubst (drop x env1) t13))) p0)
            (multi_R (Tapp ((Tabs (x, t11, (msubst (drop x env1) t13))), v1))
              (msubst (Cons ((Pair (x, v1)), env1)) t13) (ST_AppAbs (x, t11,
              (msubst (drop x env1) t13), v1, q))))
          (f (extend gamma0 x t11) t13 t12 h0 (Cons ((Pair (x, t11)), c1))
            (Cons ((Pair (x, v1)), env1)) (V_cons (x, t11, v1, c1, env1, q,
            x1, v0))))))))
    | T_App (t3, t4, gamma0, t5, t6, h0, h1) ->
      let r0 = f gamma0 t5 (TArrow (t3, t4)) h0 c1 env1 v0 in
      let Pair (h2, p) = Obj.magic r0 in
      let Pair (h3, p1) = p in
      let p2 = f gamma0 t6 t3 h1 c1 env1 v0 in p1 (msubst env1 t6) p2
    | T_True gamma0 ->
      Obj.magic (Pair ((T_True empty), (Pair ((Ex_intro (Ttrue, (Pair
        ((Multi_refl Ttrue), V_true)))), __))))
    | T_False gamma0 ->
      Obj.magic (Pair ((T_False empty), (Pair ((Ex_intro (Tfalse, (Pair
        ((Multi_refl Tfalse), V_false)))), __))))
    | T_If (gamma0, t3, t4, t5, t6, h0, h1, h2) ->
      let wT = T_If (empty, (msubst env1 t3), (msubst env1 t4),
        (msubst env1 t5), t6,
        (msubst_preserves_typing c1 env1 v0 empty t3 TBool
          (context_invariance gamma0 (mextend empty c1) t3 TBool h0)),
        (msubst_preserves_typing c1 env1 v0 empty t4 t6
          (context_invariance gamma0 (mextend empty c1) t4 t6 h1)),
        (msubst_preserves_typing c1 env1 v0 empty t5 t6
          (context_invariance gamma0 (mextend empty c1) t5 t6 h2)))
      in
      let iH1 = f gamma0 t3 TBool h0 c1 env1 v0 in
      let h3 = r_halts TBool (msubst env1 t3) iH1 in
      let Ex_intro (v1, p) = h3 in
      let Pair (p0, q) = p in
      let x = multistep_preserves_R TBool (msubst env1 t3) v1 p0 iH1 in
      let x0 = r_typable_empty TBool v1 x in
      (match q with
       | V_abs (x1, t11, t12) -> assert false (* absurd case *)
       | V_true ->
         (match x0 with
          | T_True gamma1 ->
            multistep_preserves_R' t6 (Tif ((msubst env1 t3),
              (msubst env1 t4), (msubst env1 t5))) (msubst env1 t4) wT
              (multi_trans (Tif ((msubst env1 t3), (msubst env1 t4),
                (msubst env1 t5))) (Tif (Ttrue, (msubst env1 t4),
                (msubst env1 t5))) (msubst env1 t4)
                (multistep_If (msubst env1 t3) Ttrue (msubst env1 t4)
                  (msubst env1 t5) p0)
                (multi_R (Tif (Ttrue, (msubst env1 t4), (msubst env1 t5)))
                  (msubst env1 t4) (ST_IfTrue ((msubst env1 t4),
                  (msubst env1 t5))))) (f gamma0 t4 t6 h1 c1 env1 v0)
          | _ -> assert false (* absurd case *))
       | V_false ->
         multistep_preserves_R' t6 (Tif ((msubst env1 t3), (msubst env1 t4),
           (msubst env1 t5))) (msubst env1 t5) wT
           (multi_trans (Tif ((msubst env1 t3), (msubst env1 t4),
             (msubst env1 t5))) (Tif (Tfalse, (msubst env1 t4),
             (msubst env1 t5))) (msubst env1 t5)
             (multistep_If (msubst env1 t3) Tfalse (msubst env1 t4)
               (msubst env1 t5) p0)
             (multi_R (Tif (Tfalse, (msubst env1 t4), (msubst env1 t5)))
               (msubst env1 t5) (ST_IfFalse ((msubst env1 t4),
               (msubst env1 t5))))) (f gamma0 t5 t6 h2 c1 env1 v0))
  in f gamma t t0 hT c env0 v

(** val normalization : tm -> ty -> has_type -> halts **)

let normalization t t0 x =
  r_halts t0 (msubst Nil t) (msubst_R Nil Nil t t0 x V_nil)

(** val beq_ty : ty -> ty -> bool **)

let rec beq_ty t1 t2 =
  match t1 with
  | TBool ->
    (match t2 with
     | TBool -> true
     | TArrow (t, t0) -> false)
  | TArrow (t11, t12) ->
    (match t2 with
     | TBool -> false
     | TArrow (t21, t22) -> if beq_ty t11 t21 then beq_ty t12 t22 else false)

(** val type_check : context -> tm -> ty option **)

let rec type_check gamma = function
| Tvar x -> gamma x
| Tapp (t1, t2) ->
  (match type_check gamma t1 with
   | Some t0 ->
     (match t0 with
      | TBool -> None
      | TArrow (t11, t12) ->
        (match type_check gamma t2 with
         | Some t3 -> if beq_ty t11 t3 then Some t12 else None
         | None -> None))
   | None -> None)
| Tabs (x, t11, t12) ->
  (match type_check (extend gamma x t11) t12 with
   | Some t13 -> Some (TArrow (t11, t13))
   | None -> None)
| Tif (x, t0, f) ->
  (match type_check gamma x with
   | Some t1 ->
     (match t1 with
      | TBool ->
        (match type_check gamma t0 with
         | Some t2 ->
           (match type_check gamma f with
            | Some t3 -> if beq_ty t2 t3 then Some t2 else None
            | None -> None)
         | None -> None)
      | TArrow (t2, t3) -> None)
   | None -> None)
| _ -> Some TBool

(** val type_checking_sound : context -> tm -> ty -> has_type **)

let rec type_checking_sound gamma t t0 =
  match t with
  | Tvar i -> T_Var (gamma, i, t0)
  | Tapp (t1, t2) ->
    let tO1 = type_check gamma t1 in
    let tO2 = type_check gamma t2 in
    (match tO1 with
     | Some t3 ->
       (match t3 with
        | TBool -> assert false (* absurd case *)
        | TArrow (t11, t12) ->
          (match tO2 with
           | Some t4 ->
             let b = beq_ty t11 t4 in
             if b
             then T_App (t4, t0, gamma, t1, t2,
                    (type_checking_sound gamma t1 (TArrow (t4, t0))),
                    (type_checking_sound gamma t2 t4))
             else assert false (* absurd case *)
           | None -> assert false (* absurd case *)))
     | None -> assert false (* absurd case *))
  | Tabs (i, t1, t2) ->
    let g' = extend gamma i t1 in
    let tO2 = type_check g' t2 in
    (match tO2 with
     | Some t3 ->
       T_Abs (gamma, i, t1, t3, t2,
         (type_checking_sound (extend gamma i t1) t2 t3))
     | None -> assert false (* absurd case *))
  | Ttrue -> T_True gamma
  | Tfalse -> T_False gamma
  | Tif (t1, t2, t3) ->
    let tOc = type_check gamma t1 in
    let tO1 = type_check gamma t2 in
    let tO2 = type_check gamma t3 in
    (match tOc with
     | Some tc ->
       (match tc with
        | TBool ->
          (match tO1 with
           | Some t4 ->
             (match tO2 with
              | Some t5 ->
                let b = beq_ty t4 t5 in
                if b
                then T_If (gamma, t1, t2, t3, t0,
                       (type_checking_sound gamma t1 TBool),
                       (type_checking_sound gamma t2 t0),
                       (type_checking_sound gamma t3 t0))
                else assert false (* absurd case *)
              | None -> assert false (* absurd case *))
           | None -> assert false (* absurd case *))
        | TArrow (tc1, tc2) -> assert false (* absurd case *))
     | None -> assert false (* absurd case *))

