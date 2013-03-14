Module TAL0.

Require Import ZArith.

(* Figure 4-1: Instructions and operands for TAL-0 *)

Inductive r := r1 | r2 | r3 | r4 | r5 | r6 | r7 | r8 | r9.

Inductive l := l1 | l2 | l3 | l4 | l5 | l6 | l7 | l8 | l9.

Inductive v :=
| int : Z -> v
| lab : l -> v
| reg : r -> v.

Inductive i :=
| mov : r -> v -> i
| add : r -> r -> v -> i
| if_jump : r -> v -> i.

Inductive I :=
| jump : v -> I
| seq : i -> I -> I.

(* Figure 4-2: TAL-0 abstract machine syntax *)

Record R :=
  { r1_ : v;
    r2_ : v;
    r3_ : v;
    r4_ : v;
    r5_ : v;
    r6_ : v;
    r7_ : v;
    r8_ : v;
    r9_ : v
  }.

Definition h := I.

Record H :=
  { l1_ : h;
    l2_ : h;
    l3_ : h;
    l4_ : h;
    l5_ : h;
    l6_ : h;
    l7_ : h;
    l8_ : h;
    l9_ : h
  }.

Definition M := (H, R, I).

(* Figure 4-3: TAL-0 type syntax *)

Inductive Ty :=
| Int : Ty
| Code : RegFileTy -> Ty
| Var : Z -> Ty
| Forall : Z -> Ty -> Ty
with
Record RegFileTy :=
  { R1 : Ty;
    R2 : Ty;
    R3 : Ty;
    R4 : Ty;
    R5 : Ty;
    R6 : Ty;
    R7 : Ty;
    R8 : Ty;
    R9 : Ty
  }.
