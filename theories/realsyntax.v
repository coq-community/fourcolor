(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From fourcolor Require Import real.

(******************************************************************************)
(*   This files defines Notation for the abstract reals laid out in real.v.   *)
(* Notations are defined in the %Rval scope, bound to Real.val R, and include *)
(*   0, 1, x + y, - x, x - y, x * y : the usual arithmetic operation notation *)
(*     x^-1, x / y == inverse and division, using Real.extended_inverse.      *)
(*            n%:R == 1 + ... + 1 (n times), using Real.nat.                  *)
(*               2 == 1 + 1.                                                  *)
(*          x == y <-> x and y represent the same real. This uses Real.eq,    *)
(*                     so is NOT the same as x = y.                           *)
(*          x != y <-> x and y do not represent the same real.                *)
(* --> Note that the syntax for equality tests defined in Eqtype.Equality     *)
(* will take precedence in bool contexts even if %Rval is opened.             *)
(*   x <= y, x < y, x >= y, x > y, x <= y < z, etc : usual comparison syntax  *)
(*         x == y == z <-> x == y and y === z                                 *)
(* --> x == y, x <= y, etc, are all defined in the %Rval scope, so in a bool  *)
(* context the eqtype.v and ssrnat.v or ssrnum.v definitions will have        *)
(* precedence.                                                                *)
(*  IF P then x else y == x if P holds, else y if ~ P holds.                  *)
(* --> the Coq pervasives IF will still have precedence in %type scope.       *)
(*  sup {x | P} == the sup of the set of x such that P holds (x should appear *)
(*                 in P), or 0 if this set if empty or unbounded.             *)
(* --> sup is actually an alias for Real.extended_sup, and the {x | P} is     *)
(* just notation for (fun x => P) in the %Rset scope, bound to Real.set.      *)
(* --> This files also assigns %Rval and %Rset scopes to all the Real         *)
(* operations and predicates, so the {x | P} notation can be used in Real.ub, *)
(* Real.has_ub, etc.                                                          *)
(* --> We also Export RealCoercions, so any R : Real.model can be used as a   *)
(* Type.                                                                      *)
(******************************************************************************)

Import Real.
Export RealCoercions.

Bind Scope real_scope with val.
Bind Scope realset_scope with set.
Delimit Scope real_scope with Rval.
Delimit Scope realset_scope with Rset.
Local Open Scope real_scope.

Arguments val R : rename, simpl never.
Arguments set R : rename, simpl never.
Arguments rel R : rename, simpl never.
Arguments le {R} x%Rval y%Rval : rename, simpl never.
Arguments sup {R} E%Rset : rename, simpl never.
Arguments add {R} x%Rval y%Rval : rename, simpl never.
Arguments opp {R} x%Rval : rename, simpl never.
Arguments mul {R} x%Rval y%Rval : rename, simpl never.
Arguments inv {R} x%Rval : rename, simpl never.
Arguments eq {R} x%Rval y%Rval.
Arguments ub {R} E%Rset x%Rval.
Arguments down {R} E%Rset x%Rval.
Arguments nonempty {R} E%Rset.
Arguments has_ub {R} E%Rset.
Arguments has_sup {R} E%Rset.
Arguments image {R S} phi E%Rset y%Rval.
Arguments nat R n%nat: simpl never.
Arguments select_set {R} P%type x%Rval y%Rval _%Rval.
Arguments select {R} P%type x%Rval y%Rval.
Arguments extended_inv {R} x%Rval.
Arguments extended_sup {R} E%Rset.

Reserved Notation "n %:R" (at level 2, left associativity, format "n %:R").
Reserved Notation "x ^-1" (at level 3, left associativity, format "x ^-1").

Reserved Notation "x == y" (at level 70, no associativity).
Reserved Notation "x != y" (at level 70, no associativity).
Reserved Notation "x == y == z"
  (at level 70, no associativity, y at next level).

Notation "x <= y" := (le x y) : real_scope.
Notation "x + y" := (add x y) : real_scope.
Notation "0" := (zero _) : real_scope.
Notation "- y" := (opp y) : real_scope.
Notation "x * y" := (mul x y) : real_scope.
Notation "1" := (one _) : real_scope.

Notation "x - y" := (x + (- y)) : real_scope.
Notation "x ^-1" := (extended_inv x) : real_scope.
Notation "x / y" := (x * y^-1) : real_scope.
Notation "2" := (1 + 1) : real_scope.
Notation "- 1" := (- (1)) : real_scope.
Notation "- 2" := (- (2)) : real_scope.
Notation "n %:R" := (nat _ n) : real_scope.

Notation "x == y" := (eq x y) : real_scope.
Notation "x != y" := (~ (x == y)) : real_scope.
Notation "x >= y" := (y <= x) (only parsing) : real_scope.
Notation "x < y" := (~ (x >= y)) : real_scope.
Notation "x > y" := (y < x) (only parsing) : real_scope.
Notation "x == y == z" := (x == y /\ y == z) : real_scope.
Notation "x <= y <= z" := (x <= y /\ y <= z) : real_scope.
Notation "x < y <= z" := (x < y /\ y <= z) : real_scope.
Notation "x <= y < z" := (x <= y /\ y < z) : real_scope.
Notation "x < y < z" := (x < y /\ y < z) : real_scope.

Notation "{ x | P }" := (fun x : val _ => P : Prop) : realset_scope.
Notation "'IF' P 'then' x 'else' y" := (select P x y) : real_scope.
Notation sup := extended_sup.

