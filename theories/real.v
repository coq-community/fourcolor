(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)

(******************************************************************************)
(*   This file defines an abstract interface for real numbers; for            *)
(* convenience it also defines:                                               *)
(*   excluded_middle <-> the excluded middle property of classical logic      *)
(*                      holds for intensional disjunction.                    *)
(*                   := forall P : Prop, P \/ ~ P.                            *)
(* All other definitions are packaged in a Real submodule:                    *)
(*    Real.structure == record type comprising a representation type Real.val *)
(*                      together with the operations of a complete ordered    *)
(*                      field: Real.le, Real.sup, Real.add, Real.zero,        *)
(*                      Real.opp, Real.mul, Real.one, and Real.inv.           *)
(* --> Infix syntax for most of these operations will be provided in the      *)
(* realsyntax.v file (except for Real.sup and Real.inv -- see the entries for *)
(* Real.extended_sup and Real.extended_inv below).                            *)
(*     Real.axioms R <-> the Real.structure R satisfies the axioms for a      *)
(*                      complete ordered field axioms formulated for a        *)
(*                      constructive setting.                                 *)
(* --> These axioms imply excluded_middle, through a careful formulation of   *)
(* the Real.sup_total axiom, which states the minimality of the supremum      *)
(* using a constructive disjunction that lets us compare Real.sup E with any  *)
(* potential upper bound.                                                     *)
(*        Real.model == record packing a Real.structure with its axioms.      *)
(* --> Import RealCoercions activates coercions from models to axioms,        *)
(* structures, and their representation types.                                *)
(*  Real.morphism phi <-> the function phi : Real.val R -> Real.val S is a    *)
(*                      (continuous) (mono)morphism from R to S.              *)
(*  The signature of the Real operations use two derived fields:              *)
(*        Real.set R == the type of sets (Prop predicates) on Real.val R.     *)
(* --> Thus when we write "x is in E" below, with E : Real.set R, we really   *)
(* mean "x satisfies E", i.e., "E x holds".                                   *)
(*        Real.rel R == the type of Prop relations on Real.val R.             *)
(* The formulation of Real.axioms and Real.morphism uses some auxiliary       *)
(* definitions, which all assume some R : Real.structure :                    *)
(*       Real.eq x y <-> x and y : Real.val R represent the same value.       *)
(*                   := Real.le x y /\ Real.le y x.                           *)
(* --> Because the core logic of Coq does not support quotient types, axioms  *)
(* state algebraic equations using Real.eq rather that with Coq's intensional *)
(* equality 'eq'. Thus, our models are so-called setoid models, in which the  *)
(* Real.val R is really a type of denotations of real numbers, with each real *)
(* number having possibly several denotations. Even though operations are     *)
(* defined on denotations (or sets of denotations for the supremum sup), the  *)
(* monotonicity axioms imply that they must extensional - return equal        *)
(* results for equal denotations, or sets thereof.                            *)
(*   Real.nonempty E <-> at least one x : Real.val R is in E : Real.set R.    *)
(*          Real.ub E == the Real.set of upper bounds of E : Real.set R.      *)
(*      Real.has_ub E <-> E : Real.set R is bounded (has some upper bound).   *)
(*     Real.has_sup E <-> E : Real.set R is nonempty and bounded.             *)
(*        Real.down E == the downward closure of E : Real.set R, i.e.,        *)
(*                      down E x <-> le x y for some y such that E y.         *)
(*   Real.image phi E == image in a Real.structure S of E : Real.set R under  *)
(*                      phi : Real.val R -> Real.val S.                       *)
(* We also provide additional auxiliary definitions:                          *)
(*       Real.lt x y <-> x is less than y; simply Notation for ~ Real.le y x. *)
(*       Real.nat R n == a Real.val R whose value is n : nat; more precisely, *)
(*                      Real.zero R if n = 0, or else, if n > 0,              *)
(*                      Real.add (... (Real.add 1 1) ...) 1,                  *)
(*                      where 1 == Real.one R occurs n times.                 *)
(*  Real.select_set P x y == a Real.set R that contains only x if P : Prop    *)
(*                      holds, and only y otherwise, if ~ P holds.            *)
(*  Real.select P x y == a Real.val R that represents the same value as x if  *)
(*                      P : Prop holds, and the same as y otherwise.          *)
(*  Real.extended_inv x == Real.inv x, but 0 == Real.zero R if Real.eq x 0.   *)
(*  Real.extended_sup E == Real.sup E, if Real.has_sup E, else Real.zero R;   *)
(*    This file is the first part of the basis for stating the final form of  *)
(* the Four Color Theorem, which asserts a topogical property of the real     *)
(* plane. As such, this file has no prerequisites besides Coq pervasives and  *)
(* avoids using any of the implicit syntax enhancement features of Coq -      *)
(* notation, implicit types, coercions, type classes or canonical structures. *)
(* We also name all the axioms in property records.                           *)
(*   Only the structure, axioms and model record definitions, and the eq and  *)
(* relations, are used in the statement of the Four Color Theorem. The other  *)
(* 'further' definitions above are included here to keep them packaged under  *)
(* the 'Real' namespace, and because they are supported by the Notation       *)
(* defined in realsyntax.v. The Real.morphism property is used to state the   *)
(* categorical uniqueness of real models in file realcategorical.v. Along     *)
(* with the construction in file dedekind.v of a real model assuming only     *)
(* excluded_middle, this justifies making Real.model a parameter of the       *)
(* four_color theorem.                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition excluded_middle := forall P : Prop, P \/ ~ P.

Module Real.

Record structure : Type := Structure {
   val : Type;                (* type of real (denotation) values *)
   set := val -> Prop;        (* type of real (denotation) sets *)
   rel := val -> set;         (* type of real (denotation) relations *)
   le : rel;                  (* real order (less than or equal) relation *)
   sup : set -> val;          (* supremum of (nonempty, bounded) real sets *)
   add : val -> val -> val;   (* addition of real values *)
   zero : val;                (* real zero *)
   opp : val -> val;          (* opposite of a real value *)
   mul : val -> val -> val;   (* multiplication of real values *)
   one : val;                 (* real one *)
   inv : val -> val           (* inverse of a (nonzero) real value *)
}.

(* Below R and R' are always real structures, but the declaration             *)
(* Implicit Type R : structure.                                               *)
(* is not needed, thanks to type inference.                                   *)

(* A few basic derived operations and relations, used in the real axioms. *)

(* Equality is the preorder equivalence. *)
Definition eq R : rel R := fun x y => le x y /\ le y x.

(* Set of upper bounds of a real set. *)
Definition ub R (E : set R) : set R := fun z => forall y, E y -> le y z.

(* Real set downward (order) closure. *)
Definition down R (E : set R) : set R := fun x => exists2 y, E y & le x y.

(* Real set supremum existence condition. *)
Definition nonempty R (E : set R) : Prop := exists x, E x.
Definition has_ub R (E : set R) : Prop := nonempty (ub E).
Definition has_sup R (E : set R) : Prop := nonempty E /\ has_ub E.

(****************************************************************************)
(*   This presentation of the reals is intrinsically classical; the axioms  *)
(* below imply the excluded middle (the least upper bound totality axiom is *)
(* somewhat contrived in order to achieve this). The supremum axioms also   *)
(* imply that the ordering is total.                                        *)
(*   Conversely, the usual Dedekind cut construction produces a real model, *)
(* assuming only the excluded middle; in that case we make the assumption   *)
(* explicit, using the definition below.                                    *)
(*   To summarize, we have                                                  *)
(*     Theorem Dedekind.real : excluded_middle -> Real.model.               *)
(*     Lemma reals_classic : Real.model -> excluded_middle.                 *)
(****************************************************************************)
Record axioms R : Prop := Axioms {
  le_reflexive (x : val R) :
    le x x;
  le_transitive (x y z : val R) :
    le x y -> le y z -> le x z;
  sup_upper_bound (E : set R) :
    has_sup E -> ub E (sup E);
  sup_total (E : set R) (x : val R) :
    has_sup E -> down E x \/ le (sup E) x;
  add_monotone (x y z : val R) :
    le y z -> le (add x y) (add x z);
  add_commutative (x y : val R) :
    eq (add x y) (add y x);
  add_associative (x y z : val R) :
    eq (add x (add y z)) (add (add x y) z);
  add_zero_left (x : val R) :
    eq (add (zero R) x) x;
  add_opposite_right (x : val R) :
    eq (add x (opp x)) (zero R);
  mul_monotone x y z :
    le (zero R) x -> le y z -> le (mul x y) (mul x z);
  mul_commutative (x y : val R) :
    eq (mul x y) (mul y x);
  mul_associative (x y z : val R) :
    eq (mul x (mul y z)) (mul (mul x y) z);
  mul_distributive_right (x y z : val R) :
    eq (mul x (add y z)) (add (mul x y) (mul x z));
  mul_one_left (x : val R) :
    eq (mul (one R) x) x;
  mul_inverse_right (x : val R) :
    ~ eq x (zero R) -> eq (mul x (inv x)) (one R);
  one_nonzero : ~ eq (one R) (zero R)
}.

Record model : Type := Model {
  model_structure : structure;
  model_axioms : axioms model_structure
}.

(* Real set image. *)
Definition image R S (phi : val R -> val S) (E : set R) (y : val S) :=
  exists2 x, E x & eq y (phi x).

(* We prescribe monomorphisms, which let us lift real axioms in S back to R. *)
Record morphism R S (phi : val R -> val S) : Prop := Morphism {
  morph_le x y :
   le (phi x) (phi y) <-> le x y;
  morph_sup (E : set R) :
   has_sup E -> eq (phi (sup E)) (sup (image phi E));
  morph_add x y :
   eq (phi (add x y)) (add (phi x) (phi y));
  morph_zero :
   eq (phi (zero R)) (zero S);
  morph_opp x :
   eq (phi (opp x)) (opp (phi x));
  morph_mul x y :
   eq (phi (mul x y)) (mul (phi x) (phi y));
  morph_one :
   eq (phi (one R)) (one S);
  morph_inv x :
   ~ eq x (zero R) -> eq (phi (inv x)) (inv (phi x))
}.

(* Additional definitions, supported by notation in realsyntax.v.            *)

(* The 'lt' notation presupposes 'le' is total. *)
Notation lt x y := (~ le y x).

Fixpoint nat R (n : Datatypes.nat) := match n with
  | 0 => zero R
  | 1 => one R
  | Datatypes.S n1 => add (nat R n1) (one R)
  end.

Definition select_set R P x y : set R := fun z => IF P then eq z x else eq z y.

Definition select R P x y : val R := sup (select_set P x y).

(* We extend the partially defined inv and sup operations so that 0^-1 = 0    *)
(* and sup {x | True} = sup {x | False} = 0, in the notation of realsyntax.v. *)
Definition extended_inv R x : val R := select (eq x (zero R)) x (inv x).

Definition extended_sup R E : val R := select (has_sup E) (sup E) (zero R).

End Real.

Module RealCoercions.

Import Real.
Coercion val : structure >-> Sortclass.
Identity Coercion in_set : set >-> Funclass.
Identity Coercion in_rel : rel >-> Funclass.
Coercion model_structure : model >-> structure.
Coercion model_axioms : model >-> axioms.

End RealCoercions.

