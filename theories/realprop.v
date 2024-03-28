(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div order.
From mathcomp Require Import ssralg ssrnum ssrint rat intdiv.
From Coq Require Import Morphisms Setoid.
From fourcolor Require Import real realsyntax.

(******************************************************************************)
(*   This file establishes basic arithmetic/order/setoid properties of the    *)
(* abstract real numbers specified in real.v.                                 *)
(*   We also define a few additional operations in a Real.structure R:        *)
(*                      intR R m == injection of m : int and a : rat into R.  *)
(*                      ratR R a    (made locally into coercions for fixed R) *)
(*                       floor x == the largest integral y <= x.              *)
(*                   floor_set x == the singleton set {floor x}.              *)
(*                      range1 x == the unit interval [x, x+1).               *)
(* We use 'R' as the suffix standing for real arguments, since 'r' is already *)
(* used in the MathComp library for generic ring arguments.                   *)
(*   This file provides support for classical reasoning though theorem        *)
(* reals_classic : Real.model -> excluded_middle.                             *)
(*   We have general support for relational rewriting of real expressions in  *)
(* the Real.eq setoid; the theory is developped using extended_sup and        *)
(* extended_inv instead of sup and inv because the latter are only partially  *)
(* defined, making it impossible to have unconditional context lemmas.        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Hint Resolve iff_refl : core.
Local Open Scope real_scope.

Local Notation "m %:Z" := m%:Z%R%N (only parsing).
Local Notation "a %:Q" := a%:Q%R%N (only parsing).

Section RealOperations.

Variable R : Real.structure.

Definition min x y : R := IF x <= y then x else y.

Definition max x y : R := IF x >= y then x else y.

Definition intR m : R := match m with Posz n => n%:R | Negz n => - n.+1%:R end.

Definition ratR (a : rat) :=
  if a \is a Qint then intR (numq a) else intR (numq a) / intR (denq a).

Inductive floor_set x : Real.set R :=
  FloorSet m of intR m <= x : floor_set x (intR m).

Definition floor x : R := sup (floor_set x).

Definition range1 x : Real.set R := fun y => x <= y < x + 1.

End RealOperations.

Arguments min {R} x y.
Arguments max {R} x y.
Arguments floor_set {R} x.
Arguments floor {R} x.
Arguments range1 {R} x.

Section RealLemmas.

Variable R : Real.model.
Implicit Types x y z : R.
Implicit Type E : Real.set R.
Implicit Type m d : int.
Implicit Types n p : nat.
Implicit Types a b : rat.

Let intRR := intR R.
Local Coercion intRR : int >-> Real.val.
Let ratRR := ratR R.
Local Coercion ratRR : rat >-> Real.val.
Local Notation Rtype := (Real.val (Real.model_structure R)) (only parsing).
Local Notation eqR :=(@Real.eq (Real.model_structure R)) (only parsing).
Local Notation eqRset := (pointwise_relation Rtype iff).

(*********************************************************)
(**     Comparisons and the least upper bound axioms     *)
(*********************************************************)

Lemma leRR x : x <= x.
Proof. exact: (Real.le_reflexive R). Qed.
Hint Resolve leRR : core.

Lemma leR_trans x y z : x <= y -> y <= z -> x <= z.
Proof. exact: (Real.le_transitive R). Qed.

(* Lemmas supporting the extended sup require the excluded middle. *)
Lemma real_sup_ub E : Real.has_sup E -> Real.ub E (Real.sup E).
Proof. exact: (Real.sup_upper_bound R). Qed.

Lemma real_sup_total E x : Real.has_sup E -> Real.down E x \/ Real.sup E <= x.
Proof. exact: (Real.sup_total R). Qed.

Lemma leR_total x y : x <= y \/ y <= x.
Proof.
have ubEy: Real.has_sup {z | z = y} by split; exists y => // _ ->.
have [[_ ->] | leEyx] := real_sup_total x ubEy; first by left.
right; apply: leR_trans leEyx; apply: real_sup_ub => //; exists y => _ ->.
Qed.

Lemma eqR_le2 x y : x == y <-> x <= y <= x. Proof. by []. Qed.

Lemma eqR_le x y : x == y -> x <= y. Proof. by case. Qed.

Lemma gtR_neq x y : x > y -> x != y. Proof. by move=> gtxy []. Qed.

Lemma ltR_neq x y : x < y -> x != y. Proof. by move=> ltxy []. Qed.

Lemma ltR_total x y : x != y -> x < y \/ y < x.
Proof.
by case: (leR_total x y) => leyx neq_xy; [left | right] => lexy; case: neq_xy.
Qed.

Lemma ltRW x y : x < y -> x <= y. Proof. by have [] := leR_total x y. Qed.
Hint Resolve ltRW : core.

Lemma leR_lt_trans x y z : x <= y -> y < z -> x < z.
Proof. by move=> lexy ltyz lezx; have:= leR_trans lezx lexy. Qed.

Lemma ltR_le_trans x y z : x < y -> y <= z -> x < z.
Proof. by move=> ltxy leyz lezx; have:= leR_trans leyz lezx. Qed.

Lemma ltR_trans x y z : x < y -> y < z -> x < z.
Proof. by move/ltRW; apply: leR_lt_trans. Qed.

(**********************************************************)
(**      The setoid structure                             *)
(**********************************************************)

Lemma eqR_refl x : x == x. Proof. by []. Qed.
Hint Resolve eqR_refl : core.

Lemma eqR_congr x y : x = y -> x == y. Proof. by move->. Qed.

Lemma eqR_sym x y : x == y -> y == x. Proof. by case. Qed.
Hint Immediate eqR_sym : core.

Lemma eqR_trans x y z : x == y -> y == z -> x == z.
Proof. by move=> [lexy leyx] [/(leR_trans lexy)lexz /leR_trans/(_ leyx)]. Qed.

Add Parametric Relation : R eqR
  reflexivity proved by eqR_refl
  symmetry proved by eqR_sym
  transitivity proved by eqR_trans
  as real_equality.

Instance leR_Proper : Proper (eqR ==> eqR ==> iff) Real.le.
Proof.
move=> x1 x2 [lex12 lex21] y1 y2 [ley12 ley21].
by split=> [/(leR_trans lex21) | /(leR_trans lex12)] /leR_trans; apply.
Qed.

(**********************************************************)
(**       Addition                                        *)
(**********************************************************)

Lemma addRC x y : x + y == y + x.
Proof. exact: (Real.add_commutative R). Qed.

Instance addR_Proper : Proper (eqR ==> eqR ==> eqR) Real.add.
Proof.
move=> x1 x2 Dx y1 y2 Dy; apply: (@eqR_trans _ (x1 + y2)).
  by split; apply: (Real.add_monotone R); rewrite Dy.
by rewrite -!(addRC y2); split; apply: (Real.add_monotone R); rewrite Dx.
Qed.

Lemma addRA x y z : x + (y + z) == x + y + z.
Proof. exact: (Real.add_associative R). Qed.

Lemma addRCA x y z : x + (y + z) ==  y + (x + z).
Proof. by rewrite !addRA (addRC x). Qed.

Lemma addRAC x y z : x + y + z ==  x + z + y.
Proof. by rewrite -!addRA (addRC y). Qed.

Lemma addRACA x1 y1 x2 y2 : x1 + y1 + (x2 + y2)== x1 + x2 + (y1 + y2).
Proof. by rewrite !addRA (addRAC x1). Qed.

Lemma add0R x : 0 + x == x.
Proof. exact: (Real.add_zero_left R). Qed.

Lemma addR0 x : x + 0 == x.
Proof. by rewrite addRC add0R. Qed.

Lemma subRR x : x - x == 0.
Proof. exact: (Real.add_opposite_right R). Qed.

Lemma addRK x y : x + y - y == x.
Proof. by rewrite -addRA subRR addR0. Qed.

Lemma subRK x y : x - y + y == x.
Proof. by rewrite addRAC addRK. Qed.

Lemma addKR x y : - x + (x + y) == y.
Proof. by rewrite addRCA addRA subRR add0R. Qed.

Lemma addRI x y z : x + y == x + z -> y == z.
Proof. by move=> Dxy; rewrite -(addKR x y) Dxy addKR. Qed.

Lemma addIR x y z : y + x == z + x -> y == z.
Proof. by rewrite -!(addRC x); apply: addRI. Qed.

Lemma oppRK x : - - x == x.
Proof. by apply: (@addIR (- x)); rewrite addRC !subRR. Qed.

Lemma oppRD x y : - (x + y) == - x - y.
Proof. by apply: (@addRI (x + y)); rewrite subRR addRCA addRK addRC subRR. Qed.

Lemma oppRB x y : - (x - y) == y - x.
Proof. by rewrite oppRD oppRK addRC. Qed.

Lemma oppR0 : - (0 : R) == 0.
Proof. by apply: (@addRI 0); rewrite subRR add0R. Qed.

Lemma leR_add2l x y z : x + y <= x + z <-> y <= z.
Proof.
split=> leyz; last exact: (Real.add_monotone R).
by rewrite -(addKR x y) -(addKR x z); apply: (Real.add_monotone R).
Qed.

Lemma leR_add2r x y z : y + x <= z + x <-> y <= z.
Proof. by rewrite -!(addRC x); apply: leR_add2l. Qed.

Lemma subR_ge0 x y : 0 <= y - x <-> x <= y.
Proof. by rewrite -(leR_add2r x) subRK add0R. Qed.

Lemma subR_le0 x y : x - y <= 0 <-> x <= y.
Proof. by rewrite -subR_ge0 oppRB add0R subR_ge0. Qed.

Lemma leR_opp2 x y : - x <= - y <-> y <= x.
Proof. by rewrite -subR_ge0 oppRK addRC subR_ge0. Qed.

Lemma oppR_inj x y : - x == - y -> x == y.
Proof. by rewrite /eqR !leR_opp2 => /eqR_sym. Qed.

Instance oppR_Proper : Proper (eqR ==> eqR) Real.opp.
Proof. by move=> x1 x2 Dx; apply: oppR_inj; rewrite !oppRK. Qed.

(**********************************************************)
(**       Multiplication                                  *)
(**********************************************************)

Lemma mulRC x y : x * y == y * x.
Proof. exact: (Real.mul_commutative R). Qed.

Lemma mulRDr x y z : x * (y + z) == x * y + x * z.
Proof. exact: (Real.mul_distributive_right R). Qed.

Lemma mulRDl x y z : (y + z) * x == y * x + z * x.
Proof. by rewrite -!(mulRC x) -mulRDr. Qed.

Instance mulR_Proper : Proper (eqR ==> eqR ==> eqR) Real.mul.
Proof.
have posMr x y z : 0 <= x -> y == z -> x * y == x * z.
  by move=> pos_x [lex2 ley1]; split; apply: (Real.mul_monotone R).
suffices allMr x y z: y == z -> x * y == x * z.
  by move=> x1 x2 Dx _ y /allMr->; rewrite -!(mulRC y) allMr.
move/posMr=> Dy; have [/Dy // | x_le0] := leR_total 0 x.
have{x_le0} nx_ge0: 0 <= - x by rewrite -oppR0 leR_opp2.
by apply: (@addIR (- x * y)); rewrite -mulRDl !Dy -?mulRDl ?subRR.
Qed.

Lemma mulRA x y z : x * (y * z) == x * y * z.
Proof. exact: (Real.mul_associative R). Qed.

Lemma mulRCA x y z : x * (y * z) == y * (x * z).
Proof. by rewrite !mulRA (mulRC x). Qed.

Lemma mulRAC x y z : x * y * z == x * z * y.
Proof. by rewrite -!mulRA (mulRC y). Qed.

Lemma mulRACA x1 y1 x2 y2 : x1 * y1 * (x2 * y2) == x1 * x2 * (y1 * y2).
Proof. by rewrite !mulRA (mulRAC x1). Qed.

Lemma mul0R x : 0 * x == 0.
Proof. by apply (@addRI (0 * x)); rewrite -mulRDl !addR0. Qed.

Lemma mulR0 x : x * 0 == 0.
Proof. by rewrite mulRC mul0R. Qed.

Lemma mulRN x y : x * - y == - (x * y).
Proof. by apply (@addRI (x * y)); rewrite -mulRDr !subRR mulR0. Qed.

Lemma mulNR x y : - x * y == - (x * y).
Proof. by rewrite mulRC mulRN mulRC. Qed.

Lemma mul1R x : 1 * x == x.
Proof. exact: (Real.mul_one_left R). Qed.

Lemma mulR1 x : x * 1 == x.
Proof. by rewrite mulRC mul1R. Qed.

Lemma mul2R x : 2 * x == x + x.
Proof. by rewrite mulRDl !mul1R. Qed.

Lemma mulN1R x : - 1 * x == - x.
Proof. by rewrite mulNR mul1R. Qed.

Lemma mulRN1 x : x * - 1 == - x.
Proof. by rewrite mulRN mulR1. Qed.

(* Properties of 1 (finally!) *)

Lemma neqR10 : (1 : R) != 0.
Proof. exact: (Real.one_nonzero R). Qed.

Lemma ltR01 : (0 : R) < 1.
Proof.
case/ltR_total: neqR10 => // lt10 le10; case: lt10.
have{le10} le0N1: (0 : R) <= -1 by rewrite -oppR0 leR_opp2.
by have:= Real.mul_monotone R le0N1 le0N1; rewrite mulR0 mulN1R oppRK.
Qed.
Hint Resolve ltR01 : core.

Lemma ltRS x : x < x + 1.
Proof. by rewrite -subR_le0 (addRC x) addRK. Qed.
Arguments ltRS x : clear implicits.

Lemma ltPR x : x - 1 < x.
Proof. by rewrite -subR_le0 oppRB addRCA subRR addR0. Qed.
Arguments ltPR x : clear implicits.

Lemma ltR02 : (0 : R) < 2.
Proof. exact: ltR_trans ltR01 (ltRS 1). Qed.
Hint Resolve ltR02 : core.
Let leR02 : 0 <= 2 := ltRW ltR02.

(* Excluded middle and minimality of sup follow from the properties of 2! *)

Lemma reals_classic : excluded_middle.
Proof.
move=> P; have supE: Real.has_sup {x | x = 0 \/ P /\ x = 2 :> R}.
  by split; [exists 0; left | exists 2 => x [->|[_ ->]]].
have [[x [-> /ltR01 // | []]] | leE1] := real_sup_total 1 supE; first by left.
by right=> haveP; apply/(leR_lt_trans leE1 (ltRS 1))/real_sup_ub; last right.
Qed.

Lemma real_sup_le_ub E x : Real.has_sup E -> Real.ub E x -> Real.sup E <= x.
Proof.
set y := Real.sup E => supE leEx; pose z := (x + y) * Real.inv 2.
have le2M := Real.mul_monotone R leR02.
have mul2inv: 2 * Real.inv 2 == 1 := Real.mul_inverse_right R (gtR_neq ltR02).
have{mul2inv} D2z: 2 * z == x + y by rewrite mulRCA mul2inv mulR1.
have [[t /leEx-letx lezt] | leyz] := real_sup_total z supE.
  by have /le2M := leR_trans lezt letx; rewrite D2z mul2R leR_add2l.
by have /le2M := leyz; rewrite D2z mul2R leR_add2r.
Qed.

(* Deciding comparisons. *)

Lemma leR_eqVlt x y : x <= y <-> x == y \/ x < y.
Proof.
split=> [lexy | [-> | /ltRW] //].
by have [|/ltR_total[]//] := reals_classic (x == y); [left | right].
Qed.

Lemma ltR_neqAle x y : x < y <-> x != y /\ x <= y.
Proof.
by rewrite (leR_eqVlt x y); split=> [ltxy|[neqxy []]//]; split; [case | right].
Qed.

(* Properties of the conditional. *)

Section SelectR.

Variables (P : Prop) (x y : R).
Let decP := reals_classic P.
Let E := Real.select_set P x y.

Inductive selectR_spec : Real.set R := SelectRSpec z of E z : selectR_spec z.

Lemma IFR_cases : selectR_spec (IF P then x else y).
Proof.
have [z Ez]: Real.nonempty E.
  by have [haveP | notP] := decP; [exists x; left | exists y; right].
have Dz t: E t <-> t == z.
  by case: Ez => -[defP ->]; do [split=> [[][]|]; last by [left | right]].
have le_E_z: Real.ub E z by move=> _ /Dz->.
have supE: Real.has_sup E by split; exists z.
by split; apply/Dz; split; [apply: real_sup_le_ub | apply: real_sup_ub].
Qed.

Lemma IFR_then : P -> (IF P then x else y) == x.
Proof. by move=> haveP; case: IFR_cases => z [][]. Qed.

Lemma IFR_else : ~ P -> (IF P then x else y) == y.
Proof. by move=> notP; case: IFR_cases => z [][]. Qed.

End SelectR.

Instance IFR_Proper : Proper (iff ==> eqR ==> eqR ==> eqR) Real.select.
Proof.
move=> P1 P2 defP x1 x2 Dx y1 y2 Dy.
by case: IFR_cases => _ [][/defP-defP2 ->]; case: IFR_cases => _ [][? ->].
Qed.

(* Inverse and division. *)

Lemma invRE x : x != 0 -> x^-1 == Real.inv x.
Proof. exact: IFR_else. Qed.

Lemma divRR x : x != 0 -> x / x == 1.
Proof.
move=> nzx; case: x^-1 / IFR_cases => _ [][_ ->] //.
exact: (Real.mul_inverse_right R) nzx.
Qed.

Lemma pmulKR x y : x > 0 -> x^-1 * (x * y) == y.
Proof. by move=> /gtR_neq-x_nz; rewrite mulRCA mulRA (divRR x_nz) mul1R. Qed.

Lemma pmulRI x y z : x > 0 -> x * y == x * z -> y == z.
Proof. by move=> x_gt0 Dxy; rewrite -(pmulKR y x_gt0) Dxy pmulKR. Qed.

Lemma pmulIR x y z : x > 0 -> y * x == z * x -> y == z.
Proof. by rewrite -!(mulRC x); apply: pmulRI. Qed.

Local Notation leMl x_gt0 := (Real.mul_monotone R (ltRW x_gt0)).

Lemma invR_gt0 x : x > 0 -> x^-1 > 0.
Proof.
by move=> x_gt0 /(leMl x_gt0); rewrite (divRR (gtR_neq x_gt0)) mulR0 => /ltR01.
Qed.

Lemma leR_pmul2l x y z : x > 0 -> (x * y <= x * z <-> y <= z).
Proof.
move=> x_gt0; have invx_gt0: x^-1 > 0 by apply: invR_gt0.
by split=> [/(leMl invx_gt0) | /(leMl x_gt0)//]; rewrite !pmulKR.
Qed.

Lemma leR_pmul2r x y z : x > 0 -> (y * x <= z * x <-> y <= z).
Proof. by move=> x_gt0; rewrite -!(mulRC x); apply: leR_pmul2l x_gt0. Qed.

Lemma pmulR_rle0 x y : x > 0 -> (x * y <= 0 <-> y <= 0).
Proof. by move=> x_gt0; rewrite -(leR_pmul2l y 0 x_gt0) mulR0. Qed.

Lemma mulR_gt0 x y : x > 0 -> y > 0 -> x * y > 0.
Proof. by move=> xgt0 /(pmulR_rle0 _ xgt0). Qed.

Lemma mulRI x y z : x != 0 -> x * y == x * z -> y == z.
Proof.
move=> nz_x /(mulR_Proper (eqR_refl x^-1)).
by rewrite -!(mulRCA x) !mulRA divRR ?mul1R.
Qed.

Lemma mulIR x y z : x != 0 -> y * x == z * x -> y == z.
Proof. by rewrite -!(mulRC x); apply: mulRI. Qed.

Instance invR_Proper : Proper (eqR ==> eqR) Real.extended_inv.
Proof.
move=> x1 x2 Dx; have [x2_0 | nzx2] := reals_classic (x2 == 0).
  by rewrite ![_^-1]IFR_then ?Dx.
by apply: (mulRI nzx2); rewrite divRR // -Dx divRR // Dx.
Qed.

Lemma invR0 : (0 : R)^-1 == 0. Proof. exact: IFR_then. Qed.

Lemma invR1 : (1^-1 : R) == 1.
Proof. by have:= divRR neqR10; rewrite mul1R. Qed.

Lemma invRM x y : (x * y)^-1 == x^-1 / y.
Proof.
have [-> | nzx] := reals_classic (x == 0); first by rewrite !(invR0, mul0R).
have [-> | nzy] := reals_classic (y == 0); first by rewrite !(invR0, mulR0).
have nzxy: x * y != 0 by rewrite -(mulR0 x) => /(mulRI nzx).
by apply/(mulRI nzxy); rewrite mulRACA !divRR ?mulR1.
Qed.

Lemma invRN x : (- x)^-1 == - x^-1.
Proof.
have [-> | nz_x] := reals_classic (x == 0); first by rewrite !(oppR0, invR0).
have nz_negx: - x != 0 by rewrite -oppR0 => /oppR_inj.
by apply/(mulRI nz_negx); rewrite mulRN -mulNR oppRK !divRR.
Qed.

Lemma leR_pinv2 x y : x > 0 -> y > 0 -> (x^-1 <= y^-1 <-> y <= x).
Proof.
move=> xgt0 ygt0; rewrite -(leR_pmul2r _ _ xgt0).
by rewrite -(leR_pmul2r _ _ ygt0) -!mulRA pmulKR // (mulRC x) pmulKR.
Qed.

Lemma invR_neq0 x : x != 0 -> x^-1 != 0.
Proof. by move=> nz_x vx0; case: neqR10; rewrite -(divRR nz_x) vx0 mulR0. Qed.

Lemma invRK x : x^-1^-1 == x.
Proof.
have [-> | nz_x] := reals_classic (x == 0); first by rewrite !invR0.
by have nz_vx := invR_neq0 nz_x; apply/(mulIR nz_vx); rewrite mulRC !divRR.
Qed.

(**********************************************************)
(**      The least upper bound and derived operations.    *)
(**********************************************************)

Lemma supRE E : Real.has_sup E -> sup E == Real.sup E.
Proof. exact: IFR_then. Qed.

Lemma sup_ub E : Real.has_ub E -> Real.ub E (sup E).
Proof.
move=> ubE x Ex; have supE: Real.has_sup E by split; first by exists x.
by rewrite supRE //; apply: real_sup_ub.
Qed.

Lemma ge_sup_ub E x : Real.has_ub E -> sup E <= x -> Real.ub E x.
Proof. by move/sup_ub=> ubE leEx y /ubE-leyE; apply: leR_trans leEx. Qed.

Lemma sup_le_ub E x : Real.nonempty E -> Real.ub E x -> sup E <= x.
Proof.
move=> hasE leEx; have supE: Real.has_sup E by split; last exists x.
by rewrite supRE //; apply: real_sup_le_ub.
Qed.

Lemma sup_sup E : Real.has_sup E -> forall x, Real.ub E x <-> sup E <= x.
Proof.
by case=> hasE ubE x; split; [apply: sup_le_ub | apply: ge_sup_ub].
Qed.

Lemma sup_total E x : Real.nonempty E -> Real.down E x \/ sup E <= x.
Proof.
move=> hasE; have [|ubEx] := reals_classic (Real.down E x); first by left.
by right; apply: sup_le_ub => // y Ey; apply/ltRW=> lexy; case: ubEx; exists y.
Qed.

Instance nonempty_Proper : Proper (eqRset ==> iff) Real.nonempty.
Proof. by move=> E F defE; rewrite /Real.nonempty; setoid_rewrite defE. Qed.

Instance ub_Proper : Proper (eqRset ==> eqR ==> iff) Real.ub.
Proof. by move=> E F defE x1 x2 Dx; split=> ub_x y /defE/ub_x; rewrite Dx. Qed.

Instance down_Proper : Proper (eqRset ==> eqR ==> iff) Real.down.
Proof.
by move=> E F defE x1 x2 Dx; split=> -[y /defE]; rewrite (Dx, =^~ Dx); exists y.
Qed.

Instance has_ub_Proper : Proper (eqRset ==> iff) Real.has_ub.
Proof. by move=> E F dE; split=> -[y]; exists y; rewrite (dE, =^~ dE). Qed.

Instance has_sup_Proper : Proper (eqRset ==> iff) Real.has_sup.
Proof. by move=> E F dE; rewrite /Real.has_sup dE. Qed.

Instance sup_Proper : Proper (eqRset ==> eqR) sup.
Proof.
move=> E F eqEF; have [supE | trivE] := reals_classic (Real.has_sup E).
  by split; rewrite -sup_sup // (eqEF, =^~ eqEF) ?sup_sup // -eqEF. 
by rewrite ![sup _]IFR_else -?eqEF.
Qed.

Lemma nonempty_Rdown E : Real.nonempty (Real.down E) <-> Real.nonempty E.
Proof. by split=> [[_ [x Ex _]] | [x Ex]]; do 2?exists x. Qed.

Lemma ub_Rdown E : eqRset (Real.ub (Real.down E)) (Real.ub E).
Proof.
move=> z; split=> leEz x => [Ex | [y Ey lexy]]; first by apply: leEz; exists x.
exact/(leR_trans lexy)/leEz.
Qed.

Lemma has_ub_Rdown E : Real.has_ub (Real.down E) <-> Real.has_ub E.
Proof. by rewrite /Real.has_ub; setoid_rewrite ub_Rdown. Qed.

Lemma has_sup_Rdown E : Real.has_sup (Real.down E) <-> Real.has_sup E.
Proof. by rewrite /Real.has_sup nonempty_Rdown has_ub_Rdown. Qed.

Lemma sup_Rdown E : sup (Real.down E) == sup E.
Proof.
have [supE | trivE] := reals_classic (Real.has_sup E).
  rewrite /eqR -!sup_sup ?has_sup_Rdown // (ub_Rdown _ _) sup_sup //.
  by split=> //; rewrite -(ub_Rdown _ _) sup_sup // has_sup_Rdown.
by do 2!case: (sup _) / IFR_cases => ? [][]//; rewrite has_sup_Rdown // => _ ->.
Qed.

(* Min and max.                                                         *)

Section MinMaxReal.

Variable x y : R.

Lemma leR_minl : min x y <= x.
Proof. by case: (min x y) / IFR_cases => _ [][lemx ->] //; apply/ltRW. Qed.

Lemma leR_minr : min x y <= y.
Proof. by case: (min x y) / IFR_cases => _ [][lemy ->]. Qed.
Hint Resolve leR_minl leR_minr : core.

Lemma ltR_min z : z < min x y <-> z < x /\ z < y.
Proof.
case: (min x y) / IFR_cases => _ [[lexy]|[ltyx]] ->.
  by split=> [ltzx|[]//]; split=> //; apply: ltR_le_trans ltzx lexy.
by split=> [ltzy|[]//]; split=> //; apply: ltR_trans ltzy ltyx.
Qed.

Lemma leR_min z : z <= min x y <-> z <= x /\ z <= y.
Proof.
split=> [lezm | [lezx lezy]]; first by split; apply: leR_trans lezm _.
by case: (min x y) / IFR_cases => _ [] [_ ->].
Qed.

Lemma leR_maxl : x <= max x y.
Proof. by case: (max x y) / IFR_cases => _ [][ltxm ->]//; apply/ltRW. Qed.

Lemma leR_maxr : y <= max x y.
Proof. by case: (max x y) / IFR_cases => _ [][leym ->]. Qed.
Hint Resolve leR_maxl leR_maxr : core.

Lemma ltR_max z : max x y < z <-> x < z /\ y < z.
Proof.
case: (max x y) / IFR_cases => _ [[leyx]|[ltxy]] ->.
  by split=> [ltxz | []//]; split=> //; apply: leR_lt_trans leyx ltxz.
by split=> [ltyz | []//]; split=> //; apply: ltR_trans ltxy ltyz.
Qed.

Lemma leR_max z : max x y <= z <-> x <= z /\ y <= z.
Proof.
split=> [lemz | [lexz leyz]]; first by split; apply: leR_trans lemz.
by case: (max x y) / IFR_cases => _ [] [_ ->].
Qed.

End MinMaxReal.

Instance min_Proper : Proper (eqR ==> eqR ==> eqR) min.
Proof. by move=> x1 x2 Dx y1 y2 Dy; rewrite /min Dx Dy. Qed.

Instance max_Proper : Proper (eqR ==> eqR ==> eqR) max.
Proof. by move=> x1 x2 Dx y1 y2 Dy; rewrite /max Dx Dy. Qed.

(**********************************************************)
(** Properties of the injections from N, Z, and Q into R  *)
(**********************************************************)

Lemma intRS n : n.+1 == n + 1.
Proof. by case: n => [|n] /=; rewrite ?add0R // addRC. Qed.

Lemma ltR0Sn n : 0 < n.+1.
Proof. by elim: n => // n IHn; apply: ltR_trans IHn _; apply: ltRS. Qed.
Arguments ltR0Sn n : clear implicits.

Lemma leR0n n : 0 <= n.
Proof. by case: n => // n; apply/ltRW/ltR0Sn. Qed.
Hint Resolve ltR0Sn leR0n : core.

Lemma intRN m : (- m)%R == - m.
Proof. by case: m => [[|n]|n]; rewrite ?oppR0 ?oppRK. Qed.

Lemma intRD1 m : (m + 1)%R == m + 1.
Proof.
case: m => [n|[|n]]; [by rewrite addrC intRS | by rewrite addRC subRR |].
by rewrite /= subn1 oppRD subRK.
Qed.

Lemma intRD m1 m2 : (m1 + m2)%R == m1 + m2.
Proof.
suffices intRDn m n: (m + n)%R == m + n.
  by case: m2 => // n; rewrite -[m1]opprK NegzE -opprD !(intRN, intRDn) oppRD.
elim: n => [|n IHn]; first by rewrite addr0 addR0.
by rewrite -addn1 PoszD addrA !intRD1 IHn addRA.
Qed.

Lemma intRB m1 m2 : (m1 - m2)%R == m1 - m2.
Proof. by rewrite intRD intRN. Qed.

Lemma intRB1 m : (m - 1)%R == m - 1.
Proof. exact: intRB. Qed.

Lemma intRM m1 m2 : (m1 * m2)%R == m1 * m2.
Proof.
suffices intMn m n: (m * n)%R == m * n.
  by case: m2 => n; rewrite ?NegzE ?mulrN ?intRN ?mulRN intMn.
rewrite -mulrzz -pmulrn; elim: n => [|n IHn]; first by rewrite mulR0.
by rewrite mulrS (PoszD 1%N) !intRD mulRDr mulR1 -IHn.
Qed.

Lemma intR_addbit m : m == (m %% 2%N)%Z + 2 * (m %/ 2%N)%Z.
Proof. by rewrite {1}(divz_eq m 2%:Z) mulRC addRC intRD intRM. Qed.

Lemma intR_leP m1 m2 : reflect (m1 <= m2) (m1 <= m2)%R.
Proof.
apply: (equivP idP); rewrite -subr_ge0 -subR_ge0 -intRB.
by case: (m2 - m1)%R => n; split; rewrite // -oppR0 leR_opp2 => /ltR0Sn.
Qed.

Lemma intR_ltP m1 m2 : reflect (m1 < m2) (m1 + 1 <= m2)%R.
Proof. by rewrite lezD1 ltNge; apply: (iffP idP) => /intR_leP. Qed.

(* Embedding the rationals.                                                  *)

Lemma ratRE a : ratRR a == numq a / denq a.
Proof.
by rewrite /ratRR /ratR Qint_def; case: eqP => // ->; rewrite invR1 mulR1.
Qed.

Lemma ratR_eq a : {r | a = (r.1%:Q / r.2.+1%:Q)%R & a * r.2.+1 == r.1}.
Proof.
have [d Dd] := denqP a; exists (numq a, d); rewrite -Dd ?divq_num_den //=.
by rewrite ratRE mulRAC mulRC (mulRC (numq a)) pmulKR ?Dd.
Qed.

Lemma ratR_leP a1 a2 : reflect (a1 <= a2) (a1 <= a2)%R.
Proof.
have [[r1 {3}-> Dr1] [r2 {3}-> Dr2]] := (ratR_eq a1, ratR_eq a2).
rewrite ler_pdivlMr ?ltr0Sn // mulrAC ler_pdivrMr ?ltr0Sn //.
rewrite -!intrM ler_int /=; apply: (equivP (intR_leP _ _)).
by rewrite !intRM -Dr1 -Dr2 mulRAC !leR_pmul2r.
Qed.

Lemma ratR_ltP a1 a2 : reflect (a1 < a2) (a1 < a2)%R.
Proof. by rewrite ltNge; apply: (iffP idP) => /ratR_leP. Qed.

Lemma ratR_lt0P a : reflect (0 < a) (0 < a)%R. Proof. exact: (ratR_ltP 0). Qed.

Lemma ratRz m : m%:Q = m :> R.
Proof. by rewrite /ratRR /ratR rpred_int numq_int. Qed.

Lemma ratR0 : 0%:Q = 0 :> R. Proof. by []. Qed.
Lemma ratR1 : 1%:Q = 1 :> R. Proof. by []. Qed.
Lemma ratR2 : 2%:Q = 2 :> R. Proof. by []. Qed.

Lemma ratRN a : (- a)%R == - a.
Proof. by rewrite !ratRE numqN denqN intRN mulNR. Qed.

Lemma ratRMn a n : (a * n%:Q)%R == a * n.
Proof.
have [[r1 Da Dr1] [r2 Dan Dr2]] := (ratR_eq a, ratR_eq (a * n%:Q)).
apply/(pmulIR (ltR0Sn r2.2))/(pmulIR (ltR0Sn r1.2)).
rewrite {}Dr2 -2!(mulRAC _ r1.2.+1) {}Dr1 -!intRM -!ratRz !intrM.
apply/eqR_congr/(congr1 ratRR)/(canRL (divfK _)); first by rewrite intr_eq0.
by rewrite mulrAC -{}Dan {}Da  mulrAC divfK ?intr_eq0.
Qed.

Lemma ratRD a1 a2 : (a1 + a2)%R == a1 + a2.
Proof.
have [[r1 {2}-> Dr1] [r2 {2}-> Dr2]] := (ratR_eq a1, ratR_eq a2).
apply/(pmulIR (ltR0Sn r2.2))/(pmulIR (ltR0Sn r1.2)).
rewrite !mulRDl (mulRAC a1) Dr1 Dr2 -!ratRMn !mulrDl mulrAC !divfK ?intr_eq0 //.
by rewrite -!intrM -intrD ratRz intRD !intRM.
Qed.

Lemma ratRM a1 a2 : (a1 * a2)%R == a1 * a2.
Proof.
have [[r1 {2}-> Dr1] [r2 {2}-> Dr2]] := (ratR_eq a1, ratR_eq a2).
apply/(pmulIR (ltR0Sn r1.2))/(pmulIR (ltR0Sn r2.2)).
rewrite -2!ratRMn (mulRAC a1) -mulRA {}Dr1 {}Dr2 -mulrA mulrACA.
by rewrite !divfK ?intr_eq0 // -intrM ratRz intRM.
Qed.

Lemma ratR_pinv a : (0 < a)%R -> a^-1%R == a^-1.
Proof.
move=> a_gt0; have aR_gt0: 0 < a by rewrite -ratR0; apply/ratR_ltP.
apply: (pmulIR aR_gt0); rewrite -ratRM mulRC (divRR (gtR_neq aR_gt0)).
by rewrite mulVf ?ratR1 ?gt_eqF.
Qed.

(* The floor function                                                   *)

Fact ub_floor_set x : Real.ub (floor_set x) x.
Proof. by move=> y [m]. Qed.
Hint Resolve ub_floor_set : core.

Fact has_ub_floor_set x : Real.has_ub (floor_set x).
Proof. by exists x. Qed.
Hint Resolve has_ub_floor_set : core.

Let has_floor_max x : Real.nonempty (floor_set x) -> x < floor x + 1.
Proof.
move=> has_x0 le_xx.
have inc_lex m (lemx : m <= x): (m + 1)%R <= x.
  by apply: leR_trans le_xx; rewrite intRD1 leR_add2r; apply: sup_ub.
have [[_ [m]] | ] := sup_total (floor x - 1) has_x0; last exact: ltPR.
do 2!move/inc_lex; rewrite -/intRR -{2}[m](addrK 1%R) intRB1 leR_add2r => lem2x.
by case/leR_lt_trans/(_ (ltRS _)); rewrite -intRD1; apply: sup_ub.
Qed.

Fact nonempty_floor_set x : Real.nonempty (floor_set x).
Proof.
have [le0x | lex0] := leR_total 0 x; first by exists 0%N.
have ub_nx0: Real.has_sup (floor_set (- x)).
  by split=> //; exists 0%N; split; rewrite -leR_opp2 oppRK oppR0.
have [[_ [m _] lexm] | /ltPR//] := sup_total (floor (- x) - 1) (proj1 ub_nx0).
pose m1 := (m + 1)%R; pose m2 := (m1 + 1)%R.
exists (- m2)%R; split; move: lexm; rewrite -/intRR -(addRK m 1) leR_add2r.
rewrite -{2}(oppRK x) intRN leR_opp2 -{2}(subRK (- x) 1) !intRD1 leR_add2r.
apply/leR_trans/ltRW; rewrite -(leR_add2r 1) subRK.
by apply: has_floor_max; case: ub_nx0.
Qed.
Hint Resolve nonempty_floor_set : core.

Lemma has_sup_floor_set x : Real.has_sup (floor_set x). Proof. by []. Qed.
Hint Resolve has_sup_floor_set : core.

Instance floor_Proper : Proper (eqR ==> eqR) floor.
Proof.
move=> x1 x2 Dx; apply: sup_Proper => y.
by split=> -[m int_m_x]; split; rewrite (Dx, =^~ Dx).
Qed.

Instance range1_Proper : Proper (eqR ==> eqR ==> iff) range1.
Proof. by move=> x1 x2 Dx y1 y2 Dy; rewrite /range1 Dx Dy. Qed.

Lemma range1_floor x : range1 (floor x) x.
Proof. by split; [apply: sup_le_ub | apply: has_floor_max]. Qed.

Lemma int_floor x : exists m : int, floor x == m.
Proof.
case: (range1_floor x); set y := floor x => leyx ltxy1; pose h2 : R := 2^-1.
have h2gt0: 0 < h2 by apply: invR_gt0.
have lty2y: y - h2 < y by rewrite -subR_ge0 addRC addKR -oppR0 leR_opp2.
have [[_ [m lemx] ley2m] | //] := sup_total (y - h2) (nonempty_floor_set x).
rewrite -/intRR in lemx ley2m; exists m; split; last exact: sup_ub.
pose m2 := m + h2; have leym2: y <= m2 by rewrite -(leR_add2r (- h2)) addRK.
apply: sup_le_ub => // _ [m1 lem1x]; rewrite -(leR_add2r 1) -!intRD1.
apply/intR_leP/intR_ltP; have:= h2gt0; rewrite -(leR_add2l m2) addR0.
rewrite -addRA -mul2R (divRR (gtR_neq ltR02)) -(intRD1 m).
exact/leR_lt_trans/(ge_sup_ub _ leym2).
Qed.

Lemma range1z_inj x m1 m2 : range1 m1 x -> range1 m2 x -> m1 = m2.
Proof.
move=> [m1x x_m1] [m2x x_m2].
wlog suffices: m1 m2 m1x {x_m1 m2x} x_m2 / (m1 <= m2)%R.
  by move=> IH; apply/eqP; rewrite eq_le !IH.
rewrite -(lerD2r 1); apply/intR_ltP.
by rewrite intRD1; apply: leR_lt_trans x_m2.
Qed.

Lemma range1zz m : range1 m m.
Proof. by split; rewrite // -intRD1; apply/intR_ltP. Qed.

Lemma range1z_floor m x : range1 m x <-> floor x == m.
Proof.
gen have IHm: m / floor x == m -> range1 m x.
  by move <-; apply: range1_floor.
split=> [int_m_x|/IHm//]; have [m1 Dm1] := int_floor x.
by rewrite -(range1z_inj (IHm m1 Dm1) int_m_x).
Qed.

Lemma floor_znat m : floor m == m.
Proof. by rewrite -(range1z_floor m m); apply: range1zz. Qed.

Lemma find_range1z x : exists m : int, range1 m x.
Proof.
by have [m Dm] := int_floor x; exists m; case: (range1z_floor m x); auto.
Qed.

Lemma ratR_dense x y : x < y -> exists2 a : rat, x < a & a < y.
Proof.
move=> ltxy; pose z := y - x; have z_gt0: z > 0 by rewrite subR_le0.
have [[d|n] [ledv ltvd1]] := find_range1z z^-1; last first.
  case: ltvd1; apply: ltRW; apply: leR_lt_trans (invR_gt0 z_gt0).
  by rewrite NegzE intRN intRS oppRD subRK -subR_ge0 add0R oppRK.
set d1 : R := d.+1; have d1gt0: d1 > 0 by apply: ltR0Sn.
have [m [lemx ltxm1]] := find_range1z (d1 * x).
exists ((m + 1)%:Q / d.+1%:Q)%R; rewrite -(leR_pmul2r _ _ d1gt0) -ratRMn.
  by rewrite divfK ?intr_eq0 // mulRC ratRz intRD1.
rewrite divfK ?intr_eq0 // ratRz intRD1.
rewrite -(addKR x y) addRC -addRA -/z mulRC mulRDr -(divRR (gtR_neq z_gt0)).
move: lemx; rewrite -(leR_add2r (d1 * z)); apply: ltR_le_trans.
by rewrite leR_add2l mulRC leR_pmul2l // /d1 intRS.
Qed.

Instance imageR_Proper (S : Real.structure) :
  Proper
    (pointwise_relation S eqR ==> pointwise_relation S iff ==> eqR ==> iff)
  Real.image.
Proof.
move=> f1 f2 Df E1 E2 defE y1 y2 Dy.
by split=> -[x /defE-Ex Dfx]; exists x => //; rewrite (Df, =^~Df) -Dfx Dy.
Qed.

End RealLemmas.

Arguments neqR10 R _ : clear implicits.
Arguments ltR01 R _ : clear implicits.
Arguments ltR02 R _ : clear implicits.
Arguments ltRS {R} x _.
Arguments ltPR {R} x _.
Arguments ltR0Sn R n _ : clear implicits.
Arguments intR_leP {R m1 m2}.
Arguments intR_ltP {R m1 m2}.
Arguments ratR_leP {R a1 a2}.
Arguments ratR_ltP {R a1 a2}.

Hint Resolve eqR_refl leRR ltRW : core.

Existing Instance real_equality.
Existing Instance real_equality_Transitive.
Existing Instance real_equality_Symmetric.
Existing Instance real_equality_Reflexive.
Existing Instance real_equality_relation.
Existing Instance leR_Proper.
Existing Instance addR_Proper.
Existing Instance oppR_Proper.
Existing Instance mulR_Proper.
Existing Instance invR_Proper.
Existing Instance IFR_Proper.
Existing Instance nonempty_Proper.
Existing Instance ub_Proper.
Existing Instance has_ub_Proper.
Existing Instance has_sup_Proper.
Existing Instance sup_Proper.
Existing Instance min_Proper.
Existing Instance max_Proper.
Existing Instance range1_Proper.
Existing Instance floor_Proper.
Existing Instance imageR_Proper.

