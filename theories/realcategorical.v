(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat seq order ssralg ssrnum ssrint rat.
Require Import Morphisms Setoid.
From fourcolor
Require Import real realsyntax realprop.

(******************************************************************************)
(*   A proof that the real axiomatisation is categorical -- hence that our    *)
(* Dedekind construction is essentially unique.                               *)
(*   We show:                                                                 *)
(*    Rmorph_axioms : the axioms of S : Real.model lift to R : Real.structure *)
(*                    when phi : R -> S is a Real.morphism.                   *)
(*     Rmorph_model : under the above conditions, there is a Real.model whose *)
(*                    Real.structure coercion is R.                           *)
(*     Rmorph_idfun : Real.morphism holds for idfun R when R is a Real.model. *)
(*      Rmorph_comp : Real.morphism holds for phi \o psi when it holds for    *)
(*                    phi and psi, and the codomain of phi is a Real.model.   *)
(*      Rmorph_uniq : there's at most one Real.morphism from a Real.structure *)
(*                    to a Real.model (any two such are extensionally equal). *)
(*    Rmorph_to S x : the (unique) image of x : R by a morphism to S, when    *)
(*                    both R and S are Real.model.                            *)
(*   Rmorph_toP R S : Real.morphism holds for @Rmorph_to R S (as in above).   *)
(*   Rmorph_to_id R : Rmorph_to R is (extensionally) the identity on R.       *)
(*  Rmorph_to_inv R S : Rmorph_to R is (extensionally) an inverse to          *)
(*                    Rmorph_to S.                                            *)
(* --> Rmorph_to, together with Rmorph_toP and Rmorph_to_inv, provides a      *)
(* constructive proof that any two Real.model are isomorphic.                 *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Section RealsCategorical.

Hint Resolve eqR_refl leRR : core.

Local Open Scope real_scope.

Section RealMorph.
(* Derived morphism properties that do not depend on real axioms. *)

Variables (R S : Real.structure) (phi : R -> S).
Hypothesis phiP : Real.morphism phi.

Lemma Rmorph_eq x y : phi x == phi y <-> x == y.
Proof. by rewrite /Real.eq !Real.morph_le. Qed.

Lemma Rmorph_Proper : Proper (Real.eq ==> Real.eq) phi.
Proof. by move=> x y /Rmorph_eq. Qed.

End RealMorph.

Section RealMorphAxioms.

(* A monomorphism lifts back the real axioms, and preserves the rationals. *)

Variables (R : Real.structure) (S : Real.model) (phi : R -> S).
Hypothesis phiP : Real.morphism phi.
Implicit Types (x y z : R) (E : Real.set R).

Let phi_le := Real.morph_le phiP.
Let phi_eq := Rmorph_eq phiP.
Let phi_sup := Real.morph_sup phiP.
Let phiD := Real.morph_add phiP.
Let phi0 := Real.morph_zero phiP.
Let phiN := Real.morph_opp phiP.
Let phiM := Real.morph_mul phiP.
Let phi1 := Real.morph_one phiP.
Let phiV := Real.morph_inv phiP.

(* Some derived morphism properties that depend on S being a model. *)
Lemma Rmorph_neq0 x : x != 0 -> phi x != 0.
Proof. by rewrite -phi_eq phi0. Qed.

Lemma Rimage_has_sup E : Real.has_sup E -> Real.has_sup (Real.image phi E).
Proof.
move=> [[x Ex] [z ubEz]]; split; first by exists (phi x), x.
by exists (phi z) => _ [y Ey ->]; rewrite phi_le; apply: ubEz.
Qed.

Lemma Rmorph_nat n : phi n%:R == n%:R.
Proof. by case: n; [apply: phi0 | elim=> //= n IHn; rewrite phiD phi1 IHn]. Qed.

Lemma Rmorph_int m : phi (intR R m) == intR S m.
Proof. by case: m => n; rewrite ?phiN Rmorph_nat. Qed.

(* Real axioms for R. *)

Let Rle_refl x : x <= x. Proof. by rewrite -phi_le. Qed.

Let Rle_trans x y z : x <= y -> y <= z -> x <= z.
Proof. by rewrite -!phi_le; apply: leR_trans. Qed.

Let Rsup_ub E : Real.has_sup E -> Real.ub E (Real.sup E).
Proof.
move=> supE x Ex; have supEphi := Rimage_has_sup supE.
by rewrite -phi_le phi_sup //; apply: (Real.sup_upper_bound S) => //; exists x.
Qed.

Let Rsup_total E x : Real.has_sup E -> Real.down E x \/ Real.sup E <= x.
Proof.
move=> supE; have supEphi := Rimage_has_sup supE.
have [[_ [y Ey ->]]|] := Real.sup_total S (phi x) supEphi.
  by rewrite phi_le; left; exists y.
by rewrite -phi_sup // phi_le; right.
Qed.

Let Radd_mono x y z : y <= z -> x + y <= x + z.
Proof. by rewrite -!phi_le !phiD leR_add2l. Qed.

Let Rmul_mono x y z : x >= 0 -> y <= z -> x * y <= x * z.
Proof. by rewrite -!phi_le !phiM phi0; apply: (Real.mul_monotone S). Qed.

Let Radd0 x : 0 + x == x.
Proof. by rewrite -phi_eq phiD phi0 add0R. Qed.

Let RaddC x y : x + y == y + x.
Proof. by rewrite -phi_eq !phiD addRC. Qed.

Let RaddA x y z : x + (y + z) == x + y + z.
Proof. by rewrite -phi_eq !phiD addRA. Qed.

Let RaddN x : x - x == 0.
Proof. by rewrite -phi_eq phiD phiN phi0 subRR. Qed.

Let RmulC x y : x * y == y * x.
Proof. by rewrite -phi_eq !phiM mulRC. Qed.

Let RmulA x y z : x * (y * z) == x * y * z.
Proof. by rewrite -phi_eq !phiM mulRA. Qed.

Let RmulDr x y z : x * (y + z) == x * y + x * z.
Proof. by rewrite -phi_eq !(phiD, phiM) mulRDr. Qed.

Let Rmul1 x : 1 * x == x.
Proof. by rewrite -phi_eq phiM phi1 mul1R. Qed.

Let RmulV x : x != 0 -> x * Real.inv x == 1.
Proof.
move=> nzx; rewrite -phi_eq phiM phi1 phiV //.
exact: (Real.mul_inverse_right S (Rmorph_neq0 nzx)).
Qed.

Let Rneq10 : (1 : R) != 0.
Proof. by rewrite -phi_eq phi1 phi0; apply: neqR10. Qed.

Theorem Rmorph_axioms : Real.axioms R. Proof. by []. Qed.
Let RR := Real.Model Rmorph_axioms.

Lemma Rmorph_model : {Rmodel : Real.model | R = Rmodel}.
Proof. by exists RR. Qed.

(* These properties use the fact that R is actually a model. *)
Lemma Rmorph_inv x : phi x^-1 == (phi x)^-1.
Proof.
have phi_Proper := Rmorph_Proper phiP.
case: (x : RR)^-1 / IFR_cases => _ [][x0 ->]; first by rewrite x0 !phi0 invR0.
by rewrite phiV ?invRE //; apply: Rmorph_neq0.
Qed.

Lemma Rmorph_rat a : phi (ratR R a) == ratR S a.
Proof. by rewrite /ratR; case: ifP; rewrite ?phiM ?Rmorph_inv !Rmorph_int. Qed.

End RealMorphAxioms.

(* The categorical structure of the models of the reals. *)

Theorem Rmorph_comp (R S : Real.structure) (T : Real.model)
                           (phi : S -> T) (psi : R -> S) :
  Real.morphism phi -> Real.morphism psi -> Real.morphism (phi \o psi).
Proof.
move=> phiP psiP; have [phiR phiPr] := (Rmorph_model phiP, Rmorph_Proper phiP).
case: phiR => {S}[S ->] in phi psi phiP phiPr psiP *.
split=> /= *; first 2 last.
- by rewrite !Real.morph_add.
- by rewrite !Real.morph_zero.
- by rewrite !Real.morph_opp.
- by rewrite !Real.morph_mul.
- by rewrite !Real.morph_one.
- by rewrite !Real.morph_inv //; apply: Rmorph_neq0.
- by rewrite !Real.morph_le.
rewrite !Real.morph_sup //; last exact: Rimage_has_sup.
set E1 := Real.image phi _; set E2 := Real.image _ _.
have eqE12: pointwise_relation T iff E1 E2.
  by split=> [[_ [x ? ->]] | [x]]; last exists (psi x) => //; exists x.
by rewrite -!supRE -?eqE12 //; do 2?apply/Rimage_has_sup.
Qed.

Theorem Rmorph_id (R : Real.model) : Real.morphism (@idfun R).
Proof.
split=> //= E supE; set F := Real.image idfun E.
have eqEF: pointwise_relation R iff (Real.down E) (Real.down F).
  by move=> x; split=> [[y Ey] | [_ [y Ey ->]]]; exists y => //; exists y.
have supF: Real.has_sup F by rewrite -has_sup_Rdown -eqEF has_sup_Rdown.
by rewrite -!supRE // -sup_Rdown eqEF sup_Rdown.
Qed.

Theorem Rmorph_uniq (S : Real.structure) (R : Real.model) (phi psi : S -> R) :
    Real.morphism phi -> Real.morphism psi ->
  pointwise_relation S Real.eq phi psi.
Proof.
move=> phiP psiP x.
wlog suffices IH: phi psi phiP psiP / phi x <= psi x; first by split; apply: IH.
have [//|/ratR_dense[a /ltRW-lexa []]] := reals_classic R (phi x <= psi x).
by rewrite -(Rmorph_rat phiP) Real.morph_le // -(Real.morph_le psiP) Rmorph_rat.
Qed.

Section CanonicalRealMorphism.

(* There is a (canonical) monomorphism between two real structures. *)

Variable R S : Real.model.

Inductive Rmorph_cut (x : R) : Real.set S :=
  RmorphCut a of ratR R a < x : Rmorph_cut x (ratR S a).

Definition Rmorph_to x := sup (Rmorph_cut x).
Local Notation psi := Rmorph_to.

Let psi_has_sup x : Real.has_sup (Rmorph_cut x).
Proof.
split; first by have [a _ ltax] := ratR_dense (ltPR x); exists (ratR S a).
have [a ltxa _] := ratR_dense (ltRS x); exists (ratR S a) => _ [b ltbx].
by apply/ltRW/ratR_ltP/(@ratR_ltP R); apply: ltR_trans ltbx ltxa.
Qed.

Let psi_is_ub x a : ratR R a < x -> ratR S a < psi x.
Proof.
case/ratR_dense=> b /ratR_ltP/(@ratR_ltP S)-ltab ltbx.
by have [_ ub_x] := psi_has_sup x; apply/(ltR_le_trans ltab)/sup_ub.
Qed.

Let psi_le_ub x y' : Real.ub (Rmorph_cut x) y' -> psi x <= y'.
Proof. by move/(sup_sup (psi_has_sup x)). Qed.

Let psi_rat a : psi (ratR R a) == ratR S a.
Proof.
have: psi (ratR R a) <= ratR S a.
  by apply: psi_le_ub => _ [b ltba]; apply/ltRW/ratR_ltP/(@ratR_ltP R).
rewrite leR_eqVlt => -[] // /ratR_dense[b ltba /ratR_ltP/(@ratR_ltP R)ltab].
by case: ltba; apply/ltRW/psi_is_ub.
Qed.

Let psi_le x y : psi x <= psi y <-> x <= y.
Proof.
split=> lexy; last first.
  by apply: psi_le_ub => _ [a ltax]; apply/ltRW/psi_is_ub/(ltR_le_trans ltax).
have [//|/ratR_dense[a ltya /psi_is_ub[]]] := reals_classic R (x <= y).
apply/(leR_trans lexy)/psi_le_ub=> _ [c ltcy].
by apply/ltRW/ratR_ltP/(@ratR_ltP R); apply: ltR_trans ltcy ltya.
Qed.

Let psi_eq x y : psi x == psi y <-> x == y.
Proof. by rewrite /Real.eq !psi_le. Qed.

Instance Rmorph_to_Proper : Morphisms.Proper (Real.eq ==> Real.eq) psi.
Proof. by move=> x y; rewrite psi_eq. Qed.

Let psi_0 : psi 0 == 0. Proof. by rewrite -!ratR0 psi_rat. Qed.
Let psi_ge0 x : psi x <= 0 <-> x <= 0. Proof. by rewrite -psi_0 psi_le. Qed.

Let psi_opp x : psi (- x) == - psi x.
Proof.
split.
  apply: psi_le_ub => _ [a /ltRW-leax].
  by rewrite -leR_opp2 oppRK -ratRN -psi_rat psi_le ratRN -leR_opp2 oppRK.
have [//|/ratR_dense[a ltxa []]] := reals_classic R (- psi x <= psi (- x)).
rewrite -leR_opp2 oppRK -ratRN; apply/ltRW/psi_is_ub.
by rewrite -leR_opp2 ratRN oppRK -psi_le psi_rat.
Qed.

Let psi_add x y : psi (x + y) ==  psi x + psi y.
Proof.
wlog suffices IHxy: x y / psi (x + y) <= psi x + psi y.
  split; [exact: IHxy | rewrite -(leR_add2r (psi (- y)))].
  by apply: leR_trans (IHxy _ _); rewrite psi_opp !addRK.
apply: psi_le_ub => _ [a ltxy]; pose z := ratR R a - y.
have ltzx: z < x by rewrite -(leR_add2r y) subRK.
have [b ltzb ltbx] := ratR_dense ltzx.
rewrite -(subrK b a) ratRD addRC; set c := (a - b)%R.
have ltcy: ratR R c < y.
  rewrite ratRD ratRN -(leR_add2r (ratR R b)) subRK addRC. 
  by rewrite -(leR_add2r (- y)) addRK.
apply/ltRW/(@ltR_trans _ _ (psi x + ratR S c)).
  by rewrite leR_add2r; apply: psi_is_ub.
by rewrite leR_add2l; apply: psi_is_ub.
Qed.

Let psi_1 : psi 1 == 1.
Proof. by rewrite -!ratR1 psi_rat. Qed.

Let psi_pinv x : x > 0 -> psi x^-1 == (psi x)^-1.
Proof.
move=> lt0x; have lt0y: 0 < psi x by rewrite psi_ge0.
split.
  apply: psi_le_ub => _ [a ltax]; apply/ltRW.
  have [/(@ratR_leP S a 0)ge0a | lt0a] := lerP a 0.
    by apply/(leR_lt_trans ge0a)/invR_gt0.
  have va_gt0: (0 < a^-1)%R by rewrite invr_gt0.
  rewrite -[a]invrK ratR_pinv ?leR_pinv2 //; last exact/ratR_lt0P.
  rewrite -psi_rat psi_le -leR_pinv2 //; last exact/ratR_lt0P.
  by rewrite -ratR_pinv ?invrK.
have [//|/ratR_dense[a ltvxa []]] := reals_classic R ((psi x)^-1 <= psi x^-1).
have lt0a: (0 < a)%R; last have va_gt0: (0 < a^-1)%R by rewrite invr_gt0.
  by apply/(@ratR_lt0P R)/(ltR_trans (invR_gt0 lt0x)); rewrite -psi_le psi_rat.
rewrite -[a]invrK ratR_pinv ?leR_pinv2 //; last exact/ratR_lt0P.
rewrite -psi_rat psi_le -leR_pinv2 //; last exact/ratR_lt0P.
by apply: ltRW; rewrite -ratR_pinv // invrK -psi_le psi_rat.
Qed.

Let psi_inv x : x != 0 -> psi (Real.inv x) == Real.inv (psi x).
Proof.
move=> nz_x; have nz_psix: psi x != 0 by rewrite -psi_0 psi_eq.
rewrite -!invRE //; have [gt0x | /psi_pinv//] := ltR_total nz_x.
have lt0nx: - x > 0 by rewrite -oppR0 leR_opp2.
by apply: oppR_inj; rewrite -psi_opp -!invRN psi_pinv // psi_opp.
Qed.

Let psi_mul x y : psi (x * y) == psi x * psi y.
Proof.
without loss lt0x: x / x > 0.
  have [-> | ] := reals_classic R (x == 0); first by rewrite psi_0 !mul0R.
  case/ltR_total=> [gt0x | lt0x] IHx; last exact: IHx.
  by apply: oppR_inj; rewrite -!(mulNR, psi_opp) IHx // -oppR0 leR_opp2.
without loss lt0y: y / y > 0.
  have [-> | ] := reals_classic R (y == 0); first by rewrite psi_0 !mulR0.
  case/ltR_total=> [gt0y | lt0y] IHy; last exact: IHy.
  by apply: oppR_inj; rewrite -!(mulRN, psi_opp) IHy // -oppR0 leR_opp2.
wlog suffices IHxy: x y lt0x lt0y / psi (x * y) <= psi x * psi y.
  split; first exact: IHxy.
  have lt0psix: psi x > 0 by rewrite psi_ge0.
  rewrite -(leR_pmul2l _ _ (invR_gt0 lt0psix)) pmulKR //.
  rewrite -[y in psi y](pmulKR y lt0x) -psi_pinv //.
  by apply: IHxy; [apply: invR_gt0 | rewrite pmulR_rle0].
have [lt0psix lt0psiy]: psi x > 0 /\ psi y > 0  by rewrite !psi_ge0.
apply: psi_le_ub => _ [a lt_a_xy]; apply/ltRW.
have [/(@ratR_leP S)lea0 | lt0a] := lerP a 0.
  by apply/(leR_lt_trans lea0); rewrite pmulR_rle0.
have /ratR_dense[b lt_xa_b ltby]: x^-1 * ratR R a < y.
  by rewrite -(leR_pmul2l _ _ lt0x) mulRCA pmulKR.
have lt0Rb: 0 < ratR R b.
  by apply/(ltR_trans _ lt_xa_b)/mulR_gt0; [apply/invR_gt0 | apply/ratR_lt0P].
have lt0b: (0 < b)%R by apply/(@ratR_lt0P R).
have lt0Sb: 0 < ratR S b by apply/ratR_lt0P.
have lt_ab_x: ratR R (a / b) < x.
  rewrite -(leR_pmul2r _ _ lt0Rb) -ratRM divfK ?gt_eqF //.
  by rewrite -(pmulKR (ratR R a) lt0x) mulRCA leR_pmul2l.
suffices lt_a_psix_b: ratR S a < psi x * ratR S b.
  by apply: (ltR_trans lt_a_psix_b); rewrite leR_pmul2l // -psi_rat psi_le.
by rewrite -[a](@divfK _ b) ?gt_eqF // ratRM leR_pmul2r // -psi_rat psi_le.
Qed.

Let psi_sup E :
  Real.has_sup E -> psi (Real.sup E) == Real.sup (Real.image psi E).
Proof.
case=> hasE ubE; set F := Real.image psi E.
have [hasF ubF]: Real.has_sup F; last rewrite -!supRE //.
  split; first by have [x Ex] := hasE; exists (psi x), x.
  by have [z leEz] := ubE; exists (psi z) => _ [y Ey ->]; apply/psi_le/leEz.
split; last by apply/sup_sup=> // _ [x Ex ->]; apply/psi_le/sup_ub.
apply: psi_le_ub => _ [a lt_a_supE]; rewrite -psi_rat.
have [[x Ex /psi_le-leax] | //] := sup_total (ratR R a) hasE.
by apply/(leR_trans leax)/sup_ub; last exists x.
Qed.

Theorem Rmorph_toP : Real.morphism Rmorph_to. Proof. by []. Qed.

End CanonicalRealMorphism.

Theorem Rmorph_to_inv (R S : Real.model) x : Rmorph_to R (Rmorph_to S x) == x.
Proof.
apply: Rmorph_uniq (Rmorph_to R \o Rmorph_to S) idfun _ (Rmorph_id R) x.
by apply: Rmorph_comp; apply: Rmorph_toP.
Qed.

Theorem Rmorph_to_id (R : Real.model) x : Rmorph_to R x == x.
Proof. exact: Rmorph_uniq (Rmorph_toP R R) (Rmorph_id R) x. Qed.

End RealsCategorical.
