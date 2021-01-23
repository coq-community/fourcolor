(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat seq order ssralg ssrnum ssrint rat.
From fourcolor
Require Import real.
Require Import Setoid Morphisms.

(******************************************************************************)
(*   Construcion of the real numbers as a complete totally ordered field.     *)
(* We use the standard Dedekind cut construction, assuming only a classical   *)
(* excluded middle assumption. We repeat small parts of the generic theory of *)
(* reals (see realprop.v), e.g., the setoid structure, absolute values and    *)
(* definitions by cases, to aid in the definition of multiplication and       *)
(* inverse (the latter defined as a sup). Note that there are three kinds of  *)
(* comparisons involved in this construction:                                 *)
(*      (a < b)%R, (a <= b)%R : boolean comparison of rationals               *)
(*              x < a, x >= a : comparison of a rational a with a cut x.      *)
(*                              x >= a is notation for ~ (x < a).             *)
(*                     x <= y : cut comparison.                               *)
(* The rat >-> cut coercion we define is such that (a < b)%R and a < b are    *)
(* convertible. However a >= x and x <= a are equivalent but NOT convertible, *)
(* and neither are (a <= b)%R, a <= b, and b >= a.                            *)
(*   In addition to the comaprisons above we also define internally the usual *)
(* arithmetic operations (0, 1, +, *, -, ^-1) on cuts, along with             *)
(*             x == y, x != y : (setoid) cut (in)equality.                    *)
(*    `|x|, '|x|*|y|, `|x|^-1 : absolute value, producy, inverse of abs.      *)
(* Our main result is an opaque Dedekind.real : excluded_middle -> Real.model *)
(* theorem, which we also export in a transparent form Dedekind.model that    *)
(* exposes the cut construction.                                              *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Module Dedekind.

Section Construction.

(* Classical Prop. *)
Hypothesis classical : excluded_middle.
Lemma notK P : ~ ~ P <-> P. Proof. by case: (classical P); split=> // ? ?. Qed.

(* We use nontrivial open filters of rat to represent the reals. *)

Implicit Types a b c d e f g : rat.
Implicit Types m : int.
Implicit Types n i : nat.

(* Dedekind cuts. *)

Delimit Scope cut_scope with cut.
Open Scope cut_scope.

Notation "{ x | E }" := (fun x => E) : cut_scope.

Variant is_cut (X : rat -> Prop) : Prop :=
  IsCut (ub : exists a, X a)
        (lb : exists a, ~ X a)
        (filter : forall a b, X a -> (a < b)%R -> X b)
        (open : forall a, X a -> exists2 b, X b & (b < a)%R).

Record cut := Cut {ltc; _ : is_cut ltc}.
Arguments ltc : simpl never.

Implicit Types x y z : cut.
Implicit Types E F : cut -> Prop.

Bind Scope cut_scope with cut.

Lemma ltcE ltc_x x_cut : ltc (@Cut ltc_x x_cut) = ltc_x. Proof. by []. Qed.

Notation "x < a" := (ltc x a) : cut_scope.
Notation "x >= b" := (~ ltc x b)  : cut_scope.

Lemma ltcP x a : x < a \/ x >= a. Proof. exact: classical. Qed.

Lemma cut_ub x : exists a, x < a. Proof. by case: x => x []. Qed.

Lemma cut_lb x : exists b, x >= b. Proof. by case: x => x []. Qed.

Lemma ltc_trans x a b : x < a -> (a < b)%R -> x < b.
Proof. by case: x a b => x []. Qed.

Lemma open x a : x < a -> exists2 b, x < b & (b < a)%R.
Proof. by case: x a => x []. Qed.

Lemma ltc_le_trans x a b : x < a -> (a <= b)%R -> x < b.
Proof. by rewrite le_eqVlt => ltxa /predU1P[<-//| /(ltc_trans ltxa)]. Qed.

Lemma gec_lt_trans a x b : x >= a -> x < b -> (a < b)%R.
Proof. by case: ltrP => // /ltc_le_trans-leba leax /leba. Qed.

Lemma le_gec_trans a b x : (a <= b)%R -> x >= b -> x >= a.
Proof. by move=> leab lebx ltxa; apply: lebx (ltc_le_trans ltxa leab). Qed.

Lemma lt_gec_trans a b x : (a < b)%R -> x >= b -> x >= a.
Proof. by move/ltW; apply: le_gec_trans. Qed.

(* The preorder on cuts. *)

Definition leR x y := forall a, y < a -> x < a.

Notation "x <= y" := (leR x y) : cut_scope.

Definition eqR x y := x <= y /\ y <= x.

Notation "x == y" := (eqR x y) : cut_scope.
Notation "x != y" := (~ (x == y)) : cut_scope.

Lemma leRR x : x <= x. Proof. by []. Qed.
Arguments leRR x : clear implicits.

Lemma eqRR x : x == x. Proof. by split. Qed.
Hint Resolve leRR eqRR.

Lemma eqR_sym x y : x == y -> y == x. Proof. by case. Qed.

Lemma leR_ltc_trans x y a : x <= y -> y < a -> x < a.
Proof. exact. Qed.

Lemma gec_leR_trans a x y : x >= a -> x <= y -> y >= a.
Proof. by move=> leax lexy /lexy. Qed.

Lemma leR_trans x y z : x <= y -> y <= z -> x <= z.
Proof. by move=> le_xy le_yz a /le_yz/le_xy. Qed.

Lemma eqR_trans x y z : x == y -> y == z -> x == z.
Proof. by case=> lexy leyx [leyz lezy]; split=> a; auto. Qed.

Add Relation cut eqR
  reflexivity proved by eqRR
  symmetry proved by eqR_sym
  transitivity proved by eqR_trans
as eqR_setoid.

Instance ltc_Proper : Proper (eqR ==> eq ==> iff) ltc.
Proof. by move=> x y [lexy leyx] _ a ->; split=> [/leyx | /lexy]. Qed.

Instance leR_Proper : Proper (eqR ==> eqR ==> iff) leR.
Proof.
by move=> x1 x2 Dx y1 y2 Dy; split=> le_x a; have:= le_x a; rewrite Dx Dy.
Qed.

(* Embedding of Q. *)

Fact lt_is_cut a : is_cut {b | a < b}%R.
Proof.
split=> [||b c /lt_trans| b /midf_lt[ltac ltcb]]; last 2 [exact].
- by exists (a + 1)%R; rewrite ltr_addl.
- by exists a; rewrite ltxx.
by exists ((a + b) / 2%:R)%R.
Qed.

Coercion ratR a := Cut (lt_is_cut a).
Notation "0" := (ratR 0) : cut_scope.
Notation "1" := (ratR 1) : cut_scope.

Lemma leRq a x : x >= a <-> a <= x.
Proof. by split=> [/gec_lt_trans | leax /leax]; last rewrite ltcE ltxx. Qed.

Lemma ltcW a x : x < a -> x <= a. Proof. by move/ltc_trans. Qed.

(* Supremum definition and properties. *)

Definition has E := exists x, E x.

Definition ub E := {z | forall y, E y -> y <= z}.

Definition down E := {x | exists2 y, E y & x <= y}.

Definition has_sup E := has E /\ has (ub E).

Definition lt_sup E a := exists2 b, forall x, E x -> x < b & b < a.

Fact sup_is_cut E : is_cut {a | IF has_sup E then lt_sup E a else 0 < a}.
Proof.
split=> [||a b ltEa ltab| a].
- have [supE|] := classical (has_sup E); last by exists 1%R; right.
  have [_ [x ubEx]] := supE; have [a /open[b ltab ltbx]] := cut_ub x.
  by exists a; left; split; last by exists b => // y /ubEx/leR_ltc_trans; apply.
- have [supE|] := classical (has_sup E); last by exists 0%R => -[][].
  have [[y Ey] _] := supE; have [a leay] := cut_lb y.
  by exists a => -[][] // _ [b ltEb /lt_gec_trans/(_ leay)[]]; apply: ltEb.
- case: ltEa => -[supE ltEa]; last by right; rewrite ltcE (lt_trans ltEa).
  by have [c] := ltEa; left; split=> //; exists c; last apply: lt_trans ltab.
case=> -[supE]  => [supEa | /open[c]]; last by exists c; first right.
have [c ltEc /open[b ltcb ltba]] := supEa.
by exists b; first by left; split; last exists c.
Qed.

Definition sup E := Cut (sup_is_cut E).

Lemma sup_default E : ~ has_sup E -> sup E == 0.
Proof. by split=> [|a [] [] //]; right. Qed.

Instance sup_Proper : Proper (pointwise_relation cut iff ==> eqR) sup.
Proof.
move=> E F eqEF.
have eq_ub x: ub E x <-> ub F x by split=> ub_x y /eqEF/ub_x.
have eq_has_sup: has_sup E <-> has_sup F.
  by split=> -[[y /eqEF-Ey] [x /eq_ub-ubEx]]; (split; [exists y | exists x]).
have eq_sup a: lt_sup E a <-> lt_sup F a.
  by split=> -[b ltEb ltba]; exists b => // x /eqEF/ltEb.
have [supE | not_supE] := classical (has_sup E).
  by split=> a; rewrite !ltcE /IF_then_else eq_has_sup eq_sup.
by rewrite !sup_default // -eq_has_sup.
Qed.

Section SupProperties.

Variables (E : cut -> Prop) (x : cut).

Hypothesis has_supE : has_sup E.

Lemma sup_ub : ub E (sup E).
Proof. by move=> y Ey a [][]// _ [b ltEb]; apply/ltc_trans/ltEb. Qed.

Lemma sup_le_ub y : ub E y -> sup E <= y.
Proof.
by move=> ubEy a /open[b]; left; split; last by exists b => // z ?; apply: ubEy.
Qed.

Lemma sup_total : down E x \/ sup E <= x.
Proof.
have [|leEx] := classical (down E x); [by left | right].
apply: sup_le_ub => // y Ey a ltxa; apply/notK=> /leRq-leay; case: leEx.
by exists y => // b ltyb; apply/(ltc_trans ltxa)/(leR_ltc_trans leay).
Qed.

End SupProperties.

Lemma def_sup E x : E x -> ub E x -> sup E == x.
Proof.
move=> Ex ubEx; have supE: has_sup E by split; exists x.
by split; [apply: sup_le_ub | apply: sup_ub].
Qed.

(* Definition by cases *)

Section If.

Variables (P : Prop) (x1 x2 : cut).

Definition ifR := sup (fun x => IF P then x == x1 else x == x2).

Variant ifR_spec : cut -> Prop :=
  | IfR_true of  P & ifR == x1 : ifR_spec ifR
  | IfR_not of ~ P & ifR == x2 : ifR_spec ifR.

Lemma ifR_cases : ifR_spec ifR.
Proof.
have [haveP | notP] := classical P; [left | right] => //.
  by apply: def_sup => [|y []-[_ []] //]; left.
by apply: def_sup => [|y []-[_ [] //]]; right.
Qed.

End If.

Instance ifR_Proper : Proper (iff ==> eqR ==> eqR ==> eqR) ifR.
Proof.
rewrite /ifR /IF_then_else => P Q eqPQ x1 x2 Dx y1 y2 Dy.
by setoid_rewrite eqPQ; setoid_rewrite Dx; setoid_rewrite Dy.
Qed.

(* Opposite. *)

Definition opp_cut x := {a | exists2 b, (- a < b)%R & x >= b}.

Fact opp_is_cut x : is_cut (opp_cut x).
Proof.
split=> [||a b [c lt_na_c lecx] | a [b /(@open (- a)%R)[c lt_na_c ltcb] lebx]].
- by have [a leax] := cut_lb x; exists (1 - a)%R, a; rewrite // opprB gtr_addl.
- have [a ltxa] := cut_ub x; exists (- a)%R => -[b ltab []].
  by apply: ltc_trans ltab; rewrite opprK.
- by exists c; first by apply: lt_trans lt_na_c; rewrite ltr_opp2.
by exists (- c)%R; [exists b; rewrite ?opprK | rewrite ltr_oppl].
Qed.

Definition opp x := Cut (opp_is_cut x).
Notation "- x" := (opp x) : cut_scope.

Lemma leR_opp2 x y : x <= y -> - y <= - x.
Proof. by move=> lexy a [b ltab ltyb]; exists b => // /lexy. Qed.

Instance opp_Proper : Proper (eqR ==> eqR) opp.
Proof. by move=> x y []; split; apply: leR_opp2. Qed.

Lemma gec0_opp x : x < 0 -> - x >= 0.
Proof. by move=> ltx0 [a lt0a []]; apply: ltc_trans lt0a; rewrite oppr0. Qed.

Lemma opp_ind E :
  (forall x, E (- x) -> E x) -> (forall x, x >= 0 -> E x) -> forall x, E x.
Proof. by move=> IHopp IHpos x; case: (ltcP x 0) gec0_opp; auto. Qed.

Lemma oppK x : - (- x) == x.
Proof.
split=> [a /open[b ltxb ltba] | a [b lt_na_b le_b_nx]].
  by exists (- b)%R => [|[c]]; rewrite ?ltr_opp2 ?opprK => // /(ltc_trans ltxb).
by apply/notK=> leax; case: le_b_nx; exists a; rewrite // ltr_oppl.
Qed.

Lemma eqR_opp2 x y : opp x == opp y -> x == y.
Proof. by move=> eq_nx_ny; rewrite -(oppK x) eq_nx_ny oppK. Qed.

(* Absolute value *)

Definition abs_cut x := {a | x < a /\ - x < a}.

Definition abs_is_cut x : is_cut (abs_cut x).
Proof.
split=> [||a b [ltxa ltnxa] ltab | a [ltxa ltnxa]].
- have [[a ltxa] [b ltnxb]] := (cut_ub x, cut_ub (- x)).
  case: (ltrP b a); first by exists a; split; last apply: ltc_trans ltnxb _.
  by exists b; split; first apply: ltc_le_trans ltxa _.
- by exists 0%R => -[lt0x [a lt0a []]]; apply: ltc_trans lt0a; rewrite oppr0.
- by split; apply: ltc_trans ltab.
have [[b1 ltxb1 ltab1] [b2 ltnxb2 ltab2]] := (open ltxa, open ltnxa).
have [ltb21 | leb12] := ltrP b2 b1.
  by exists b1 => //; split; last apply: ltc_trans ltnxb2 _.
by exists b2 => //; split; first apply: ltc_le_trans ltxb1 _.
Qed.

Definition abs x := Cut (abs_is_cut x).
Local Notation "`| x |" := (abs x) : cut_scope.

Instance abs_Proper : Proper (eqR ==> eqR) abs.
Proof. by move=> x y Dx; split=> a; rewrite !ltcE /abs_cut Dx. Qed.

Lemma abs_ge0 x : 0 <= `|x|.
Proof.
by apply/leRq=> -[lt0x [a lt0a []]]; apply: ltc_trans lt0a; rewrite oppr0.
Qed.

Lemma ge0_abs x : x >= 0 -> `|x| == x.
Proof.
move=> le0x; split=> [a ltxa | a []//]; split=> //.
by exists 0%R; rewrite // oppr_lt0; apply/leRq: a ltxa.
Qed.

Lemma absN x : `|- x| == `|x|.
Proof. by split=> a; rewrite !ltcE /abs_cut oppK => -[]. Qed.

(* Addition. *)

Definition add_cut x y := {a | exists2 b, x < b & y < a - b}.

Fact add_is_cut x y : is_cut (add_cut x y).
Proof.
split=> [|| a b [c ltxc ltyac] ltab | a [b ltxb /open[c ltyc ltcab]]].
- have [[a ltxa] [b ltyb]] := (cut_ub x, cut_ub y).
  by exists (b + a)%R, a; rewrite ?addrK.
- have [[a leax] [b /leRq-leby]] := (cut_lb x, cut_lb y).
  exists (b + a)%R => -[c ltxc /leby].
  by rewrite ltcE ltr_subr_addr ltr_add2l => /(ltc_trans ltxc).
- by exists c => //; apply: ltc_trans ltyac _; rewrite ltr_add2r.
by exists (c + b)%R; [exists b; rewrite ?addrK | rewrite -ltr_subr_addr].

Qed.

Definition add x y := Cut (add_is_cut x y).
Infix "+" := add : cut_scope.
Notation "x - y" := (x + (- y)) : cut_scope.

Instance add_Proper : Proper (eqR ==> eqR ==> eqR) add.
Proof.
move=> x1 x2 Dx y1 y2 Dy.
by split=> b [a ltxa ltyba]; exists a; rewrite ?Dx ?Dy in ltxa ltyba *.
Qed.

Lemma add_monotony x y z : y <= z -> x + y <= x + z.
Proof. by move=> leyz b [a ltxa /leyz]; exists a. Qed.

Lemma addC x y : x + y == y + x.
Proof.
by split=> a [b ltxb ltyab]; exists (a - b)%R; rewrite // opprD addNKr opprK.
Qed.

Lemma addA x y z : x + (y + z) == x + y + z.
Proof.
wlog suffices: x y z / x + y + z <= x + (y + z).
  by split; rewrite // -!(addC z) !(addC x).
move=> c [a ltxa [b ltyb ltzc]]; exists (a + b)%R; last by rewrite opprD addrA.
by exists a; last rewrite addrC addKr.
Qed.

Lemma addN x : x - x == 0.
Proof.
apply eqR_sym; split=> [c [a ltxa [b lt_ac_b /leRq-lebx]] | d d_gt0].
  by rewrite ltcE -(ltr_addr (- a)) ltr_oppl (lt_trans lt_ac_b) ?lebx.
have [[a ltxa] [b lebx]] := (cut_ub x, cut_lb x).
have{a ltxa d_gt0} []: exists n, x < b + d *+ n.
  have ltab: (0 < a - b)%R by move/leRq in lebx; rewrite subr_gt0 lebx.
  pose c := ((a - b) / d)%R; have c_ge0: (0 <= c)%R by rewrite ltW // divr_gt0.
  exists `|numq c|%N; apply: ltc_le_trans ltxa _; rewrite -ler_subl_addl.
  rewrite pmulrn gez0_abs -?ge_rat0 // -mulrzl numqE mulrAC.
  by rewrite divfK ?gt_eqF ?ler_pmulr // ler1z -gtz0_ge1 denq_gt0.
elim=> [|n IHn]; rewrite ?addr0 // mulrSr => /open[a ltxa lt_a_dnd].
have [/IHn//| le_bdn_x] := classical (x < b + d *+ n).
by exists a => //; exists (b + d *+ n)%R; rewrite // opprB ltr_subl_addr -addrA.
Qed.

Lemma add0 x : 0 + x == x.
Proof.
split=> [a /open[b ltxb ltba] | a [b b_gt0] ltxab].
  by exists (a - b)%R; [rewrite ltcE subr_gt0 | rewrite opprD opprK addNKr].
by apply: ltc_trans ltxab _; rewrite gtr_addl oppr_lt0.
Qed.

Lemma opp0 : - 0 == 0. Proof. by rewrite -[opp 0]add0 addN. Qed.

Lemma oppD x y : - (x + y) == - x - y.
Proof. 
rewrite addC -[- x - y]add0 -(addN (y + x)) -addA [- _ + _]addC addA.
by rewrite -(addA y) (addA x) !(addN, add0).
Qed.

Lemma gec0N_eq0 x : x >= 0 -> - x >= 0 -> x == 0.
Proof. by move/leRq=> le0x /leRq/leR_opp2; rewrite oppK opp0. Qed.

(* Multiplication. *)

Definition amul_cut x y := {a | exists2 b, `|x| < b & `|y| < a / b}.

Fact amul_is_cut x y : is_cut (amul_cut x y).
Proof.
split=> [|| a b [c ltxc ltyac] ltab | a [b ltxb /open[c ltyc ltcab]]].
- have [[a ltxa] [b ltyb]] := (cut_ub `|x|, cut_ub `|y|).
  by exists (b * a)%R, a; rewrite ?mulfK ?gt_eqF // (abs_ge0 ltxa).
- by exists 0%R => -[a _ /abs_ge0]; rewrite mul0r ltcE ltxx.
- exists c => //; have c_gt0: 0 < c := abs_ge0 ltxc.
  by apply: ltc_trans ltyac _; rewrite ltr_pmul2r ?invr_gt0.
have b_gt0: 0 < b := abs_ge0 ltxb.
by exists (c * b)%R; first exists b; rewrite -?ltr_pdivl_mulr ?mulfK ?gt_eqF.
Qed.

Definition amul x y := Cut (amul_is_cut x y).
Notation "`| x |*| y |" := (amul x y)
  (at level 0, x, y at level 99, format "`| x |*| y |") : cut_scope.

Definition mul x y := ifR (x < 0 <-> y < 0) `|x|*|y| (- `|x|*|y|).
Infix "*" := mul : cut_scope.

Instance amul_Proper : Proper (eqR ==> eqR ==> eqR) amul.
Proof.
move=> x1 x2 Dx y1 y2 Dy.
by split=> b [a ltxa ltyba]; exists a; rewrite ?Dx ?Dy in ltxa ltyba *.
Qed.

Instance mul_Proper : Proper (eqR ==> eqR ==> eqR) mul.
Proof. by move=> x1 x2 Dx y1 y2 Dy; rewrite /mul Dx Dy. Qed.

Lemma amul_ge0 {x y} : `|x|*|y| >= 0.
Proof. by case=> a _ /abs_ge0; rewrite ltcE mul0r ltxx. Qed.

Lemma ge0_mul x y : x >= 0 -> y >= 0 -> x * y == `|x|*|y|.
Proof. by rewrite /mul => le0x le0y; case: ifR_cases => [|[]]. Qed.

Lemma amulC x y : `|x|*|y| == `|y|*|x|.
Proof.
without loss suffices: x y / `|y|*|x| <= `|x|*|y| by [].
move=> b [a ltxa ltyba]; exists (b / a)%R; rewrite // invf_div mulrC divfK //.
by rewrite gt_eqF // -(mul0r a) -ltr_pdivl_mulr (abs_ge0 ltxa, abs_ge0 ltyba).
Qed.

Lemma amulA x y z : `|x|*|`|y|*|z| | == `| `|x|*|y| |*|z|.
Proof.
without loss suffices: x y z / `| `|x|*|y| |*|z| <= `|x|*|`|y|*|z| |.
  by split=> //; rewrite !(amulC x) -!(amulC z).
move=> c [a ltxa [[b ltyb ltz_cab] _]]; have a_gt0: 0 < a := abs_ge0 ltxa.
exists (a * b)%R; last by rewrite invfM mulrA.
by rewrite (ge0_abs amul_ge0); exists a; rewrite //= mulrC mulKf ?gt_eqF.
Qed.

Lemma amul0 x : `|0|*|x| == 0.
Proof.
split=> [a a_gt0|]; last exact/leRq/amul_ge0.
have [b lexb] := cut_ub `|x|; have b_gt0 := abs_ge0 lexb.
exists (a / b)%R; first by rewrite ltcE /abs_cut opp0 ltcE divr_gt0.
by rewrite invfM invrK mulVKf ?gt_eqF.
Qed.

Lemma mulC x y : x * y == y * x.
Proof. by rewrite /mul [_ <-> _]and_comm amulC. Qed.

Lemma amulN x y : `|- x|*|y| == `|x|*|y|.
Proof. by split=> a [b]; do 2?[rewrite absN | exists b]. Qed.

Lemma mulNR x y : - x * y == - (x * y).
Proof.
elim/opp_ind: x => [x | x le0x]; first by rewrite oppK => ->; rewrite oppK.
rewrite /mul amulN; case: ifR_cases => le0nx ->; case: ifR_cases => gt0y ->;
  rewrite ?oppK // (gec0N_eq0 le0x) ?amul0 ?opp0 // ?le0nx -?gt0y // => gt0nx.
by case: gt0y; split=> // gt0y; case: le0nx.
Qed.

Lemma mulRN x y : x * - y == - (x * y).
Proof. by rewrite !(mulC x) mulNR. Qed.

Lemma mulA x y z : x * (y * z) == x * y * z.
Proof.
elim/opp_ind: x => [* | x le0x]; first by apply: eqR_opp2; rewrite -!mulNR.
elim/opp_ind: y => [y IHy | y le0y].
  by apply: eqR_opp2; rewrite -mulRN -mulNR IHy mulRN mulNR.
elim/opp_ind: z => [* | z le0z]; first by apply: eqR_opp2; rewrite -!mulRN.
by rewrite !ge0_mul ?amulA //; apply: amul_ge0.
Qed.

Lemma mulDr x y z : x * (y + z) == x * y + x * z.
Proof.
elim/opp_ind: x => [x IHx | x le0x].
  by apply/eqR_opp2; rewrite oppD -!mulNR IHx.
elim/opp_ind: y => [y IHy | y le0y] in z *.
  by apply/eqR_opp2; rewrite oppD -!mulRN oppD IHy.
without loss le0z: y z le0y / z >= 0.
  move=> IHz; have [/gec0_opp-le0nz | /(IHz y)->//] := ltcP z 0.
  move Dt: (y + z) => t; have{Dt} Dt: y + z == t by rewrite Dt.
  elim/opp_ind: t => [t IHt | t le0t] in y z Dt le0y le0nz *.
    by apply/eqR_opp2; rewrite oppD -!mulRN addC -IHt ?oppK // addC -oppD Dt.
  rewrite -(add0 (x * t)) -(addN (x * z)) -mulRN -addA -{}IHz //.
  by rewrite addC -Dt (addC y) addA -(addC z) addN add0.
have [/leRq-leR0y /leRq-leR0z] := (le0y, le0z).
have le0yz: y + z >= 0 by move/(add_monotony leR0z); rewrite addC add0.
rewrite !ge0_mul //; symmetry; split=> [c [a ltxa] | c [d [a1 ltxa1]]].
  rewrite ge0_abs // => -[b ltyb ltz_cab]; have a_gt0 := abs_ge0 ltxa.
  exists (b * a)%R, a => //; first by rewrite mulfK ?gt_eqF // ge0_abs.
  by rewrite mulrBl mulfK ?gt_eqF // ge0_abs.
rewrite ge0_abs // => lty_da1 [a2]; rewrite (ge0_abs le0z) // => ltxa2 ltz_cda2.
have [a ltxa [lea1 lea2]]: exists2 a, `|x| < a & (a <= a1)%R /\ (a <= a2)%R.
  exists (Num.min a1 a2); first by rewrite fun_if; case: ifP.
  by apply/andP; rewrite -lexI.
have [[a_gt0 a1_gt0] a2_gt0] := (abs_ge0 ltxa, abs_ge0 ltxa1, abs_ge0 ltxa2). 
have dgt0: 0 < d by move/leR0y: lty_da1; rewrite ltcE pmulr_lgt0 ?invr_gt0.
have cdgt0: 0 < c - d.
  by move/leR0z: ltz_cda2; rewrite ltcE pmulr_lgt0 ?invr_gt0.
exists a; rewrite // (ge0_abs le0yz); exists (d / a)%R; last rewrite -mulrBl.
  by apply: ltc_le_trans lty_da1 _; rewrite ler_pmul2l ?lef_pinv.
by apply: ltc_le_trans ltz_cda2 _; rewrite ler_pmul2l ?lef_pinv.
Qed.

Lemma mul1 x : 1 * x == x.
Proof.
elim/opp_ind: x => [x IHx | x le0x].
  by apply eqR_opp2; rewrite -IHx mulRN.
rewrite ge0_mul //; split=> [b /open[a ltxa ltab] | b [a [lt1a _] ltxba]].
  have a_gt0: 0 < a by apply/leRq: (a) ltxa.
  by rewrite amulC; exists a; rewrite ge0_abs // ltcE ltr_pdivl_mulr ?mul1r.
have a_gt0: 0 < a by apply: lt_trans lt1a.
have b_gt0: 0 < b by rewrite ltcE -(mul0r a) -ltr_pdivl_mulr ?(abs_ge0 ltxba).
rewrite -[x]ge0_abs //; apply: ltc_trans ltxba _.
by rewrite gtr_pmulr ?invf_lt1.
Qed.

Lemma mul_monotony x y z : 0 <= x -> y <= z -> x * y <= x * z.
Proof.
move=> le0x leyz; set xy := mul x y; pose t := add (- y) z.
have le0t: 0 <= t by rewrite -(addN y) addC; apply: add_monotony.
rewrite -(add0 z) -(addN y) -addA -/t mulDr -[xy]add0 addC -/xy.
by rewrite ge0_mul => [|/le0x|/le0t] //; apply/add_monotony/leRq/amul_ge0.
Qed.

(* Inverse. *)

Definition ainv x := sup {y | `|x|*|y| < 1}.
Notation "`| x |^-1" := (ainv x)
  (at level 0, x at level 99, format "`| x |^-1") : cut_scope.
Definition inv x := ifR (x < 0) (- `|x|^-1) `|x|^-1.
Notation "x ^-1" := (inv x) : cut_scope.

Instance ainv_Proper : Proper (eqR ==> eqR) ainv.
Proof. by move=> x y Dx; rewrite /ainv; setoid_rewrite Dx. Qed.

Instance inv_Proper : Proper (eqR ==> eqR) inv.
Proof. by move=> x y Dx; rewrite /inv Dx. Qed.

Lemma ainv0 : ainv 0 == 0.
Proof.
apply: sup_default => -[_ [z ub_z]].
by have [a /notK[]] := cut_ub z; apply/leRq/ub_z; rewrite amul0.
Qed.

Lemma invN x : (- x)^-1 == - x^-1.
Proof.
rewrite /inv /`|_|^-1; setoid_rewrite amulN; rewrite -/`|x|^-1.
have [/gec0_opp-le0nx -> | le0x ->] := ifR_cases (x < 0).
  by rewrite oppK; case: ifR_cases.
by case: ifR_cases => // /(gec0N_eq0 le0x)-> ->; rewrite ainv0 opp0.
Qed.

Lemma mulV x : x != 0 -> x * x^-1 == 1.
Proof.
elim/opp_ind: x => [x IHx | x le0x] nz_x.
  by rewrite -(oppK x^-1) -invN mulRN -mulNR IHx // -opp0 => /eqR_opp2.
rewrite /inv; set y := `|x|^-1; case: ifR_cases => // _ ->.
have{nz_x} [a lt0a leax]: exists2 a, 0 < a & x >= a.
  by have [[a] | /(gec0N_eq0 le0x)//] := ltcP (- x) 0; rewrite oppr0; exists a.
pose E z := `|x|*|z| < 1; have E_0: E 0 by rewrite /E amulC amul0.
have supE: has_sup E.
  split; [by exists 0 | exists a^-1%R => //].
  move=> z [b ltxb [lt_z_vb _]]; apply/ltcW/(ltc_trans lt_z_vb).
  by rewrite mul1r (ltf_pinv (abs_ge0 ltxb)) ?(gec_lt_trans _ ltxb) // => -[].
have ubEy: ub E y by apply: sup_ub.
have le0y: y >= 0 by apply/leRq/ubEy.
rewrite ge0_mul //; split=> [b lt1b | b [c ltxc [ltybc _]]]; last first.
  have [d ltxd ltdc] := open ltxc.
  have [c_gt0 d_gt0] := (abs_ge0 ltxc, abs_ge0 ltxd).
  suffices: (1 / c < b / c)%R by rewrite ltr_pmul2r ?invr_gt0.
  apply: gec_lt_trans ltybc; apply/leRq/ubEy; exists d => //.
  by rewrite !mul1r ge0_abs ltcE ?ltf_pinv // lt_gtF ?invr_gt0.
have lt0b: 0 < b by apply: lt_trans lt1b.
pose e := (1 - b^-1)%R; have lt0e: 0 < e by rewrite ltcE subr_gt0 invf_lt1.
have [c ltxc [d lt_cea_d ledx]]: x - x < a * e by rewrite addN ltcE mulr_gt0.
have ltac: a < c := gec_lt_trans leax ltxc.
have lt0c: 0 < c := lt_trans lt0a ltac.
have lt0d: 0 < d.
  apply: lt_trans lt_cea_d; rewrite opprB subr_gt0 mulrBr mulr1.
  by rewrite ltr_snsaddr // oppr_lt0 divr_gt0.
have le_y_vd: y <= d^-1%R.
  apply/sup_le_ub=> // z -[f ltxf [lt_z_vf _]]; apply/ltcW/(ltc_trans lt_z_vf).
  by rewrite mul1r (ltf_pinv (abs_ge0 ltxf)) ?(gec_lt_trans _ ltxf) // => -[].
exists c; rewrite ge0_abs //; apply: le_y_vd; rewrite ltcE.
rewrite -invf_div ltf_pinv ?rpred_div //; apply: lt_trans lt_cea_d.
by rewrite ltr_oppr -[c in (_ - c)%R]mulr1 ltr_subl_addl -mulrBr ltr_pmul2r.
Qed.

Definition structure := Real.Structure leR sup add 0 opp mul 1 inv.

Lemma axioms : Real.axioms structure.
Proof.
move: leRR leR_trans sup_ub sup_total add_monotony addC addA add0 addN.
by move: mul_monotony mulC mulA mulDr mul1 mulV; split=> //= -[/leRq[]].
Qed.

Definition model := Real.Model axioms.

End Construction.

Theorem real : excluded_middle -> Real.model. Proof. exact: model. Qed.

End Dedekind.
