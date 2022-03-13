(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype tuple.
From mathcomp
Require Import path fingraph bigop order ssralg ssrnum ssrint div intdiv.
From fourcolor
Require Import hypermap geometry coloring grid matte.
From fourcolor
Require Import real realplane.
Require Import Setoid Morphisms.
From fourcolor
Require Import realsyntax realprop.

(******************************************************************************)
(*   Approximations of real scalars, points, regions and rectangles, used to  *)
(* cast the continuous four color problem into a combinatorial form.          *)
(*   Because the grid decomposition is based on dichotomy, we choose to       *)
(* approximate the real coordinates with binary decimals (i.e., floating      *)
(* point numbers), rather than arbitrary rationals.                           *)
(*   For a Real.model R, we define:                                           *)
(*          exp2R R s == 2 ^ s in R, for s : nat.                             *)
(*        scale R s m == m : int scaled back s, in R (i.e., m / 2 ^ s).       *)
(*  scale_point R s p == p : gpoint scaled back s, in point R.                *)
(*       approx s x m <-> m is the int approximation of x : R at scale s.     *)
(*                    := m <= x * 2 ^ s < m + 1.                              *)
(*  approx_point s z p <-> p : gpoint is the approximation of z : point R at  *)
(*                        scale s.                                            *)
(*   mem_approx s gr z <-> the approximation of z at scale s is in gregion gr *)
(*       scaled_rect R == the type of pairs of a natural integer scale and a  *)
(*                        grid rectangle. The phantom parameter R lets us     *)
(*                        coerce from scaled_rect R to a (rectangular) region *)
(*                        via mem_approx.                                     *)
(*    refine_srect s b == the scaled rectangle resulting from increasing the  *)
(*                        scale of b : scaled_rect by s while simultaneously  *)
(*                        scaling b's coordinates by s, so that b and         *)
(*                        refine_srect s b coerce to the same region.         *)
(*       inset_srect b == the scaled recangle inset one grid pixel from b;    *)
(*                        this insets the corresponding real region by        *)
(*                        1 / 2 ^ s on all sides.                             *)
(* cap_interval xz1 xz2 == the intersection of xz1 xz2 : interval R; this is  *)
(*                        a (possibly empty) interval.                        *)
(*      cap_rect r1 r2 == the rectangle intersection of r1 r2 : rectangle R.  *)
(*  sep_interval x1 x2 == a separating interval R containing x2 and NOT       *)
(*                        containing x1, provided x1 != x2.                   *)
(*      sep_rect z1 z2 == a separating rectangle R containing z2 : point R    *)
(*                        but not z1, unless z1 is extensionally equal to z2  *)
(*                        (belongs to the same regions).                      *)
(*      scaled_matte R == the type of pairs of a natural integer scale and a  *)
(*                        grid matte. The phantom parameter R lets us coerce  *)
(*                        from scaled_matte R to a (polygonal) region via     *)
(*                        mem_approx.                                         *)
(*   refine_smatte s m == the scaled matte resulting from increasing the      *)
(*                        scale of m : scaled_matte by s while simultaneously *)
(*                        scaling m's coordinates by s, so that m and         *)
(*                        refine_matte s m coerce to the same region.         *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory RealPlaneCoercions.

Definition scaled_rect (R : Real.model) : Type := nat * grect.
Definition scaled_matte (R : Real.model) : Type := nat * matte.

Section ApproxMap.

Open Scope real_scope.

Variable R : Real.model.
Implicit Types x y : R.

Local Notation Rstr := (Real.model_structure R).
Local Notation point := (point Rstr).
Local Notation region := (region Rstr).
Local Notation map := (map Rstr).
Local Notation interval := (interval Rstr).
Local Notation rectangle := (rectangle Rstr).
Local Coercion intRR := intR R.

Let ltR01 := ltR01 R.
Let ltR02 := ltR02 R.
Let ltR12 : 1 < 2 := @ltRS R 1.

(* Real powers of 2, for scaling approximations.                          *)

Definition exp2R s := intR R (2 ^ s)%N.

Lemma exp2RS s : exp2R s.+1 == 2 * exp2R s.
Proof. by rewrite /exp2R expnS PoszM intRM. Qed.

Lemma leR1exp2 s : 1 <= exp2R s.
Proof. by apply/(@intR_leP R 1); rewrite lez_nat expn_gt0. Qed.

Lemma ltR0exp2 s : 0 < exp2R s.
Proof. exact/(ltR_le_trans ltR01)/leR1exp2. Qed.
Arguments ltR0exp2 : clear implicits.
Hint Resolve ltR0exp2 : core.

Lemma exp2R_add s1 s2 : exp2R (s1 + s2) == exp2R s1 * exp2R s2.
Proof. by rewrite /exp2R expnD -intRM. Qed.

Lemma leRexp2 s1 s2 : (s1 <= s2)%N -> exp2R s1 <= exp2R s2.
Proof. by move=> le_s12; apply/intR_leP; rewrite lez_nat leq_exp2l. Qed.

Lemma ltR1exp2S s : 1 < exp2R s.+1.
Proof. by apply/(@intR_ltP R 1); rewrite lez_nat (leq_exp2l 1). Qed.
Arguments ltR1exp2S : clear implicits.

(* Scalar decimal approximation.                                       *)

Definition approx s x (m : int) := range1 m (exp2R s * x).

Instance approx_Proper : Proper (eq ==> Real.eq ==> eq ==> iff) approx.
Proof. by move=> _ s -> x y Dx  _ m ->; rewrite /approx Dx. Qed.

Lemma approx_inj s x m1 m2 : approx s x m1 -> approx s x m2 -> m1 = m2.
Proof. exact: range1z_inj. Qed.

Lemma approx_exists s x : exists m, approx s x m.
Proof. by apply: find_range1z. Qed.

Definition scale s (m : int) := m / exp2R s.

Lemma approx_scale s m : approx s (scale s m) m.
Proof.
by rewrite /approx /scale (mulRC m) mulRCA pmulKR //; apply: range1zz.
Qed.

Lemma approx_halfz s x m : approx s.+1 x m -> approx s x (m %/ 2)%Z%N.
Proof.
rewrite /approx exp2RS -mulRA [m : R]intR_addbit -/intRR modz2.
move: {s x}(_ * x) {m}(odd `|m|) (m %/ 2)%Z%N => x b m [Hxm Hmx].
split; rewrite -(leR_pmul2l _ _ ltR02).
  by apply: leR_trans Hxm; rewrite -subR_ge0 addRK; apply: leR0n.
apply: (ltR_le_trans Hmx); rewrite mulRDr mulR1 addRCA -addRA leR_add2r.
by apply/(@intR_leP R _ 1); rewrite lez_nat leq_b1.
Qed.

Lemma scale_exists x : x > 0 -> exists s, exp2R s * x > 1.
Proof.
move=> Hx; have [[s|s'] [_]] := find_range1z x^-1; last first.
  case; apply: ltRW; apply: leR_lt_trans (invR_gt0 Hx).
  by rewrite NegzE addRC intRN -leR_opp2 oppR0 oppRB -intRB1; apply: leR0n.
rewrite -intRS -/intRR -(leR_pmul2l _ _ Hx) (divRR (gtR_neq Hx)) mulRC => Hs.
exists s; apply: ltR_le_trans Hs _; rewrite leR_pmul2r {x Hx}//.
by apply/intR_leP; rewrite lez_nat ltn_expl.
Qed.

Lemma approx_between s x1 x2 m1 m2 :
   approx s.+1 x1 m1 -> approx s.+1 x2 m2 -> 1 < exp2R s * (x2 - x1) ->
  exists2 m, (m1 + 1 <= m)%R & (m + 1 <= m2)%R.
Proof.
have [m] := approx_exists s (x1 + x2); rewrite /approx exp2RS.
move: (exp2R s) => s2; set y := s2 * (x1 + x2); set z := s2 * (x2 - x1).
have ->: 2 * s2 * x1 == y - z.
  by rewrite -mulRA mulRCA mul2R -mulRN -mulRDr oppRD addRA addRK oppRK.
have ->: 2 * s2 * x2 == y + z.
  by rewrite -mulRA mulRCA -mulRDr (addRC (x1 + x2)) -addRA addKR mul2R.
case=> Hmy Hym [Hm1 _] [_ Hm2] Hz.
exists m; apply/(@intR_ltP R); rewrite -/intRR.
  apply: (leR_lt_trans Hm1); rewrite -(leR_add2r z) subRK.
  by apply: (ltR_trans Hym); rewrite leR_add2l.
apply: (leR_lt_trans Hmy); rewrite -(leR_add2r z).
by apply: (ltR_trans Hm2); rewrite leR_add2l.
Qed.

(* Geometrical binary approximation.                                   *)

Definition approx_point s (z : point) p :=
  let: Point x y := z in let: Gpoint mx my := p in
  approx s x mx /\ approx s y my.

Lemma approx_point_inj s z p1 p2 :
  approx_point s z p1 -> approx_point s z p2 -> p1 = p2.
Proof.
case: z p1 p2 => [x y] [mx1 my1] [mx2 my2] [Hx1 Hy1] [Hx2 Hy2].
by congr (Gpoint _ _); eapply approx_inj; eauto.
Qed.

Lemma approx_point_exists s z : exists p, approx_point s z p.
Proof.
case: z => x y.
have [[mx Hmx] [my Hmy]] := (approx_exists s x, approx_exists s y).
by exists (Gpoint mx my).
Qed.

Definition scale_point s p : point :=
  let: Gpoint mx my := p in Point (scale s mx) (scale s my).

Lemma approx_scale_point s p : approx_point s (scale_point s p) p.
Proof. by case: p => mx my; split; apply: approx_scale. Qed.

Lemma approx_halfg s z p : approx_point s.+1 z p -> approx_point s z (halfg p).
Proof. by case: z p => [x y] [mx my] [Hx Hy]; split; apply: approx_halfz. Qed.

Definition mem_approx s (gr : gregion) : region :=
  fun z => exists2 p, approx_point s z p & gr p.

Lemma sub_mem_approx s (gr1 gr2 : gregion) :
  subpred gr1 gr2 -> subregion (mem_approx s gr1) (mem_approx s gr2).
Proof. by move=> Hgr12 z [p Dp Hp]; exists p; auto. Qed.

Lemma mem_approx_scale s gr p :
  reflect (mem_approx s gr (scale_point s p)) (gr p).
Proof.
apply: (iffP idP) => [Hp | [p' Dp' Hp']].
  by exists p; first by apply approx_scale_point.
by rewrite (approx_point_inj (approx_scale_point _ _) Dp').
Qed.

Lemma eq_mem_approx s (gr1 gr2 : gregion) z :
  gr1 =1 gr2 -> (mem_approx s gr1 z <-> mem_approx s gr2 z).
Proof. by move=> Dgr; split; apply/sub_mem_approx=> p; rewrite Dgr. Qed.

Lemma mem_approx_refine s (gr : gregion) z :
  mem_approx s.+1 (preim halfg gr) z <-> mem_approx s gr z.
Proof.
split=> [] [p Dp Hp]; first by exists (halfg p); first apply/approx_halfg.
have [q Dq] := approx_point_exists s.+1 z; exists q => //=.
by rewrite (approx_point_inj (approx_halfg Dq) Dp).
Qed.

Lemma mem_approx_refine_inset s (b : grect) :
  subregion (mem_approx s (inset b)) (mem_approx s.+1 (inset (refine_rect b))).
Proof.
move=> z /mem_approx_refine[p Dp]; rewrite /= -in_refine_rect refine_inset.
by move/insetW; exists p.
Qed.

(* Scaled rectangle *)

Let srect := scaled_rect R.
Definition srect_region (b : srect) : region := mem_approx b.1 b.2.
Local Coercion srect_region : srect >-> region.

Definition refine_srect s (b : srect) : srect :=
  (s + b.1, iter s refine_rect b.2)%N.

Definition inset_srect (b : srect) : srect := (b.1, inset b.2).

Lemma in_refine_srect s b z : refine_srect s b z <-> b z.
Proof.
elim: s => // s <-; rewrite -[refine_srect s b z]mem_approx_refine.
by apply/eq_mem_approx=> t /=; rewrite in_refine_rect.
Qed.

Lemma in_refine_inset s b z :
  inset_srect b z -> inset_srect (refine_srect s b) z.
Proof. by elim: s => // s IHs /IHs; apply/mem_approx_refine_inset. Qed.

Lemma approx_rect z (r : rectangle) :
  r z -> exists2 b, inset_srect b z & subregion b r.
Proof.
case: z r => [x y] [[x0 x1] [y0 y1]] [[lbx ubx] [lby uby]].
pose i4 := @Ordinal 4; pose dxy := tnth [tuple x - x0; x1 - x; y - y0; y1 - y].
have{lbx ubx lby uby} [s scale_s_dxy]: exists s, forall i, 1 < exp2R s * dxy i.
  have dxy_gt0 i: 0 < dxy i by case: i; do 4?case=> [?|]; rewrite ?subR_le0.
  have /fin_all_exists[s lbs] i := scale_exists (dxy_gt0 i).
  exists (\max_i s i) => i.
  exact/(ltR_le_trans (lbs i))/leR_pmul2r/leRexp2/leq_bigmax.
pose s1 := s.+1; pose ap_s1 := approx s1; have es1gt0 := ltR0exp2 s1.
have [[mx Dmx] [my Dmy]] := (approx_exists s1 x, approx_exists s1 y).
have [[mx0 Dmx0] [mx1 Dmx1]] := (approx_exists s1 x0, approx_exists s1 x1).
have [[my0 Dmy0] [my1 Dmy1]] := (approx_exists s1 y0, approx_exists s1 y1).
have [nx0 lbx0 ubx0] := approx_between Dmx0 Dmx (scale_s_dxy (i4 0%N isT)).
have [nx1 lbx1 ubx1] := approx_between Dmx Dmx1 (scale_s_dxy (i4 1%N isT)).
have [ny0 lby0 uby0] := approx_between Dmy0 Dmy (scale_s_dxy (i4 2%N isT)).
have [ny1 lby1 uby1] := approx_between Dmy Dmy1 (scale_s_dxy (i4 3%N isT)).
exists (s1, Grect nx0 (nx1 + 1) ny0 (ny1 + 1)) => /=.
  by exists (Gpoint mx my); rewrite //= !addrK -!lez_addr1 ubx0 lbx1 uby0 lby1.
have lt_approx u v mu mv: ap_s1 u mu -> ap_s1 v mv -> (mu + 1 <= mv)%R -> u < v.
  case=> _ ubu [lbv _] ltuv; apply/(leR_pmul2l v u es1gt0)/(ltR_le_trans ubu).
  by apply: leR_trans lbv; rewrite -intRD1; apply/intR_leP.
case=> x2 y2 [[mx2 my2] [Dmx2 Dmy2]] /=; rewrite -andbA -!lez_addr1 => /and4P[].
move=> /(le_trans lbx0)/lt_approx-lbx /le_trans/(_ ubx1)/lt_approx-ubx.
move=> /(le_trans lby0)/lt_approx-lby /le_trans/(_ uby1)/lt_approx-uby.
by do 2!split; [apply/lbx | apply/ubx | apply/lby | apply/uby].
Qed.

Lemma rect_approx s z p (b_p : srect := (s, ltouch p)) :
  approx_point s z p -> exists2 r : rectangle, r z & subregion r b_p.
Proof.
case: z p => x y [mx my] in b_p * => -[[lbx ubx] [lby uby]].
have sXgt0: exp2R s > 0 by apply: ltR0exp2.
have sZK u: exp2R s * (u / exp2R s) == u by rewrite [u / _]mulRC mulRCA pmulKR.
pose step (m : int) := Interval ((m - 1)%R / exp2R s) ((m + 1)%R / exp2R s).
exists (Rectangle (step mx) (step my)) => [|[x1 y1] [[]]].
  split; split; rewrite -(leR_pmul2l _ _ sXgt0) sZK /intRR ?intRD1 //.
    by apply: ltR_le_trans lbx; apply/intR_ltP; rewrite subrK.
  by apply: ltR_le_trans lby; apply/intR_ltP; rewrite subrK.
rewrite -(leR_pmul2l _ x1 sXgt0) -(leR_pmul2l x1 _ sXgt0) !sZK => lbx1 ubx1 [].
rewrite -(leR_pmul2l _ y1 sXgt0) -(leR_pmul2l y1 _ sXgt0) !sZK => lby1 uby1.
have [p1 Dp1] := approx_point_exists s (Point x1 y1); exists p1 => //.
case: p1 Dp1 => [p1x p1y] [[ubp1x lbp1x] [ubp1y lbp1y]] /=.
rewrite -!(rwP andP) -!ltz_addr1 -!lez_addr1 -!(rwP (@intR_ltP R _ _)).
rewrite (intRD1 R p1x) (intRD1 R p1y)  -/intRR; split.
  by split; [apply: ltR_trans lbp1x | apply: leR_lt_trans ubx1].
by split; [apply: ltR_trans lbp1y | apply: leR_lt_trans uby1].
Qed.

(* Some rectangle operations.                                                 *)

Definition cap_interval (xz1 xz2 : interval) :=
  let: Interval x1 z1 := xz1 in let: Interval x2 z2 := xz2 in
  Interval (max x1 x2) (min z1 z2).

Lemma mem_cap_interval xz1 xz2 y : cap_interval xz1 xz2 y <-> xz1 y /\ xz2 y.
Proof.
by case: xz1 xz2 => x1 z1 [x2 z2] /=; rewrite ltR_max ltR_min; tauto.
Qed.

Definition cap_rect r1 r2 :=
  let: Rectangle w1 h1 := r1 in let: Rectangle w2 h2 := r2 in
  Rectangle (cap_interval w1 w2) (cap_interval h1 h2).

Lemma mem_cap_rect r1 r2 p : cap_rect r1 r2 p <-> r1 p /\ r2 p.
Proof.
by case: p r1 r2 => x y [w1 h1] [w2 h2] /=; rewrite !mem_cap_interval; tauto.
Qed.

Definition sep_interval x1 x2 :=
  let w := (x1 + x2) / 2 in
  Interval (IF x2 <= w then x2 - 1 else w) (IF x2 >= w then x2 + 1 else w).

Lemma mem_sep_interval x1 x2 : sep_interval x1 x2 x2.
Proof.
rewrite /sep_interval; move: {x1}(_ / 2) => y; split.
  by case: IFR_cases => _ [][lex2y ->] //; apply: ltPR.
by case: IFR_cases => _ [][leyx2 ->] //; apply: ltRS.
Qed.

Lemma meet_sep_interval x y t :
  sep_interval x y t -> sep_interval y x t -> x == y.
Proof.
without loss ltxy: x y / x < y.
  by move=> IHxy ? ?; have [|/ltR_total[]/IHxy->] := reals_classic R (x == y).
case; set u := (x + y) / 2 => /ltRW-lttu _ [_ []]; rewrite addRC.
suffices{lttu} [ltxu ltuy]: x < u < y by rewrite !IFR_else in lttu *.
have Du: 2 * u == x + y by rewrite [u]mulRC mulRCA pmulKR.
by split; rewrite -(leR_pmul2l _ _ ltR02) Du mul2R (leR_add2l, leR_add2r).
Qed.

Definition sep_rect z1 z2 :=
  let: Point x1 y1 := z1 in let: Point x2 y2 := z2 in
  Rectangle (sep_interval x1 x2) (sep_interval y1 y2).

Lemma mem_sep_rect z1 z2 : sep_rect z1 z2 z2.
Proof. by case: z1 z2 => [x1 y1] [x2 y2]; split; apply: mem_sep_interval. Qed.

Lemma meet_sep_rect z1 z2 :
    meet (sep_rect z1 z2) (sep_rect z2 z1) ->
  forall rr : rectangle, rr z1 -> rr z2.
Proof.
case: z1 z2 => x1 y1 [x2 y2] [[x y] [[x12x y12y] [x21x y21y]]] [[? ?] [? ?]] /=.
by rewrite (meet_sep_interval x12x x21x) (meet_sep_interval y12y y21y).
Qed.

(* Scaled matte *)

Let smatte := scaled_matte R.
Definition smatte_region (m : smatte) : region := mem_approx m.1 m.2.
Local Coercion smatte_region : smatte >-> region.

Definition refine_smatte s (m : smatte) : smatte :=
  (s + m.1, iter s refine_matte m.2)%N.

Lemma in_refine_smatte s (m : smatte) z : refine_smatte s m z <-> m z.
Proof.
elim: s => // s <-; rewrite -[refine_smatte s m z]mem_approx_refine.
by apply/eq_mem_approx=> t; rewrite /= in_refine_matte.
Qed.

End ApproxMap.

Coercion srect_region : scaled_rect >-> region.
Coercion smatte_region : scaled_matte >-> region.

