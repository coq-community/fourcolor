(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype path fingraph bigop ssralg ssrnum ssrint.
From mathcomp Require Import div intdiv.
From fourcolor Require Import hypermap geometry coloring grid matte gridmap.
From fourcolor Require Import real realplane realprop approx.

(******************************************************************************)
(* Discretizing the coloring problem for an arbitrary finite map. We compute  *)
(* a finite hypermap whose colorings induce colorings of the map, using the   *)
(* grid computation package.                                                  *)
(* The discrete approximation is constructed in five steps :                  *)
(* 1) Enumerate the regions and adjacencies of m0, choosing a representative  *)
(*    border point for each adjacency.                                        *)
(* 2) Construct disjoint rectangles covering the border points.               *)
(* 3) Construct approximations of the border rectangles.                      *)
(* 4) Construct matte approximations of the regions that meet all the         *)
(*    corresponding border rectangles.                                        *)
(* 5) Construct a hypermap from the mattes using the gridmap library.         *)
(* Assuming a real model R and a finite simple map m0 in the R plane we       *)
(* define the following:                                                      *)
(*    map_repr n == representation type for n-region transversals for m0.     *)
(*               := 'I_n -> point R                                           *)
(*  mr_proper mr <-> mr is a proper transversal, mapping different indices in *)
(*                  'I_r to points in different regions of m0.                *)
(*   mr_cover mr <-> the transversal mr covers all the regions on m0.         *)
(* Now assuming a transversal mr : map_repr Nr for some Nr : nat, we then     *)
(* define:                                                                    *)
(*   ab_mr_proper b e i <-> if the grect component of the scaled_rect b       *)
(*                   witnesses adjacency at e : adj_index Nr, then the region *)
(*                   of m0 containing mr i meets inset_srect b if i is one of *)
(*                   the components of e, and altogether disjoint from b      *)
(*                   otherwise. Thus if this holds for all i, b properly      *)
(*                   witnesses an m0 adjacency at e.                          *)
(*   proper_smatte ab m i E <-> m is a scaled matte approximation of the m0   *)
(*                   region containing mr i: m is included in this region,    *)
(*                   and meets inset_srect (ab e) for all e in E.             *)
(* Scaled mattes satisfying this latter predicate are built up from a pixel   *)
(* matte around mr i, using the connectedness of the surrounding m0 region to *)
(* find a a larger interpolating matte contained in that region, that meets   *)
(* ab e for some e in E.                                                      *)
(*   interpolant_at z U V W <-> region W interpolates between {z} u U and V.  *)
(*   smatte_interpolated U V == the region that is the union of all scaled    *)
(*                   mattes W interpolating between regions U and V.          *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Num.Def RealCoercions RealPlaneCoercions.

Section DiscretizeMap.

Variable R : Real.model.

Local Notation Rt := (Real.model_structure R) (only parsing).
Local Notation point := (point Rt).
Local Notation region := (region Rt).
Local Notation map := (map Rt).
Local Notation rect := (rectangle Rt).
Local Notation interval := (interval Rt).

Local Notation srect := (scaled_rect R).
Local Notation smatte := (scaled_matte R).

Let Rclassic : excluded_middle := reals_classic R.

Variable m0 : map.
Hypothesis fin_m0 : finite_simple_map m0.
Local Notation m0sym := (map_sym fin_m0).
Local Notation m0tr := (map_trans fin_m0).

Definition map_repr n := 'I_n -> point.

Definition mr_proper n (mr : map_repr n) :=
  forall i, cover m0 (mr i) /\ (forall j, m0 (mr i) (mr j) -> i = j).

Definition mr_cover n (mr : map_repr n) : region :=
  fun z => exists i, m0 (mr i) z.

Lemma exists_map_repr : exists n, exists2 mr : map_repr n,
  mr_proper mr & subregion (cover m0) (mr_cover mr).
Proof.
have [_ [k [mr0 sm0r0]]] := fin_m0; pose mr0k : map_repr k := mr0.
suffices{sm0r0} [n [mr mrP sr0mr]]: exists n, exists2 mr : map_repr n,
  mr_proper mr & subregion (mr_cover mr0k) (mr_cover mr).
- by exists n, mr => // z /sm0r0[i /ltP-lti ?]; apply/sr0mr; exists (Sub i lti).
elim: k @mr0k => [|k [n [mr mrP]] sr0mr]; last pose t := mr0 k.
  by exists 0, (fun=> mr0 0) => [|z []] [].
have [mr_t | mr't] := Rclassic (cover m0 t -> mr_cover mr t).
  exists n, mr => // z [j]; have{j} [j -> m0jz | -> m0tz] := unliftP ord_max j.
    by rewrite lift_max in m0jz; apply/sr0mr; exists j.
  have [i m0it]: mr_cover mr t by apply/mr_t/(m0tr m0tz)/m0sym.
  by exists i; apply/(m0tr m0it).
exists n.+1, [fun i => oapp mr t (unlift ord0 i)] => [i1 | z [j]] /=.
  case: unliftP => [i|] -> {i1}/=.
    have [m0i Imr_i] := mrP i; split=> {m0i}// j1.
    by case: unliftP => [j -> /Imr_i|] -> //= m0it; case: mr't; exists i.
  split=> [|j1]; first by case: (Rclassic (cover m0 t)) mr't => // m0't [].
  by case: unliftP => //= j _ /m0sym-m0jt; case: mr't; exists j.
have{j} [j -> m0jz | -> /= m0tz] := unliftP ord_max j; last first.
  by exists ord0; rewrite /= unlift_none.
suffices [i m0iz]: mr_cover mr z by exists (lift ord0 i); rewrite /= liftK.
by rewrite lift_max in m0jz; apply/sr0mr; exists j.
Qed.

Section AdjRepr.

Variables (Nr : nat) (mr : map_repr Nr).
Hypothesis mrP : mr_proper mr.

Local Notation Ir := 'I_Nr.
Local Notation Er := (adj_index Nr).
Implicit Types (i j : Ir) (e f : Er).

Definition ab_mr_proper (b : srect) e i :=
  gr_proper b.2 -> let m0i := m0 (mr i) in
  [/\ i \in e -> meet (inset_srect b) m0i & meet b m0i -> i \in e].

Lemma ab_mr_proper_refine s b e i :
  ab_mr_proper b e i -> ab_mr_proper (refine_srect s b) e i.
Proof.
rewrite /ab_mr_proper gr_proper_refine => beiP /beiP{beiP}[ei_b b_ei].
split=> [/ei_b|] [z []]; first by exists z; split; first apply/in_refine_inset.
by move/in_refine_srect=> b_z m0i_z; apply/b_ei; exists z.
Qed.

Let mr_adj (e : Er) := adjacent m0 (mr e.1) (mr e.2) /\ e.1 < e.2.

Lemma exists_adjbox :
  exists ab,
    [/\ ab_proper ab, exists s, forall e i, ab_mr_proper (s, ab e) e i
      & forall e, mr_adj e -> gr_proper (ab e)].
Proof.
have /fin_all_exists[is_arc arcP] e: exists is_arc : bool, mr_adj e <-> is_arc.
  by have [] := Rclassic (mr_adj e); [exists true | exists false].
pose arc := {e : Er | is_arc e}; pose v (a : arc) := sval a.
pose a_adj a := meet (not_corner m0) (border m0 (mr (v a).1) (mr (v a).2)).
have{a_adj}/fin_all_exists[/= ap apP] a: a_adj a by have /arcP[[]] := valP a.
pose cl i := closure (m0 (mr i)).
pose cl_a a (r : rect) i := meet r (cl i) -> i \in v a.
pose has_ar0 a := exists2 ar0, forall i, cl_a a ar0 i & ar0 (ap a).
have{has_ar0} /fin_all_exists2[ar0 ar0a ar0p] a: has_ar0 a.
  have [ar0 ar0p]: exists ar0 : rect, ar0 (ap a).
    by exists (sep_rect (ap a) (ap a)); apply: mem_sep_rect.
  have /fin_all_exists2[ar ar_a ar_p] i: exists2 ar, cl_a a ar i & ar (ap a).
    have [a_i | a'i] := boolP (i \in v a); first by exists ar0.
    have [//|no_ar] := Rclassic (exists2 ar, cl_a a ar i & ar (ap a)).
    have{no_ar} cl_i_e: cl i (ap a).
      move=> U openU /openU[ar ar_e Uar].
      have [//|m0i'U] := Rclassic (meet (m0 (mr i)) U); case: no_ar.
      by exists ar => // -[z [ar_z /(_ U _ _)/m0i'U[]//]]; apply: Uar.
    pose J := [:: i; (v a).1; (v a).2]; have [[me meP] [apPa1 apPa2]] := apP a.
    have /fin_all_exists[k kP] j: exists k : 'I_2, j \in J -> m0 (me k) (mr j).
      case Jj: (j \in J); last by exists ord0.
      have [|k /ltP-ltk2 []] := meP (mr j); last by exists (Ordinal ltk2).
      by split; [have [] := mrP j | have:= Jj; rewrite !inE => /or3P[]/eqP->].
    have{me meP kP} inj_k: {in J &, injective k}.
      move=> j1 j2 /kP-m0mj1 /kP-m0mj2 Dkj.
      by have [_] := mrP j1; apply; apply/(m0tr _ m0mj2)/m0sym; rewrite -Dkj.
    have [/arcP[_ lta] /idPn[]] := (valP a, max_card (mem [seq k j | j in J])).
    by rewrite card_ord card_in_image ?(card_uniqP _) //= !inE a'i neq_ltn lta.
  exists (\big[(@cap_rect R)/ar0]_(i | i \notin v a) ar i) => [i|]; last first.
    by elim/big_rec: _ => // j r _ r_a; apply/mem_cap_rect.
  rewrite -big_filter; set I := filter _ _ => -[z [ar_z cli_z]].
  have [ari_z | ari'z] := Rclassic (ar i z); first by apply/ar_a; exists z.
  suffices: i \notin I by rewrite mem_enum negbK.
  elim: I ar_z => // j I IH; rewrite big_cons => /mem_cap_rect[clj_z /IH-a'i].
  by rewrite inE; case: eqP ari'z => // ->.
pose ar1 a b := sep_rect (ap a) (ap b).
have ar1_inj a b: meet (ar1 a b) (ar1 b a) -> a = b.
  move/meet_sep_rect/(_ _ (ar0p a))=> ar0ab; apply/esym/eqP/andP.
  have a_clb i: cl i (ap b) -> i \in v a.
   by move=> cli_b; apply/ar0a; exists (ap b).
  have [/arcP[_ lta] /arcP[_ ltb]] := (valP a, valP b).
  have [_ [_ /a_clb/orP[/idPn[] | Df2]]] := apP b.
    rewrite neq_ltn orbC (leq_ltn_trans _ ltb) // /v.
    by have [_ [/a_clb/pred2P[]->] _ //] := apP b; apply: ltnW.
  by have [_ [/a_clb/orP[//|/idPn[]]]] := apP b; rewrite neq_ltn -(eqP Df2) ltb.
pose ar a := \big[@cap_rect R/ar0 a]_b ar1 b a.
have ar_p a: ar a (ap a).
  rewrite /ar; elim/big_rec: _ => // b r _ r_a.
  by apply/mem_cap_rect; split; first apply: mem_sep_rect.
have ar_a a i: cl_a a (ar a) i.
  rewrite /ar; elim/big_rec: _ => // b r _ r_b [z [/mem_cap_rect[_ r_z] i_z]].
  by apply/r_b; exists z.
have ar1ar a b: subregion (ar a) (ar1 b a).
  rewrite /ar -big_filter; set B := filter _ _ => z.
  have: b \in B by rewrite mem_enum.
  elim: B => //= c B IH_B; rewrite inE big_cons => cBb /mem_cap_rect[].
  by case/predU1P: cBb => [-> | Bb _ /(IH_B Bb)].
have{ar1_inj ar1ar} ar_inj a b: meet (ar a) (ar b) -> a = b.
  by case=> z [a_z b_z]; apply/ar1_inj; exists z; split; apply/ar1ar.
have /fin_all_exists2[ab0 ab0ap ar_ab] a := approx_rect (ar_p a).
pose r0 := Grect 1 0 1 0; have not_r0 p: ~~ r0 p by case: p => -[[]|].
pose s := \sum_a (ab0 a).1; pose s_ a := \sum_(b | b != a) (ab0 b).1.
have Ds a: s = s_ a + (ab0 a).1 by rewrite addnC [s](bigD1 a).
pose ab_ a := refine_srect (s_ a).+1 (ab0 a).
exists (fun e => if insub e is Some e then (ab_ e).2 else r0).
have {}ar_ab a z: ab_ a z -> ar a z by move/in_refine_srect/ar_ab.
split=> [e f p | | e [adj_e lte]]; last 1 first.
- have [a _ _|/negP[]] := insubP; last exact/arcP.
  have [p _ /insetW-ab0a_p] := ab0ap a.
  by rewrite gr_proper_refine; apply/gr_properP; exists p.
- have [a _ <- /= a_p | _ /idPn[]//] := insubP.
  have [b _ <- /= b_p | _ /idPn[]//] := insubP.
  rewrite (ar_inj a b) //; exists (scale_point R s.+1 p); split; apply/ar_ab.
    by rewrite (Ds a) -addSn; apply/mem_approx_scale.
  by rewrite (Ds b) -addSn; apply/mem_approx_scale.
exists s.+1 => e i; case: insubP => //= a _ Da _; rewrite /= (Ds a) -addSn.
split=> [e_i | [z [/ar_ab-a_z m0i_z]]]; last first.
  by rewrite -Da; apply/ar_a; exists z; split; last exists z.
have{e_i} cli_a: cl i (ap a).
  by have [_ []] := apP a; rewrite /v Da; case/pred2P: e_i => ->.
have /(in_refine_srect 1)[p /rect_approx[r r_a p_r] a_p] := ab0ap a.
have{r_a} /cli_a[|z [m0iz r_z]] := r_a; first by exists r.
suffices /(in_refine_inset (s_ a)): inset_srect (refine_srect 1 (ab0 a)) z.
  by rewrite /(srect_region _ z) /= -iterSr addnS; exists z.
apply: sub_mem_approx (p_r z r_z)=> q /gtouch_l; apply/insetP: q.
by rewrite -refine_inset.
Qed.

Definition interpolant_at z (U V W : region) :=
  [/\ W z, subregion U W & subregion W V].

Definition smatte_interpolated (U V : region) z :=
  exists m : smatte, interpolant_at z U V m.

Lemma refine_smatte_interpolant s (U V : region) (m : smatte) z :
  interpolant_at z U V m -> interpolant_at z U V (refine_smatte s m).
Proof.
case=> mz mU Vm; split=> [|t /mU-mt|t]; try exact/in_refine_smatte.
by move/in_refine_smatte/Vm.
Qed.

Lemma connected_matte (U : region) (m : smatte) :
    open U -> connected U -> subregion m U ->
  subregion U (smatte_interpolated m U).
Proof.
move=> Uopen Uconnected Um.
set U1 := smatte_interpolated m U; pose U2 z := U z /\ ~ U1 z.
have U12_U: subregion U (union U1 U2).
  by move=> z; case: (Rclassic (U1 z)); [left | right].
have U1_U: meet U1 U.
  suffices [z m_z]: {p | m p} by exists z; split; [exists m; split | apply/Um].
  case: (m) => s [[|p] //=].
  by exists (scale_point R s p); apply/mem_approx_scale/mem_head.
have U1open: open U1.
  move=> z [m1 m1z]; pose inrU b z := inset_srect b z /\ subregion b U.
  pose s := m1.1; without loss m1_Uz: m1 @s m1z / exists2 b, inrU b z & b.1 = s.
    have{m1z} [m1z m1m Um1] := m1z; have /Uopen[r r_z Ur] := Um1 z m1z.
    have [b1 b1z r_b1] := approx_rect r_z => /(_ (refine_smatte b1.1 m1)).
    apply; first exact/refine_smatte_interpolant.
    exists (refine_srect s b1); last exact: addnC.
    by split=> [|t /in_refine_srect/r_b1/Ur//]; apply/in_refine_inset.
  have [n]: exists n, mem_approx s [pred p in m1.2 | mcorner m1.2 p < n] z.
    by have [[p]] := m1z; exists (mcorner m1.2 p).+1, p; last apply/andP.
  elim: n => [|n IHn] in m1 s m1_Uz m1z * => -[p Dp /andP[m1p m1n_p]] //.
  have{m1_Uz m1z} [[b [b_z Ub] Db1] [m1z m1m Um1]] := (m1_Uz, m1z).
  have [p_inner | p_corner] := posnP (mcorner m1.2 p).
    have{m1n_p Dp} [r r_z p_r] := rect_approx Dp; exists r => // t /p_r-r_t.
    by exists m1; split; first apply/(sub_mem_approx _ r_t)/mcorner0.
  have b_p: inset b.2 p.
    by case: b_z => q; rewrite /= Db1 => /(approx_point_inj Dp)<-.
  have [p2 Dp2] := approx_point_exists s.+1 z.
  have Ep2: halfg p2 = p by apply/(approx_point_inj _ Dp)/approx_halfg.
  have [|||m2 []] := @refine_mcorner m1.2 b.2 p2; rewrite Ep2 //.
  move=> m2m1 bm1m2 ltm; have m2p2: p2 \in m2 by rewrite m2m1 // inE Ep2.
  apply: (IHn (s.+1, m2)); last by exists p2; rewrite //= m2p2 (leq_trans ltm).
    exists (refine_srect 1 b); last by rewrite /= Db1.
    by split=> [|t bt]; [apply/in_refine_inset | apply/Ub/(in_refine_srect 1)].
  split=> [|t /m1m/(in_refine_smatte 1) | t]; first by exists p2.
    by apply: sub_mem_approx t => q; rewrite /= in_refine_matte => /m2m1.
  case=> q2 /approx_halfg-Dq /bm1m2; rewrite !inE; set q := halfg q2 in Dq *.
  by case/orP=> [b_q | m1q]; [apply/Ub | apply/Um1]; exists q; rewrite // Db1.
suffices{U1open} U2open: open U2.
  move=> z Uz; have /U12_U[// | U2z] := Uz.
  by have [] := Uconnected U1 U2 => // [|t [U1t [_ []]//]]; exists z; split.
move=> z [/Uopen[r /approx_rect[b b_z r_b] Ur] U1'z].
suffices b'U1: ~ meet b U1.
  have [p /rect_approx[rp rp_z p_rp] b_p] := b_z; exists rp => // t /p_rp-p_t.
  have b_t: b t by apply: sub_mem_approx t p_t => q /gtouch_l/(insetP b_p).
  by split=> [|U1t]; [apply/Ur/r_b | have [] := b'U1; exists t].
case=> t [b_t [m1]]; move: r_b b_z b_t.
without loss: b m1 / b.1 = m1.1 /\ coarse_in b.2 m1.2.
  pose b2 := refine_srect m1.1.+1 b; pose m2 := refine_smatte b.1.+1 m1.
  move=> IH r_b b_z b_t /(refine_smatte_interpolant b.1.+1).
  apply: (IH b2); last 1 [exact/in_refine_inset | exact/in_refine_srect].
    by split; [rewrite /= addnC addnS | apply/refine_matte_coarse].
  by move=> v /in_refine_srect/r_b.
case: b => _ b /= [-> b_ref] r_b [p /= Dp b_p] [q /= Dq b_q] [m1t m1m Um1].
have{q Dq b_q m1t} b_m1: has b m1.2.
  by apply/hasP; exists q => //; have [_ /(approx_point_inj Dq)<-] := m1t.
have [m2 m2m1 bm1m2 m2p] := coarse_extends_in b_ref b_m1 b_p.
case: U1'z; exists (m1.1, m2); split=> [|u /m1m|u [q Dq]]; first by exists p.
  exact/sub_mem_approx/in_extension.
by case/bm1m2/orP=> [b1q | m1q]; [apply/Ur/r_b | apply/Um1]; exists q.
Qed.

Section DiscrMatte.

Variable ab : Er -> srect.
Hypothesis abP : forall e i, ab_mr_proper (ab e) e i.

Definition proper_smatte (m : smatte) i (E : pred Er) :=
  let meet_m be := gr_proper be.2 -> meet m (inset_srect be) in
  subregion m (m0 (mr i)) /\ {in E, forall e, meet_m (ab e)}.

Lemma refine_smatte_proper s m i E :
  proper_smatte m i E -> proper_smatte (refine_smatte s m) i E.
Proof.
case=> ri_m rm_ab; split=> [z /in_refine_smatte/ri_m//| e Ee].
by case/rm_ab=> // z [m_z ab_z]; exists z; split; first apply/in_refine_smatte.
Qed.

Lemma exists_smatte :
  exists s cm, forall i, proper_smatte (s, cm i) i [pred e : Er | i \in e].
Proof.
pose E i := enum [pred e : Er | i \in e].
suffices /fin_all_exists[m mP] i: exists m, proper_smatte m i [mem E i].
  pose s_ i := \sum_(j | j != i) (m j).1.
  exists (\sum_i (m i).1), (fun i => (refine_smatte (s_ i) (m i)).2) => i.
  rewrite (bigD1 i) //= addnC; apply/refine_smatte_proper.
  by have [m_i m_E] := mP i; split=> // e; rewrite -mem_enum => /m_E.
have: all [pred e : Er | i \in e] (E i) by apply/allP=> e; rewrite mem_enum.
have [[_ m0open m0connect] _] := fin_m0.
elim: {E}(E i) => [_|e E IHe /= /andP[e_i /IHe{IHe}[m [m_i m_E]]]].
  have [/m0open[r r_i m0i_r] _] := mrP i.
  have [[s b] [p p_i /insetW-b_p] r_b] := approx_rect r_i.
  exists (s, point_matte p); split=> // z p_z; apply/m0i_r/r_b.
  by apply: sub_mem_approx p_z => _ /predU1P[] // ->.
have [ab_e | ab'e] := boolP (gr_proper (ab e).2); last first.
  by exists m; split=> // f /predU1P[-> /idPn | /m_E].
have [/(_ e_i)[z [e_z m0i_z]] _] := abP i ab_e.
have [m1 [m1z m1m m0im1]] := connected_matte (m0open _) (m0connect _) m_i m0i_z.
exists m1; split=> // f /predU1P[-> _ | _ /m_E[]// t []]; first by exists z.
by exists t; split; first apply/m1m.
Qed.

End DiscrMatte.

End AdjRepr.

Lemma discretize_to_hypermap :
  exists2 G, planar_bridgeless G & four_colorable G -> colorable_with 4 m0.
Proof.
have m0tr_cl z t: m0 z t -> subregion (closure (m0 t)) (closure (m0 z)).
  by move=> m0zt u t_u U openU /t_u[] // v [/(m0tr m0zt)]; exists v.
have [Nr [mr mrP mr_m0]] := exists_map_repr.
have [ab [abP [s ab_mrP]] ab_m0] := exists_adjbox mrP.
have [s1 [cm cmP]] := exists_smatte mrP ab_mrP.
without loss Ds1: s s1 ab cm abP ab_mrP ab_m0 cmP / s1 = s.
  pose s2 := s + s1; pose ab2 e := (refine_srect s1 (s, ab e) : srect).2.
  move/(_ s2 s2 ab2 (fun i => (refine_smatte s (s1, cm i) : smatte).2)).
  apply=> // [||e [m0ij ltij]|i].
  - rewrite /ab2; elim: (s1) => //= n IHn => e f p.
    by rewrite !in_refine_rect; apply: IHn.
  - by rewrite [s2]addnC => e i; apply/ab_mr_proper_refine/ab_mrP.
  - by rewrite gr_proper_refine ab_m0.
  apply: refine_smatte_proper (s1, _) _ _ _.
  have [m0i_cm cmi_ab] := cmP i; split=> // e /cmi_ab-cmi_e.
  rewrite gr_proper_refine => /cmi_e[z [mi_z ab_z]]; rewrite [s2]addnC.
  by exists z; split; last apply/in_refine_inset: ab_z.
have{ab_mrP} ab_cmP e i: ab_cm_proper ab cm e i.
  move=> ab_e; have [m0i_cm e_cmi] := cmP i.
  split=> [/e_cmi[] // z [[p Dp cm_p] [q Dq ab_q]] | /hasP[p ab_p cmi_p]].
    by apply/hasP; exists q; rewrite // -[q](approx_point_inj Dp) ?Ds1.
  have [_ ->//] := ab_mrP e i ab_e; exists (scale_point R s p).
  by split; last apply/m0i_cm; rewrite -Ds1; apply/mem_approx_scale.
have {}cmP: cm_proper cm.
  move=> i j /hasP[p /= cmi_p cmj_p].
  have [_ /(_ j)-> //] := mrP i; apply: m0tr (scale_point R s1 p) _ _ _.
    by have [m0_cmi _] := cmP i; apply/m0_cmi/mem_approx_scale.
  by have [m0_cmj _] := cmP j; apply/m0sym/m0_cmj/mem_approx_scale.
exists (grid_map abP cmP ab_cmP); first exact: planar_bridgeless_grid_map.
case/grid_map_coloring=> k0 ab_k0'.
pose k z t := exists2 i, m0 (mr i) z & exists2 j, m0 (mr j) t & k0 i = k0 j.
have mr_inj z t i j: m0 z t -> m0 (mr i) z -> m0 (mr j) t -> i = j.
  move=> m0zt m0iz m0jt; have [_] := mrP i; apply.
  exact/(m0tr (m0tr m0iz m0zt))/m0sym.
exists k; last first.
  have p0: point by split; apply: Real.zero.
  exists (fun c => oapp mr p0 [pick i | k0 i == c :> nat]) => z [i m0iz _].
  exists (k0 i); first exact/ltP/ltn_ord.
  have [j /eqP/val_inj-k0ij | /(_ i)/eqP] //= := pickP.
  by exists j; [have [] := mrP j | exists i].
have m0cover z t: m0 z t -> cover m0 z by move=> m0zt; apply/(m0tr m0zt)/m0sym.
split=> [|z [i /m0sym/m0cover] // | z t m0zt | z t adj_zt [i m0iz [j m0jt]]].
- split=> z t [i m0iz [j m0jt k_ij]]; first by exists j => //; exists i.
  move=> t1 [i1 m0i1t [j1 m0jt1 k_j1]]; exists i => //; exists j1 => //.
  by rewrite k_ij (mr_inj t t j i1) //; apply: m0cover (m0sym m0jt).
- by have /m0cover/mr_m0[i m0iz] := m0zt; do 2!exists i => //; apply: m0tr m0zt.
without loss ltij: z t i j m0iz m0jt adj_zt / i < j.
  move=> IHij k0ij; have [m0'tz [u [corner'u [m0z_u m0t_u]]]] := adj_zt.
  have adj_tz: adjacent m0 t z by split=> [/m0sym|]; last exists u.
  have: i != j by case: eqP m0jt => // <- /(m0tr (m0sym m0iz)).
  by rewrite neq_ltn => /orP[/(IHij z t) | /(IHij t z)] [].
have [m0'zt [u [corner'u [m0zu m0tu]]]] := adj_zt.
apply/eqP/(ab_k0' (AdjIndex ltij))/ab_m0; split=> //; split=> [/= m0ij|].
  by have [] := m0'zt; apply/(m0tr _ (m0tr m0ij m0jt))/m0sym.
by do [exists u; do 2!split=> //]; [apply: m0tr_cl m0zu | apply: m0tr_cl m0tu].
Qed.

End DiscretizeMap.
