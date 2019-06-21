(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype path fingraph.
From mathcomp
Require Import ssralg ssrnum ssrint.
From fourcolor
Require Import hypermap geometry color coloring patch snip grid matte.

(******************************************************************************)
(* The construction of a hypermap, from a finite set of disjoint mattes and a *)
(* set of adjacency boxes. These sets are simply represented by functions on  *)
(* `nat' integers. The construction starts by extending the mattes so that    *)
(* mattes that meet a common adjacency box share a contour edge. Then we      *)
(* compute a bounding box for the mattes, and create a plain planar connected *)
(* hypermap by framing the bounding box. The matte rings then map to simple   *)
(* rings of this map, with disjoint disks, so we can use the "snip" operation *)
(* to turn them into node rings (we need to operate in the dual map to make   *)
(* this work), by removing their interiors. Dualizing the resulting hypermap  *)
(* gives us a map whose coloring solves the initial coloring problem.         *)
(*   All definitions here depend on the number Nr of matte regions:           *)
(*           Ir := local Notation for 'I_Nr, the matte index type.            *)
(*    adj_index == the adjacency index type, which consist of ordered pairs   *)
(*                 of matte indices; this type coerces to both pairs and the  *)
(*                 collection of its components.                              *)
(*  AdjIndex ltij == the adj_index with components i, j, given ltij : i < j.  *)
(*       cmatte == Ir -> matte, the type for a set of Nr mattes.              *)
(*       abjbox == adj_index -> grect, the type for a collection of adjacency *)
(*                 boxes, i.e., grid rectangles isolating mattes adjacencies. *)
(*                 Non-adjacency is represented by empty rectangles.          *)
(*  cm_proper cm <-> the mattes in cm : cmatte are pairwise disjoint.         *)
(*  ab_proper ab <-> the rectangles in ab : adjbox are pairwise disjoint.     *)
(*  ab_cm_proper ab cm e i <-> if ab witnesses adjacency at e, then cm i      *)
(*                 meets the inside of ab e (specifically, inset (ab e)) if   *)
(*                 i is a component of e and is disjoint from ab e otherwise. *)
(* The remaining definitions in this file depend on a adjbox ab0 and cmatte   *)
(* cm0, and proofs, ab0P, cm0P and abcm0P that they satisfy the three well    *)
(* formedness properties above, for example:                                  *)
(*   grid_map ab0P cm0P abcm0P == a planar plain bridgeless hypermap that is  *)
(*                 four colorable only if a map with Nr regions and           *)
(*                 adjacencies described by ab.                               *)
(* This construction uses the following intermediate definitions, for which   *)
(* we omit the ab0, cm0, ab0P, cm0P and abcm0P parameters and assumptions:    *)
(*      cm_bbox == a grid rectangle containing all the mattes in a set cm of  *)
(*                 pairwise disjoint mattes that extend the cm0 set to        *)
(*                 realize the ab0 adjacencies as (madj) matte adjacencies.   *)
(*       gmgrid == a list of all the grid points in the gedge closure of      *)
(*                 cm_bbox.                                                   *)
(*       gmdart == the (finite) subtype with extent gmgrid, which coerces to  *)
(*                 gpoint.                                                    *)
(*   gmpick u s == some gmdart whose gpoint projection occurs in s,           *)
(*                 defaulting to u if s and gmgrid are disjoint.              *)
(*   gmdart_map == a hypermap with dart type gmdart.                          *)
(* gmedge, gmnode, gmface == the hypermap permutations for gmdart_map.        *)
(*  gm_cutout E == sigma-type encapsulating a planar hypermap that is the     *)
(*                 the remainder left by removing from gmdart_map (using      *)
(*                 library snip) the interior of all mattes cm i for i in Er  *)
(*                 (with cm as in cm_bbox), alongside its embedding in gmdart *)
(*                 the border rings of the removed mattes, and the proof that *)
(*                 this data satisfies the properties of a remainder map.     *)
(* We constuct an instance of gm_cutout Ir, and finally obtain grid_map as    *)
(* the hypermap dual of its encapsulated hypermap.                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Num.Def.
Local Open Scope ring_scope.

Section GridMap.

Variable Nr : nat.
Local Notation Ir := 'I_Nr.
Implicit Types i j : Ir.

Definition adj_index := {ij : Ir * Ir | ij.1 < ij.2}%N.
Definition adjbox := adj_index -> grect.
Definition cmatte := Ir -> matte.

Implicit Types (e : adj_index) (ab : adjbox) (cm : cmatte).

Canonical adj_index_eqType := [eqType of adj_index].
Canonical adj_index_choiceType := [choiceType of adj_index].
Canonical adj_index_finType := [finType of adj_index].

Coercion pair_of_adj_index e : Ir * Ir := val e.
Coercion adj_incident e := pred2 e.1 e.2.

Definition AdjIndex i j ltij : adj_index := Sub (i, j) ltij.

Definition cm_proper cm := forall i j, has (cm i) (cm j) -> i = j.

Definition ab_proper ab := forall e f p, ab e p -> ab f p -> e = f.

Definition ab_cm_proper ab cm e i (b := ab e) (m := cm i) :=
  gr_proper b -> [/\ i \in e -> has (inset b) m & has b m -> i \in e].

Variable (ab0 : adjbox) (cm0 : cmatte).
Hypotheses (ab0P : ab_proper ab0) (cm0P : cm_proper cm0).
Hypothesis abcm0P : forall e i, ab_cm_proper ab0 cm0 e i.

Lemma cm_extend_adj :
  {cm | cm_proper cm & forall e, gr_proper (ab0 e) -> madj (cm e.1) (cm e.2)}.
Proof.
pose cm i := refine_matte (cm0 i); pose ab e := refine_rect (ab0 e).
have: cm_proper cm.
  move=> i j /hasP[p /= cmj_p cmi_p]; apply/cm0P/hasP.
  by exists (halfg p); rewrite /= -in_refine_mdisk.
have abP: ab_proper ab by move=> e f p; rewrite !in_refine_rect; apply/ab0P.
have ab0_adj e: gr_proper (ab0 e) = gr_proper (ab e).
  by rewrite (gr_proper_refine 1).
pose cm_apart cm := [pred e | gr_proper (ab e) & ~~ madj (cm e.1) (cm e.2)].
pose coarse_inset (b : grect) m := coarse_in b m /\ has (inset b) m.
have (e) i (b := ab e) (m := cm i) :
  cm_apart cm e -> [/\ i \in e -> coarse_inset b m & has b m -> i \in e].
- rewrite /= -ab0_adj => /andP[/abcm0P-/(_ i)[b_m e_i] _].
  split=> [/b_m|] /hasP[p].
    rewrite -[p]halfg_double -in_refine_matte -/(cm i) -/m => m_2p.
    rewrite -in_refine_rect refine_inset -/(ab e) -/b => /insetW-b1_2p.
    by split; [apply: refine_matte_coarse | apply/hasP; exists (p *+ 2)].
  rewrite in_refine_matte in_refine_rect => mi_p ab_p.
  by apply/e_i/hasP; exists (halfg p).
elim: {cm}_.+1 {-2}cm (ltnSn #|cm_apart cm|) => // n IHn cm le_cm_n abcmP cmP.
have [cm_meet | ] := boolP [forall e, ~~ cm_apart cm e].
  exists cm => // e ab_e; have:= forallP cm_meet e.
  by rewrite /= -ab0_adj ab_e negbK.
rewrite -negb_exists negbK => /existsP/sigW/=[e cm'e].
have [/abcmP-/all_and2[cme_ab ab_e] /ltn_eqF-e1'2] := (cm'e, valP e).
have cm1ab: has (inset (ab e)) (cm e.1).
  by have [] //:= cme_ab e.1; rewrite !inE eqxx.
have [cm2ref cm2ab]: coarse_in (ab e) (cm e.2) /\ has (ab e) (cm e.2).
  have [|cm2ref cm2ab]:= cme_ab e.2; first by rewrite !inE eqxx orbT.
  by split; last apply/(sub_has _ cm2ab)/insetW.
have cm2'1: ~~ has (cm e.2) (cm e.1) by apply: contraFN e1'2 => /cmP->.
have [cm2 [cm2cm ab_cm2] cm12] := extend_madj cm2ref cm2ab cm1ab cm2'1.
pose xcm := [eta cm with e.2 |-> cm2].
have{cm12 e1'2} xcm_e: ~~ cm_apart xcm e.
  by rewrite /= eqxx -val_eqE e1'2 cm12 andbF.
have has'cm2 i: i != e.2 -> ~~ has cm2 (cm i).
  move=> e2'i; apply/hasPn=> p.
  have [-> | e1'i] := eqVneq i e.1; first by apply/contraL=> /ab_cm2/andP[].
  have ab'i: ~~ has (ab e) (cm i) by apply/(contra (ab_e i))/norP.
  have cm2'i: ~~ has (cm e.2) (cm i) by apply: contra e2'i => /cmP->.
  apply: contraL => /ab_cm2/andP[_]; apply/contraL=> cmi_p /=.
  by rewrite negb_or (hasPn ab'i) ?(hasPn cm2'i).
have madj_cm2 i: i != e.2 -> madj (cm i) (cm e.2) -> madj (cm i) cm2.
  move=> e2'i /hasP[d cmi_d cm2ed]; apply/hasP; exists d => //.
  move: cmi_d cm2ed; rewrite !(inE, in_mring) => /andP[r2_d _] /andP[ri_ed _].
  by rewrite cm2cm // (hasPn _ _ ri_ed) ?has'cm2.
have{madj_cm2} xcm'cm': subpred (cm_apart xcm) (cm_apart cm).
  move=> f /= /andP[->]; apply/contra.
  have [-> | e2'f1] := altP eqP; last by case: eqP => // ->; apply: madj_cm2.
  have [-> | e2'f2] := altP eqP; first by rewrite madj_irrefl.
  by rewrite madj_sym (madj_sym cm2); apply: madj_cm2.
have: cm_proper xcm.
  move=> i j /=; do 2!have [-> | /has'cm2/negP] := altP eqP; rewrite has_sym //.
  by clear 2; apply: cmP.
apply: IHn => [|f i bf m xcm'f].
  move: le_cm_n; rewrite ltnS (cardD1 e) inE [_ && _]cm'e.
  apply/leq_ltn_trans/subset_leq_card/subsetP=> f xcm'f.
  by rewrite inE xcm'cm' // (memPn _ _ xcm'f).
have bf'e p: ab e p -> ~ bf p by move=> ? /(abP e)D; rewrite D ?xcm'f in xcm_e.
have /xcm'cm'/(abcmP f i)/= := xcm'f; rewrite -/bf /m /=.
case: eqP => // -> -[e2bf bf_f]; split=> [/e2bf[cm2ref_bf cm2_bf]|]; last first.
  by case/hasP=> p /ab_cm2/andP[_ /orP[/bf'e//|*]]; apply/bf_f/hasP; exists p.
split=> [p q bf_p Dpq|]; last first.
  by have [p /cm2cm-cm2p bf_p] := hasP cm2_bf; apply/hasP; exists p.
without loss suffices IHpq: p q bf_p Dpq / p \in cm2 -> q \in cm2.
  by apply/idP/idP=> /IHpq-> //; rewrite !in_refine_rect Dpq in bf_p *. 
by case/ab_cm2/andP=> _ /orP[/bf'e//|cm2p]; rewrite cm2cm // (cm2ref_bf p q).
Qed.

Let cm := let: exist2 cm _ _ := cm_extend_adj in cm.

Let cmP : cm_proper cm. Proof. by rewrite /cm; case: cm_extend_adj. Qed.

Let ab_cmP e : gr_proper (ab0 e) -> madj (cm e.1) (cm e.2).
Proof. by rewrite /cm; case: cm_extend_adj => ? _; apply. Qed.

(* Now we compute a bounding box for the extended mattes. *)

Let grect0 := Grect 0 1 0 1.
Definition cm_bbox :=
  foldr extend_grect grect0 (flatten [seq mdisk (cm i) | i : Ir]).

Notation bb := cm_bbox.
Notation bbw := (gwidth bb).
Notation bbh := (gheight bb).

Lemma sub_cm_bbox i : subpred (cm i) bb.
Proof.
rewrite /bb; set e := flatten _ => p mi_p.
have{mi_p}: p \in e by apply/flatten_mapP; exists i; rewrite ?mem_enum.
elim: e => //= q e IHe; rewrite inE => qe_p.
by apply/in_extend_grect => /=; case: (p == q) qe_p.
Qed.

Lemma cm_bboxE :
  [/\ 0 < bbw%:Z, 0 < bbh%:Z & exists2 p0,
       forall x y, bb (p0 + Gpoint x y) = (0 <= x < bbw) && (0 <= y < bbh)
     & forall p, bb p -> exists x y : nat,
       [/\ p = p0 + Gpoint x y, x%:Z < bbw & y%:Z < bbh]].
Proof.
have [w_gt0 h_gt0]: 0 < bbw%:Z /\ 0 < bbh%:Z; last split=> //.
  apply/andP; rewrite -muln_gt0; apply: garea_subrect grect0 bb _ => p r0p.
  rewrite /bb; elim: (flatten _) => //= q e IHe.
  by rewrite in_extend_grect //= IHe orbT.
case: bb w_gt0 h_gt0 => x0 x1 y0 y1 /=; rewrite -[x1](subrK x0) -[y1](subrK y0).
rewrite /zwidth /= !addrK; case: (_ - _) (_ - _) => h []w _ _ //.
pose p0 := Gpoint x0 y0; exists p0 => [x y | p].
  by rewrite addrC /= !ltr_add2r !ler_addr.
rewrite -(subrK p0 p); case: (p - p0) => x y /=; rewrite !ler_addr !ltr_add2r.
by case: x y => x [] y /andP[] //; exists x, y; first rewrite addrC.
Qed.

(* Now we define the box hypermap.                                            *)
(* It would be tempting to form this hypermap from the darts contained in the *)
(* bounding box, but unfortunately this map is not bridgeless. We work around *)
(* this issue by using the edge closure of gmgrid.                            *)
Definition gmgrid :=
  let inner := enum_grect (refine_rect bb) in inner ++ map gedge inner.

Lemma gmgridE d : (d \in gmgrid) = bb (halfg d) || bb (halfg (gedge d)).
Proof.
rewrite mem_cat -[d in d \in map _ _]gedge2 (mem_map (can_inj gedge2)).
by rewrite !mem_enum_grect !in_refine_rect.
Qed.

Lemma gmgrid_edge d: (gedge d \in gmgrid) = (d \in gmgrid).
Proof. by rewrite !gmgridE gedge2 orbC. Qed.

Definition gmdart : predArgType := seq_sub gmgrid.
Coercion gmval := @ssval _ _ : gmdart -> gpoint.
Definition Gmdart d : d \in gmgrid -> gmdart := Sub d.
Implicit Types u v w : gmdart.

Canonical gmdart_subType := [subType of gmdart for gmval].
Canonical gmdart_eqType := [eqType of gmdart].
Canonical gmdart_choiceType := [choiceType of gmdart].
Canonical gmdart_finType := [finType of gmdart].
Canonical gmdart_subFinType := [subFinType of gmdart].

Definition gmedge u := Gmdart (etrans (gmgrid_edge u) (valP u)).
Definition gmpick u s : gmdart := foldl insubd u s.
Definition gmface u := gmpick u (traject gnode (gnode u) 3).
Definition gmnode u := gmpick u (rev (map gedge (traject gnode (gnode u) 3))).

Lemma gmedge2 : involutive gmedge.
Proof. by move=> u; apply/val_inj; rewrite /= gedge2. Qed.

Lemma gmedgeK : cancel3 gmedge gmnode gmface.
Proof.
case=> d Gd; apply/val_inj; rewrite !val_insubd /= ifE.
have [_ | G'n3ed] := ifP; first by rewrite gnode4 gedge2 Gd. 
have [_ | G'n2ed] := ifP; first by rewrite gnode4 gedge2 Gd gmgrid_edge G'n3ed.
rewrite ifT; first by rewrite gnode4 gedge2 Gd !gmgrid_edge G'n3ed G'n2ed.
rewrite -gnode_face gnode4 gmgridE halfg_face in G'n3ed.
do [rewrite gmgridE -implyNb => /implyP] in Gd.
by rewrite gmgridE orbC -halfg_face gnodeK Gd //; case/norP: G'n3ed.
Qed.

Canonical gmdart_map := Hypermap gmedgeK.

Lemma gmdart_plain : plain gmdart_map.
Proof.
apply/plainP=> /= u _; rewrite gmedge2 -val_eqE /=.
by rewrite (contraFneq _ (neq_halfg_edge u)) => // ->.
Qed.

Definition gm_inner := [pred u : gmdart | bb (halfg u)].

Lemma val_gmnode u : u \in gm_inner -> val (node u) = gedge (gnode u).
Proof.
by rewrite inE => bb_u; rewrite val_insubd gmgridE -halfg_face gnodeK bb_u.
Qed.

Lemma gm_inner_node u : u \in gm_inner -> node u \in gm_inner.
Proof. by move=> bb_u; rewrite inE -halfg_face val_gmnode ?gnodeK. Qed.

Lemma gm_inner_closed : fclosed node gm_inner.
Proof. by apply/(intro_closed cnodeC)=> u _ /eqP<-; apply: gm_inner_node. Qed.

Lemma card_gmdart : #|gmdart| = (bbw * bbh * 2 + bbw + bbh).*2.
Proof.
have [w_gt0 h_gt0 [p0 bbE bbP]] := cm_bboxE.
rewrite -addnA muln2 doubleD -(cardC gm_inner); congr (_ + _)%N.
  rewrite -garea_refine_rect -size_enum_grect cardE -(size_map val).
  apply/eqP; rewrite -uniq_size_uniq ?enum_grect_uniq // => [|d].
    exact/dinjectiveP/(in2W val_inj).
  rewrite mem_enum_grect in_refine_rect; apply/idP/imageP=> [bb_d|[u ? -> //]].
  by have Gd: d \in gmgrid; [rewrite gmgridE bb_d | exists (Gmdart Gd)].
pose bbc c := Gpoint (0 < c < 3)%N (1 < c)%N.
pose w1 := bbw%:Z - 1; pose h1 := bbh%:Z - 1.
pose bbp c z := Gpoint (nth 0 [:: z; w1; z] c) (nth z [:: 0; z; h1] c).
pose bbd c z := (p0 + bbp c z%:Z) *+ 2 + bbc c.
pose bbl c := if ~~ odd c then bbw else bbh.
pose side c := [seq bbd c z | z <- iota 0 (bbl c)].
have <-: size (flatten [seq side c | c <- iota 0 4]) = (bbw + bbh).*2.
  by rewrite !size_cat !size_map !size_iota addn0 addnA addnn.
rewrite cardE -(size_map (val \o gmedge)); apply/perm_size.
apply/uniq_perm; first exact/dinjectiveP/(in2W (inj_comp val_inj _))/edgeI.
  have bbd_inj c: injective (bbd c).
    move=> e1 e2 /(congr1 halfg); rewrite !halfg_add2 => /addIr/addrI.
    by do 4!case: c => [[]// | c]; case.
  have hasn_side c1 c2: (c1 < c2 < 4)%N -> has [mem side c1] (side c2) = false.
    rewrite andbC => ltc; apply/hasPn=> _ /mapP[z2 _ ->]; apply/mapP=> -[z1 _].
    by move/(congr1 oddg); rewrite !oddg_add2; case: c2 c1 ltc; do 6!case=> //.
  by rewrite !cat_uniq !cats0 !has_cat !map_inj_uniq ?iota_uniq ?hasn_side.
move=> d; apply/imageP/flatten_mapP=> [[/= u G'u ->] | [c ltc /mapP[z ltz ->]]].
  rewrite -[gedge u]halfgK; rewrite !inE -(gedge2 u) halfg_edge in G'u.
  have:= valP (edge u); rewrite gmgridE orbC -implyNb halfg_edge G'u /=.
  case/bbP=> x [y [Deu ubx uby]]; rewrite {}Deu -addrA in G'u *.
  pose c := index (oddg (gedge u)) (traject ccw 0 4).
  exists c; first by rewrite /c; case: oddgP.
  apply/mapP; exists (if ~~ odd c then x else y).
    by rewrite /c mem_iota; case: oddgP.
  rewrite {}/c /bbd /bbp; congr ((p0 + _) *+ 2 + _); last by case: oddgP.
  case: oddgP G'u; rewrite bbE ?addr0 ?ubx ?uby /= ?andbT /h1 /w1;
    do ?by rewrite andbC -lez_addr1 subrK ltrW // subr_ge0 -eqn0Ngt => /eqP->.
  - by have [/idPn||->] := ltrgtP bbh%:Z; rewrite ?addrK // -lerNgt lez_addr1.
  - by have [/idPn||->] := ltrgtP bbw%:Z; rewrite ?addrK // -lerNgt lez_addr1.
rewrite -[bbd c z]gedge2; set ed := gedge (bbd c z).
suffices /andP[Ged]: (ed \in gmgrid) && ~~ bb (halfg ed) by exists (Gmdart Ged).
rewrite mem_iota /= -ltz_nat in ltz; rewrite !inE in ltc.
rewrite gmgridE andb_orl andbN gedge2 halfg_edge halfg_add2 oddg_add2 -!addrA.
by case/or4P: ltc ltz => /eqP->; rewrite !bbE !addr0 ?addrK ?ltrr => ->;
   rewrite ?gtr_addl !andbT ?subr_ge0.
Qed.

Lemma cface_end0g u v : cface u v = (end0g u == end0g v).
Proof.
apply/idP/eqP=> [/connectP[_ /fpathP[k ->] ->] | /same_end0g/trajectP[k]].
  rewrite last_traject; elim: k => //= k IHk in u *.
  by rewrite !val_insubd !(fun_if end0g) !end0g_node !if_same.
without loss: k u v / k \in iota 2 2.
  case: k => [|[|k]] IHk ltk Dv; first by have ->: v = u by apply/val_inj.
    by rewrite cfaceC (IHk 3) // Dv /= gnode4.
  by rewrite (IHk k.+2) ?mem_iota.
have Gv := valP v; rewrite !inE => /pred2P[]-> _ /= Dv; rewrite /= Dv in Gv.
  case Gn3u: (iter 3 gnode u \in gmgrid).
    rewrite 2!cface1 eq_connect0 //; apply/val_inj; rewrite !val_insubd Gn3u.
    by rewrite gnode4 Gv.
  by rewrite cface1 eq_connect0 //; apply/val_inj; rewrite !val_insubd Gn3u Gv.
by rewrite cface1 eq_connect0 //; apply/val_inj; rewrite val_insubd Gv.
Qed.

Lemma fcard_gmface : fcard face gmdart_map = (bbw.+1 * bbh.+1)%N.
Proof.
have [w_gt0 h_gt0 [p0 bbE bbP]] := cm_bboxE.
pose gmframe := enum_grect (Grect 0 bbw.+1 0 bbh.+1).
have gmendP (u : gmdart): end0g u - p0 \in gmframe.
  without loss /bbP[x [] y [] Du ubx uby]: u / u \in gm_inner.
    move=> IHu; have:= valP u; rewrite gmgridE => /orP[/IHu//|].
    rewrite -halfg_face -[gface _]gnode4 gedgeK => bbn3u; have:= IHu (face u).
    by rewrite inE val_insubd gmgridE bbn3u !end0g_node => ->.
  rewrite /end0g {}Du addrC -addrA addKr mem_enum_grect !intS !(addrC 1).
  by case: oddgP; rewrite /= ?addr0 ?ltr_add2r ?ltz_addr1 ?ltrW ?ubx.
pose gmend u := SeqSub (gmendP u).
suffices adj_gmend: fun_adjunction gmend id face predT.
  rewrite -(adjunction_n_comp _ (fconnect_sym _) cfaceC _ adj_gmend) //.
  rewrite fcard_id card_seq_sub ?enum_grect_uniq // size_enum_grect /=.
  by rewrite /garea /= /zwidth !addr0.
split=> [[[x y] Gxy] _ | u v _]; last first.
  by rewrite fconnect_id cface_end0g eq_sym -val_eqE /= (inj_eq (addIr _)).
pose c := locked Gpoint (x == bbw) (y == bbh).
suffices Gu: (p0 + (Gpoint x y - oddg c)) *+ 2 + oddg c \in gmgrid.
  exists (Gmdart Gu); rewrite fconnect_id -val_eqE /= addrCA -addrA -opprB.
  by rewrite halfg_eq ?oddg_eq ?subrK.
rewrite gmgridE halfg_eq //= {}/c -lock bbE !ltr_subl_addl !subr_ge0.
apply/orP; left; apply/andP; move: Gxy; rewrite mem_enum_grect /=.
rewrite !intS !ltz_add1r (ler_eqVlt x) (ler_eqVlt y) => /andP[Gx Gy].
by split; [move: Gx | move: Gy]; case: eqP => // -> _; rewrite ltr_addr andbT.
Qed.

Lemma fcard_gmnode : (bbw * bbh <= fcard node gmdart_map)%N.
Proof.
rewrite (n_compC gm_inner) addnC (@leq_add 0) // -2!leq_double.
rewrite -garea_refine_rect -size_enum_grect.
rewrite -[n in n.*2]muln2 doubleMr (fcard_order_set nodeI _ gm_inner_closed).
  rewrite cardE -(size_map val) uniq_leq_size ?enum_grect_uniq // => d.
  rewrite mem_enum_grect in_refine_rect => bb_d.
  by apply/imageP/(ex_intro2 _ _ (Sub d _)); rewrite // gmgridE bb_d.
apply/subsetP=> /= u bb_u; rewrite inE.
have cyc_u: fcycle node (traject node u 4).
  rewrite [3]lock /= rcons_path fpath_traject -lock /= -val_eqE.
  by rewrite !val_gmnode ?gm_inner_node // -[gedge _]gface4 !gnodeK.
rewrite (order_cycle cyc_u) ?mem_head // looping_uniq.
have neq_node v: oddg v != oddg u -> v != u by apply: contraNneq => ->.
by rewrite /looping !inE !(inj_eq nodeI) !negb_or !neq_node //;
   rewrite !val_gmnode ?gm_inner_node // !(oddg_node, oddg_edge); case: oddgP.
Qed.

Lemma gmdart_connected : connected gmdart_map.
Proof.
have [w_gt0 h_gt0 [p0 bbE bbP]] := cm_bboxE.
have[:uP] @u := @Gmdart ((p0 + 0) *+ 2) uP.
  by rewrite gmgridE halfg_double bbE w_gt0 h_gt0.
apply/eqP; congr (_ = 1%N): (n_comp_connect glinkC u).
apply/eq_n_comp_r => /= v; rewrite !inE glinkC.
without loss bb_v: v / v \in gm_inner.
  have:= valP v; rewrite gmgridE => /orP[bb_v | bb_ev] IHv; first exact: IHv.
  by rewrite (same_connect1 glinkC (glinkE v)) IHv.
have /bbP[x [] y [] Dv _ _] := bb_v.
move Dn: (x + y).+1 => n; elim: n => // n IHn in x y v Dv bb_v Dn *.
without loss Dov: v Dv bb_v / oddg v = oddg (Gpoint 0 (x != 0%N)).
  set c := (c in oddg c) => IHv; move: Dv; rewrite -[RHS](halfg_eq _ (oddgP c)).
  case/esym/same_halfg/trajectP=> i _ Dv; elim: i => [|i IHi] in v Dv bb_v *.
    by rewrite IHv ?Dv ?halfg_eq ?oddg_eq.
  rewrite (same_connect1 glinkC (glinkN v)) IHi ?gm_inner_node //.
  by rewrite val_gmnode // Dv gfaceK.
case: n IHn => [_|n IHn] in Dn.
  apply/eq_connect0/val_inj; rewrite -[val v]halfgK {}Dv {}Dov.
  by case: x y Dn => -[] _ //; rewrite addr0.
have{Dov} Dev: halfg (gmedge v) = p0 + Gpoint (x - 1)%N (y - (x == 0))%N.
  by rewrite halfg_edge {}Dv {}Dov addrAC -addrA; case: x y Dn => [|x] [].
rewrite (same_connect1 glinkC (glinkE v)) (IHn _ _ _ Dev) //.
  have:= bb_v; rewrite !inE Dv Dev !bbE /= => /andP[ubx uby].
  by rewrite !ltz_nat !(leq_ltn_trans (leq_subr _ _)).
by case: x y {Dv Dev} Dn => [|x] [|y] // [<-]; rewrite !subn1.
Qed.

Lemma gmdart_planar : planar gmdart_map.
Proof.
rewrite /planar -leqn0 (@half_leq _ 1) // leq_subLR addn1.
rewrite /Euler_lhs (eqnP gmdart_connected) add2n ltnS -ltn_double -addnn //.
rewrite doubleD -muln2 (fcard_order_set edgeI gmdart_plain) // ltn_add2l.
rewrite card_gmdart ltn_double muln2 -addnn -addnA addnAC addnA -mulnSr.
by rewrite -addSn -addnS -mulSnr addnC fcard_gmface leq_add2r fcard_gmnode.
Qed.

Definition gmring i : seq gmdart := pmap insub (mring (cm i)).

Lemma val_gmring i : map val (gmring i) = mring (cm i).
Proof.
rewrite (pmap_filter (insubK _)) (all_filterP _) //.
apply/allP=> d; rewrite in_mring => /andP[mi_d _].
by rewrite isSome_insub gmgridE (sub_cm_bbox mi_d).
Qed.

Lemma gm_disk_def i : {subset diskN (gmring i) <= [preim halfg \o val of cm i]}.
Proof.
move=> _ /hasP[nv ri_nv /connectP[s vDs ->]]; set v := finv _ _ in vDs *.
have{ri_nv} mi_v: halfg (val v) \in cm i.
  have:= map_f val ri_nv; rewrite val_gmring // in_mring => /andP[mi_nv _].
  rewrite -[val v]gnodeK halfg_face -val_gmnode ?(f_finv nodeI) //.
  by rewrite (fclosed1 gm_inner_closed) (f_finv nodeI) inE (sub_cm_bbox mi_nv).
elim: s {nv}v mi_v vDs => //= v s IHs u mi_u /andP[/andP[r'u uCv]]; apply: IHs.
rewrite -(mem_map val_inj) val_gmring // in_mring inE mi_u /= negbK in r'u.
case/clinkP: uCv => [Du | <-].
  rewrite -[val v]gnodeK halfg_face -val_gmnode -?Du //.
  by rewrite (fclosed1 gm_inner_closed) -Du inE (sub_cm_bbox mi_u).
rewrite -[u]faceK gedge2 in r'u; rewrite -[val _]gnodeK halfg_face.
by rewrite -val_gmnode // (fclosed1 gm_inner_closed) inE (sub_cm_bbox r'u).
Qed.

Lemma disjoint_gmdisk i j :
  i != j -> [disjoint diskN (gmring i) & diskN (gmring j)].
Proof.
apply/contraR=> /exists_inP[/= u mi_u mj_u]; apply/eqP/cmP/hasP.
by exists (halfg u); apply: gm_disk_def.
Qed.

Lemma gmring_cycle i : scycle rlink (gmring i).
Proof.
have Dri := val_gmring i; have Uri: simple (gmring i).
  apply: map_uniq (end0g \o val) _ _; congr (uniq _): (mring_simple (cm i)).
  rewrite -Dri -!map_comp; apply: eq_map => u /=; apply/eqP.
  by rewrite -cface_end0g connect_root.
rewrite /scycle cycle_from_next ?simple_uniq // => u.
rewrite -(mem_map val_inj) Dri => /(next_cycle (mring_cycle (cm i))).
rewrite -Dri (next_map val_inj) ?simple_uniq //= -end0g_face.
by rewrite -end0g_node gnode_face /rlink cface_end0g.
Qed.

Inductive gm_cutout (E : pred Ir) :=
  GmCutout (G : hypermap) (h : G -> gmdart) (r : Ir -> seq G) of
      planar G
    & injective h & {morph h : x / edge x} & {mono h : x y / cface x y}
    & {in [pred x | [forall i in E, x \notin r i]], {morph h : x / node x}}
    & forall i, rev (map h (r i)) = gmring i
    & {in E, forall i, ufcycle node (r i)}.

Lemma has_cutout : gm_cutout Ir.
Proof.
have planGm := gmdart_planar; set E := Ir : pred Ir.
elim: {E}_.+1 {-2}E (ltnSn #|E|) => // n IHn E leEn.
have [j /= Ej | /(_ _)/=noE] := pickP [mem E]; last first.
  by exists gmdart_map id (rev \o gmring) => // i; rewrite ?noE ?map_id ?revK.
rewrite ltnS (cardD1 j) Ej in leEn.
have{IHn} [G h r planG Ih hE hF hN Dr cycNr] := IHn _ leEn.
pose mj := [preim h of diskN (gmring j)].
have h_r i x: (h x \in gmring i) = (x \in rev (r i)).
  by rewrite -Dr !mem_rev mem_map.
have cycRrj: scycle rlink (rev (r j)).
  have /andP[] := gmring_cycle j; rewrite -Dr -map_rev simple_map //.
  move=> cycRrj UFrj; have Urj := simple_uniq UFrj.
  rewrite /scycle cycle_from_next // => x /(map_f h)/(next_cycle cycRrj).
  by rewrite next_map // /rlink -hE hF.
have r'mj i x: i != j -> x \in mj -> x \notin r i.
  move=> j'i mj_x; apply: contraL (disjoint_gmdisk j'i) => ri_x.
  by apply/existsP; exists (h x); rewrite /= diskN_E !inE h_r mem_rev ri_x.
have mj_hN: {in mj, {morph h : x / node x}}.
  by move=> x mj_x; apply/hN/forall_inP=> i /andP[/r'mj->].
have mjN: fclosed node mj.
  apply/(intro_closed cnodeC)=> x _ /eqP<- mj_x; rewrite inE /= mj_hN //.
  by rewrite -(fclosed1 (diskN_node _)).
have h_mj: {subset diskN (rev (r j)) <= mj}.
  move=> _ /hasP[z rj_z /connectP[s xDs ->]]; set x := finv node z in xDs *.
  have{rj_z} mj_x: x \in mj.
    by rewrite (fclosed1 mjN) (f_finv nodeI) !inE diskN_E !inE h_r rj_z.
  elim: s => //= y s IHs in {z} (x) mj_x xDs *.
  case/andP: xDs => /andP[/= rj'x xCy]; apply: {s}IHs; rewrite (fclosed1 mjN).
  case/clinkP: xCy => <- //; rewrite !inE diskN_E; apply/orP; right=> /=.
  rewrite (fclosed1 (diskE_edge gmdart_planar (gmring_cycle j))) -hE faceK.
  by rewrite !inE (h_r j) rj'x.
have patch_j := snip_patch planG cycRrj; set Gj := snip_rem _ _ in patch_j.
set hj : Gj -> G := snipr in patch_j.
have [_ Ihj _ cycNrj _ _ _ _ _ hjN] := patch_j.
pose rj i := preim_seq hj (rev (rev (r i))); have Drj i: map hj (rj i) = r i.
  rewrite map_preim revK // => x; rewrite codom_snipr !inE mem_rev.
  by apply: contraL => /andP[rj'x /h_mj/(r'mj i)-/implyP]; case: eqP => [->|].
have hjF x y: cface (hj x) (hj y) = cface x y by rewrite (patch_face_r patch_j).
have h_rj i x: (hj x \in r i) = (x \in rj i) by rewrite -(mem_map Ihj) Drj.
exists Gj (h \o hj) rj; first 1 [exact: planar_snipr | exact: inj_comp].
- by move=> x; rewrite /= hE.
- by move=> x y; rewrite [LHS]hF hjF.
- move=> x /forall_inP/=r'x; rewrite [y in h y]hjN ?(inE, r'x) //.
  by apply/hN/forall_inP=> i /andP[_ /r'x]; rewrite h_rj.
- by move=> i; rewrite map_comp Drj Dr.
move=> i Ei; have [-> // | j'i] := eqVneq i j.
have [|cycNri Uri] := andP (cycNr i _); first exact/andP.
have Urji: uniq (rj i) by rewrite -(map_inj_uniq Ihj) Drj.
rewrite /ucycle cycle_from_next // => x /(map_f hj); rewrite Drj => r_x.
have:= next_cycle cycNri r_x; rewrite -Drj next_map //= -hjN // !inE -h_rj.
by apply: contraL r_x => rj_x; rewrite r'mj ?h_mj // diskN_E !inE mem_rev rj_x.
Qed.

Definition grid_map :=
  let: GmCutout G _ _ _ _ _ _ _ _ _ := has_cutout in dual G.

Lemma planar_bridgeless_grid_map : planar_bridgeless grid_map.
Proof.
rewrite /grid_map; case: has_cutout => G h r planG Ih hE _ hN Dr cycNr.
split; rewrite ?planar_dual ?bridgeless_dual //; apply/existsP=> -[x xNex].
without loss bb_hx: x xNex / h x \in gm_inner.
  move=> IHx; have:= valP (h x); rewrite gmgridE => /orP[/IHx[]//|bb_ex].
  apply: IHx (edge x) _ _; [rewrite cnodeC | by rewrite hE].
  by congr (cnode _ _): xNex; apply/Ih/val_inj; rewrite !hE /= gedge2.
have [/existsP[i ri_x] | r'x] := boolP [exists i, x \in r i].
  have /andP[cycNri _] := cycNr i isT.
  have:= xNex; rewrite (fconnect_cycle cycNri) //; move: ri_x.
  rewrite -!(mem_map Ih) hE -!(mem_rev (map h _)) Dr -!(mem_map val_inj).
  by rewrite val_gmring // !in_mring !inE => /andP[_ /negPf->].
suff: halfg (h x) = halfg (h (edge x)) by apply/eqP; rewrite hE neq_halfg_edge.
case/connectP: xNex => _ /fpathP[k ->] ->; rewrite last_traject.
rewrite negb_exists in r'x; elim: k => // k IHk in x bb_hx r'x *.
rewrite -(gnodeK (h x)) halfg_face iterSr.
rewrite -IHk ?hN ?val_gmnode ?gm_inner_node //.
apply/forallP=> i; apply: contra (forallP r'x i).
by move/(fconnect_cycle (ucycle_cycle (cycNr i isT))) <-; rewrite -cnode1.
Qed.

Lemma grid_map_coloring :
    four_colorable grid_map ->
  exists k : Ir -> 'I_4, forall e, gr_proper (ab0 e) -> k e.1 != k e.2.
Proof.
rewrite /grid_map; case: has_cutout => G h r planG Ih hE _ hN Dr cycNr.
case/four_colorable_dual=> k [kE /fconnect_invariant-kN].
have{cycNr kN} k_r i: {in r i &, forall x y, k x = k y}.
  by have /andP[/fconnect_cycle-cycNri _] := cycNr i isT => x y /cycNri<- /kN.
pose kn x := Ordinal (index_size (k x) [:: Color0; Color1; Color2] : _ < 4)%N.
exists (fun i => oapp kn ord0 [pick x in r i]) => e /ab_cmP/hasP[d].
rewrite !inE eqE /= -!val_gmring => /mapP[u r2u {d}->] /mapP[eu r1eu Deu].
have{Deu} Deu: edge u = eu by apply/val_inj.
rewrite -{eu}Deu -!{}Dr !mem_rev in r2u r1eu.
case/mapP: r2u r1eu => x r2x ->; rewrite -hE mem_map // => r1ex.
apply: contraFN (kE x); have [y /= /k_r <- | /(_ (edge x))/idP] // := pickP.
by have [z /(k_r _ x)-> | /(_ x)/idP] //= := pickP; do 2!case: (k _).
Qed.

End GridMap.
