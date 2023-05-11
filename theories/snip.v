(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype path fingraph.
From fourcolor Require Import hypermap jordan color geometry patch.

(******************************************************************************)
(*   This file provides a construction for cutting a planar hypermmap G along *)
(* a ring r (i.e., a simple R-cycle) so as to yield two maps Gd and Gr that   *)
(* will satisfy the "patch" predicate. We could have carried out a more       *)
(* general division of the map G along a contour (uniq C-cycle), from which   *)
(* the ring r could be extracted as a subpath; indeed we do construct such a  *)
(* contour inside the proof of our main lemma, which establishes that the     *)
(* "inside" of the disk part is edge-closed. However for the proof of the     *)
(* Four Color Theorem the ring r is a more natural parameter and the stronger *)
(* assumption on r (that it is face-simple, rather than part of a contour)    *)
(* lets us prove the other closure properties without using the planarity of  *)
(* G. In the Four Color Theorem proof more general divisions in which contour *)
(* might not be face-simple are obtained by directly identifying the interior *)
(* as the embedding of a specific configuration. The construction given here  *)
(* is used in the preliminary reducibility results -- mainly Birkhoff's       *)
(* connectivity theorem.                                                      *)
(*   Given G : hypermap, r : seq G, and assumption planG : planar G, and      *)
(* cycRr : scycle rlink r we define:                                          *)
(*     dlink r x y <=> there is a C-link from x \notin r to y.                *)
(*  dconnect r x y <=> there is an internally r-disjoint C-path from y to x   *)
(*                     that starts with a (reverse) N-link, i.e., there is    *)
(*                     a dlink path from finv node y to x.                    *)
(*       diskN r x <=> x is inside the N-closed disk delimited by r, i.e.,    *)
(*                     dconnect x y holds for some y \in r. Note that diskN r *)
(*                     contains r.                                            *)
(*       diskE r x <=> x is inside the E-closed disk strictly delimited by r, *)
(*                     that is, in diskN r but not in r.                      *)
(*       diskF r x <=> x is inside the F-closed disk strictly delimited by r, *)
(*                     that is, in diskN r but not in fband r.                *)
(*      diskFC r x <=> x is strictly outside the F-closure of the disk        *)
(*                     i.e., neither in diskN r nor fband r.                  *)
(*    snip_disk planG cycRr == a "disk" planar connected hypermap containing  *)
(*                             the darts of diskN r.                          *)
(*   snipd_ring planG cycRr == the border E-cycle of snip_disk planG cycRr.   *)
(*                  snipd u == the projection of u : snip_disk _ _ in G.      *)
(*     snip_rem planG cycRr == a "remainder" hypermap containing the darts of *)
(*                     G on or outside r, including those not connected to r. *)
(*   snipr_ring planG cycRr == the border N-cycle of snip_rem planG cycRr.    *)
(*                  snipr u == the projection of u : snip_rem _ _ in G.       *)
(* We then have:                                                              *)
(* @patch G _ _ snipd snipr (snipd_ring planG cycRr) (snipr_ring planG cycRr) *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Snip.

Variable G : hypermap.
Hypothesis planarG : planar G.

Variable r : seq G.

Hypothesis scycRr : scycle rlink r.
Let cycRr := scycle_cycle scycRr.
Let UrF := scycle_simple scycRr.
Let Ur := scycle_uniq scycRr.

(******************************************************************************)
(*   The disk defined by the ring is defined as the set of darts that can be  *)
(* reached from the ring by a C-path that starts with a inverse node step and *)
(* does not cross the contour. That disk is node-closed. Because a planar map *)
(* G has the Jordan property, the edge-interior of that disk Gd is just Gd    *)
(* with r removed (assuming we're not in the trivial case where r is an edge  *)
(* 2-cycle). For the face interior we need to remove all of (fband r).        *)
(******************************************************************************)

Definition dlink : rel G := [rel x y | (x \notin r) && clink x y].

Definition dconnect : rel G := [rel x y | connect dlink (finv node y) x].
Canonical dconnect_app_pred x := ApplicativePred (dconnect x).

Definition diskN : pred G := (fun x => has (dconnect x) r).

Definition diskE : pred G := [predD diskN & r].

Definition diskF : pred G := [predD diskN & fband r].

Definition diskFC : pred G := [predD [predC diskN] & fband r].

Lemma diskN_node : fclosed node diskN.
Proof.
suffices clN'dN: fclosed (finv node) diskN.
  apply: (intro_closed cnodeC) => x _ /eqP <- dNx.
  by rewrite (fclosed1 clN'dN) (finv_f nodeI).
have nodeI' := finv_inj (@nodeI G).
apply: (intro_closed (fconnect_sym nodeI')) => x _ /eqP <- dNx; apply/hasP.
case rx: (x \in r); first by exists x; rewrite /dconnect /=.
have [z rz z'Dx] := hasP dNx; exists z => //.
by apply: connect_trans z'Dx (connect1 _); rewrite /dlink /= rx /clink /= eqxx.
Qed.

Lemma diskN_E x : (x \in diskN) = (x \in r) || (x \in diskE).
Proof.
rewrite !inE; case r_x: (x \in r) => //=.
rewrite -[x](f_finv nodeI) -(fclosed1 diskN_node).
by apply/hasP; exists x; last apply: connect0.
Qed.

Lemma diskF_face : fclosed face diskF.
Proof.
apply: (intro_closed cfaceC) => x _ /eqP <- /andP[/= F'x dNx].
rewrite inE /= -(fclosed1 (fbandF r)) F'x.
have [y ry y'Dx] := hasP dNx; apply/hasP; exists y => //=.
rewrite /dconnect /= (connect_trans y'Dx) ?connect1 /dlink //= clinkF andbT.
by apply: contra F'x => rx; apply: (subsetP (ring_fband r)).
Qed.

Lemma diskFC_face : fclosed face diskFC.
Proof.
move=> /= x y xFy; have:= diskF_face xFy; rewrite !inE.
by rewrite (fbandF r xFy); case: (~~ _) => //= ->.
Qed.

Lemma diskE_edge : fclosed edge diskE.
Proof.
apply: (intro_closed cedgeC) => x _ /eqP <- /andP[/= r'x dNx].
suffices[x' dNx' [p [x'Fp <-] /= /norP[r'x' r'p]]]: exists2 x', x' \in diskN
  & exists2 p, fpath face x' p /\ last x' p = edge x & ~~ has (mem r) (x' :: p).
- elim/last_ind: p x'Fp r'p => [|p y IHp] /=; first by rewrite !inE r'x'.
  rewrite last_rcons rcons_path has_rcons /= => /andP[x'Fp Dy] /norP[r'y r'p].
  have{IHp x'Fp r'p} /andP[r'p /hasP[z rz z'Dp]] := IHp x'Fp r'p.
  rewrite !inE r'y; apply/hasP; exists z => //=; apply: connect_trans z'Dp _.
  by rewrite connect1 /dlink //= r'p -(eqP Dy) clinkF.
pose x' := face (edge x); have: cface x' (edge x) by rewrite cfaceC fconnect1.
case/connectP=> _ /shortenP[q x'Fq Uq _] Lq.
have [[y qy ry] | r'q] := altP (@hasP _ (mem r) (x' :: q)); last first.
  by exists x'; [rewrite (fclosed1 diskN_node) edgeK | exists q].
have [i r1 Dr] := rot_to ry.
have:= cycRr; rewrite -(rot_cycle i) Dr /= rcons_path => /andP[yRr1].
set z := last y r1; pose z' := face (edge z) => zRy.
have rz: z \in r by rewrite -(mem_rot i) Dr mem_last.
have yFz': cface y z' by rewrite cfaceC -cface1.
have: z' \in x' :: q.
  suffices Fx': cface x' =i x' :: q.
    by rewrite -!Fx' [_ \in _]cfaceC (same_cface yFz') -cfaceC in qy *.
  by apply: fconnect_cycle (mem_head _ _); rewrite /= rcons_path x'Fq -Lq /=.
rewrite inE => /predU1P[/faceI/edgeI zx | qz']; first by rewrite -zx rz in r'x.
rewrite {}Lq; do [have{q qz'} [q1 q2] := splitPr qz'] in Uq x'Fq qy *.
rewrite -cat_cons cat_uniq mem_cat cat_path last_cat in Uq x'Fq qy *.
rewrite /= in x'Fq *.
have{Uq x'Fq} [[Uq1 Uq12 Uq2] [x'Fq1 /eqP Lq1 zFq2]] := (and3P Uq, and3P x'Fq).
have{qy} [q1y | q2y] := orP qy.
  exists z'; last exists q2 => //.
    by rewrite (fclosed1 diskN_node) edgeK diskN_E inE /= rz.
  apply: contra Uq12 => /(@hasP _ _ (z' :: q2))[t q2t rt].
  have yFt: cface y t by apply: connect_trans (path_connect zFq2 _).
  by apply/hasP; exists y => //; rewrite (scycle_cface scycRr ry rt yFt).
pose rclink := [fun t => face (if t \in r then edge t else t)].
have [c [z'Cc Uc Lc] [sr1c Uq1c]]: exists2 c,
       [/\ fpath rclink z' c, uniq (z' :: c) & last z' c = z]
    &  {subset y :: r1 <= z' :: c} /\ ~~ has (mem (x' :: q1)) (z' :: c).
  have sr1r: {subset r1 <= r}.
    by move=> t r1t; rewrite -(mem_rot i r) Dr mem_behead.
  have cFpL (t : G) c : fpath face t c -> {subset t :: c <= cface (last t c)}.
    move=> tFc u cu; apply: connect_trans (path_connect tFc cu).
    by rewrite cfaceC; apply/connectP; exists c.
  have sFCr t c :
    uniq (t :: c) -> last t c \in r -> fpath face t c -> fpath rclink t c.
  - rewrite lastI rcons_uniq => /andP[Uc _] Lc tFc.
    have RFbase: fun_base id rclink face (mem r) by move=> u v /= /negPf->.
    rewrite -(map_id c) (map_path RFbase) // -(@eq_has _ (mem r)) //.
    apply/hasPn=> u cu; apply: contra Uc => /= ru.
    by rewrite (scycle_cface scycRr Lc ru) // [cface _ _]cFpL ?mem_belast.
  have /=/andP[r1'y Ur1]: uniq (y :: r1) by rewrite -Dr rot_uniq.
  suffices [c2 [yRc2 Uc2 Lc2] [sr1c2 sFc2r1]]: exists2 c2,
       [/\ fpath rclink y c2, uniq c2 & last y c2 = z]
     & {subset r1 <= c2} /\ {subset fband c2 <= fband r1}.
  - have c2F'y t: t \in c2 -> ~~ cface y t.
      move=> c2t; apply: contra r1'y => yFt.
      have /hasP[u r1u tFu]: has (cface t) r1 by apply/sFc2r1/hasP; exists t.
      by rewrite (scycle_cface scycRr _ _ (connect_trans yFt tFu)) // sr1r.
    case/splitPl: {q2}q2y zFq2 Uq12 Uq2 => c1 q2' Lc1.
    rewrite cat_path -cat_cons has_cat cat_uniq => /andP[z'Fc1 _].
    move=> /norP[Uq1c1 _] /andP[Uc1 _].
    exists (c1 ++ c2).
      rewrite cat_path last_cat Lc1 -cons_uniq -cat_cons cat_uniq Uc1 Uc2 andbT.
      rewrite sFCr ?Lc1 //; split=> //; apply/hasP => [[t c2t c1t]].
      by case/negP: (c2F'y t c2t); rewrite -Lc1 [cface _ t]cFpL.
    rewrite -cat_cons has_cat orbA negb_or Uq1c1; split.
      move=> t /predU1P[-> | r1t]; rewrite mem_cat -?Lc1 ?mem_last //.
      by rewrite sr1c2 ?orbT.
    apply/hasP => [[t c2t q1t]]; case/negP: (c2F'y t c2t).
    by rewrite (same_cface yFz') -Lq1 -cface1 [cface _ _]cFpL.
  rewrite {i Dr z' zRy rz yFz' Uq12 Uq2 Lq1 zFq2 q2y r1'y}/z.
  elim: r1 y ry sr1r yRr1 Ur1 => /= [|z r1 IHr] y ry; first by exists nil.
  move/allP=> /=/andP[rz /allP sr1r] /andP[yRz zRr1] /andP[r1'z Ur1].
  have{IHr zRr1 Ur1}[c2 [zRc2 Uc2 Lc2] [sr1c2 sc2r1]] := IHr z rz sr1r zRr1 Ur1.
  move: yRz; rewrite /rlink cface1 => /connectP[_ /shortenP[c1 yFc1 Uc1 _] Lc1].
  have sc1Fz := cFpL _ _ yFc1; rewrite -Lc1 in sc1Fz.
  exists ((face (edge y) :: c1) ++ c2).
    split; last by rewrite last_cat /= -Lc1.
      by rewrite cat_path /= -Lc1 zRc2 andbT {1}/rclink /= ry eqxx sFCr -?Lc1.
    rewrite cat_uniq Uc1 Uc2 andbT; apply: contra r1'z => /hasP[t c2t c1t].
    have /hasP[u r1u tFu]: fband r1 t by apply/sc2r1/hasP; exists t.
    have zFu: cface z u := connect_trans (sc1Fz t c1t) tFu.
    by rewrite (scycle_cface scycRr rz _ zFu) ?sr1r.
  split=> t.
    rewrite inE mem_cat => /predU1P[-> | r1t]; first by rewrite Lc1 mem_last.
    by rewrite orbC sr1c2.
  rewrite [t \in _]has_cat => /orP[/hasP[u c1u tFu] | /sc2r1/hasP[u r1u tFu]].
    apply/hasP; exists z; first exact: mem_head.
    by rewrite (same_cface tFu) cfaceC [cface _ _]sc1Fz.
  by apply/hasP; exists u; first apply: mem_behead.
have [x1 c_nx1 [p [x1Cp Lp] Upc]]: exists2 x1, node x1 \in z' :: c
          & exists2 p, path clink x1 p /\ last x1 p = x'
                    &  ~~ has (mem (z' :: c)) (x1 :: p).
- have{dNx} [x0 rx0 /connectP[p x0'Dp Lp]] := hasP dNx.
  set x0' := finv node x0 in x0'Dp Lp.
  have cycCc: fcycle rclink (z' :: c) by rewrite /= rcons_path z'Cc /= Lc rz.
  have{rx0}: has (mem (z' :: c)) (x0' :: p).
    have cx0: x0 \in z' :: c by rewrite sr1c // -Dr mem_rot.
    have <-: rclink x0 = x0' by rewrite /= rx0 -[x0](f_finv nodeI) nodeK.
    by rewrite (eqP (next_cycle cycCc cx0)) /= (mem_next (_ :: _)) cx0.
  elim: p {x0}x0' x0'Dp Lp => [|x1 p IHp] x0.
    rewrite /= orbF => _ <-{x0} cx; exists x'; first by rewrite edgeK.
    exists nil; rewrite //= orbF; apply: contra Uq1c => cx'.
    by rewrite has_sym /= cx'.
  rewrite {-1 2 4}[@cons]lock /= -lock orbC => /andP[x0Dx1 x1Dp] Lp.
  have [cIp _| Ucp {IHp} cx0] := boolP (has _ _); first exact: IHp cIp.
  have:= cx0; rewrite orFb -mem_next -(eqP (next_cycle cycCc cx0)) /=.
  case/andP: x0Dx1 => /negPf-> x0Cx1 cfx0.
  have [x0nx1 | fx0x1] := clinkP x0Cx1; last by rewrite /= -fx0x1 cfx0 in Ucp.
  exists x1; [by rewrite -x0nx1 | exists (rcons p x')].
    split; last by rewrite last_rcons.
    rewrite rcons_path -Lp /= -{1}[x]edgeK clinkN andbT.
    by apply: sub_path x1Dp => t u /andP[].
  rewrite has_rcons orbCA negb_or Ucp andbT.
  by apply: contra Uq1c; rewrite has_sym /= => ->.
have {}z'Cc: path clink z' c.
  apply: sub_path z'Cc => t _ /eqP <- /=.
  by case: ifP => _; [rewrite -{1}[t]edgeK clinkN | rewrite clinkF].
have [c0 [x1Cc0 Lc0] Ucc0]: exists2 c0,
  path clink x1 c0 /\ clink (last x1 c0) z' & ~~ has (mem (z' :: c)) (x1 :: c0).
- exists (p ++ q1).
    split; last by rewrite last_cat Lp -Lq1 clinkF.
    by rewrite cat_path x1Cp Lp (sub_path _ x'Fq1) //; apply: subrelUr.
  rewrite -cat_cons has_cat negb_or Upc.
  by rewrite has_sym in Uq1c; case/norP: Uq1c.
case/shortenP: x1Cc0 Lc0 => [c1 x1Cc1 Uc1 sc01] Lc1.
have /and3P[] := planarP G planarG (x1 :: c1 ++ z' :: c); split; first 1 last.
- by rewrite cat_path /= x1Cc1 Lc1.
- rewrite last_cat /= Lc mem2_cat mem2_cons (finv_eq_can nodeK) -/z'.
  by rewrite eqxx /= c_nx1 orbT.
rewrite -cat_cons cat_uniq Uc1 Uc andbT; apply: contra Ucc0 => /hasP[t ct c1t].
by apply/hasP; exists t; move: c1t; rewrite //= !inE; case: eqP => // _ /sc01.
Qed.

Let ddart := {x | x \in diskN}.

Definition snipd_edge x := if x \in r then next r x else edge x.

Fact dedge_subproof (u : ddart) : snipd_edge (val u) \in diskN.
Proof.
rewrite /= /snipd_edge diskN_E.
case ru: (val u \in r); first by rewrite mem_next ru.
by rewrite orbC -(fclosed1 diskE_edge) inE /= ru (valP u).
Qed.

Definition snipd_face x := if x \in r then face (edge (prev r x)) else face x.

Fact dface_subproof  (u : ddart) : snipd_face (val u) \in diskN.
Proof.
rewrite /= /snipd_face (fclosed1 diskN_node) diskN_E.
case ru: (val u \in r); first by rewrite edgeK mem_prev ru.
by rewrite orbC (fclosed1 diskE_edge) faceK inE /= ru (valP u).
Qed.

Fact dnode_subproof (u : ddart) : node (val u) \in diskN.
Proof. by rewrite -(fclosed1 diskN_node) (valP u). Qed.

Let dedge u := (sub _ : _ -> ddart) (dedge_subproof u).
Let dnode u := (sub _ : _ -> ddart) (dnode_subproof u).
Let dface u := (sub _ : _ -> ddart) (dface_subproof u).

Fact snipd_subproof : cancel3 dedge dnode dface.
Proof.
move=> u; apply: val_inj; rewrite /= /snipd_edge.
case ru: (val u \in r); rewrite /snipd_face.
  by rewrite mem_next ru edgeK (prev_next Ur).
have dEu: edge (val u) \in diskE.
  by rewrite -(fclosed1 diskE_edge) inE /= ru (valP u).
by case/andP: dEu => /negPf/=->; rewrite edgeK.
Qed.

Definition snip_disk := Hypermap snipd_subproof.
Definition snipd (u : snip_disk) := sval u.

Lemma inj_snipd : injective snipd. Proof. exact: val_inj. Qed.

Lemma codom_snipd : codom snipd =i diskN.
Proof.
move=> z; apply/imageP/idP => [[[y dNy] /= _ -> //] | dNz].
by exists (sub z dNz).
Qed.

Definition snipd_ring := preim_seq snipd r.

Lemma map_snipd_ring : map snipd snipd_ring = r.
Proof. by apply: map_preim => x rx; rewrite codom_snipd diskN_E inE /= rx. Qed.

Lemma ucycle_snipd_ring : ufcycle edge snipd_ring.
Proof.
have UbGd: uniq snipd_ring.
  by rewrite -(map_inj_uniq inj_snipd) map_snipd_ring Ur.
rewrite /ucycle UbGd andbT; apply: (cycle_from_next UbGd) => u b_u.
apply/eqP/inj_snipd; rewrite /= /snipd_edge -/(snipd u) -map_snipd_ring.
by rewrite (mem_map inj_snipd) b_u (next_map inj_snipd UbGd).
Qed.

Lemma cface_snipd : {mono snipd : u v / cface u v}.
Proof.
have homFd: {homo snipd : u v / cface u v}.
  move=> u _ /connectP[p uFp ->].
  elim: p u uFp => //= _ p IHp u /andP[/eqP<- /IHp]; apply: {IHp}connect_trans.
  rewrite /= /snipd_face; case: ifP => ru; last exact: fconnect1.
  by rewrite cfaceC -cface1; apply (prev_cycle cycRr ru).
have homFd' u v :
  ~~ fband snipd_ring u -> cface (snipd u) (snipd v) -> cface u v.
- move=> b'u /connectP[p]; elim: p => [|y p IHp] /= in u b'u *.
    by move=> _ /inj_snipd->.
  case/andP=> /eqP Dy yFp Lp.
  have r'u: (val u \notin r).
    apply: contra b'u => ru; apply/hasP; exists u => //.
    by rewrite -(mem_map inj_snipd) map_snipd_ring.
  have dNy: y \in diskN.
    rewrite (fclosed1 diskN_node) diskN_E (fclosed1 diskE_edge) orbC.
    by rewrite -Dy faceK inE /= r'u (valP u).
  apply: connect_trans {IHp yFp Lp}(IHp (sub y _) _ yFp Lp).
    by rewrite connect1 //= -val_eqE /= /snipd_face (negPf r'u) Dy.
  apply/hasP => [[w b_w yFw]]; case/hasP: b'u; exists w => //.
  apply: connect_trans yFw.
  by rewrite connect1 //= -val_eqE /= /snipd_face (negPf r'u) Dy.
move=> u v; apply/idP/idP; last exact: homFd.
have [b_u | ] := boolP (u \in fband snipd_ring); last exact: homFd'.
have [b_v uFv | ] := boolP (v \in fband snipd_ring); last first.
  by rewrite (cfaceC u) cfaceC; apply: homFd'.
have [[u1 ru1 uFu1] [v1 rv1 vFv1]] := (hasP b_u, hasP b_v).
have u1Fv1: cface (snipd u1) (snipd v1).
  by rewrite (connect_trans (connect_trans _ uFv)) ?homFd ?(cfaceC u1).
rewrite (same_cface uFu1) (same_connect_r cfaceC vFv1) eq_connect0 //.
by apply/inj_snipd/(scycle_cface scycRr); rewrite // -map_snipd_ring map_f.
Qed.

Lemma simple_snipd_ring : simple snipd_ring.
Proof.
have: uniq snipd_ring by rewrite -(map_inj_uniq inj_snipd) map_snipd_ring.
have: all (fun u => snipd u \in r) snipd_ring.
  by rewrite -all_map map_snipd_ring; apply/allP.
rewrite /simple; elim: snipd_ring => //= u p IHp /andP[ru spr] /andP[p'u Up].
rewrite {}IHp {Up}// (contra _ p'u) // => /mapP[v pv uFv].
rewrite (inj_snipd (scycle_cface scycRr ru (allP spr v _) _)) // cface_snipd.
exact/(rootP cfaceC).
Qed.

Lemma scycle_snipd_ring : sfcycle edge snipd_ring.
Proof.
by rewrite /scycle simple_snipd_ring andbT; case/andP: ucycle_snipd_ring.
Qed.

Let rdart := {x | x \notin diskE}.

Fact redge_subproof (u : rdart) : edge (sval u) \notin diskE.
Proof. by rewrite -(fclosed1 diskE_edge) (valP u). Qed.

Definition snipr_node z := if z \in r then prev r z else node z.

Fact rnode_subproof (u : rdart) : snipr_node (sval u) \notin diskE.
Proof.
rewrite /snipr_node.
case: ifPn => [ru | r'u]; first by rewrite inE /= mem_prev ru.
by apply: contra (valP u); rewrite !inE r'u -(fclosed1 diskN_node) => /andP[].
Qed.

Definition snipr_face z :=
  if node (face z) \in r then next r (node (face z)) else face z.

Fact rface_subproof (u : rdart) : snipr_face (sval u) \notin diskE.
Proof.
rewrite /snipr_face.
case: ifPn => [rnfu | r'nfu]; first by rewrite inE /= mem_next rnfu.
apply: contra (valP u) => /andP[_ /= dNfu]; rewrite -[val u]faceK.
by rewrite -(fclosed1 diskE_edge) !inE r'nfu -(fclosed1 diskN_node).
Qed.

Let redge u := (sub _ : _ -> rdart) (redge_subproof u).
Let rnode u := (sub _ : _ -> rdart) (rnode_subproof u).
Let rface u := (sub _ : _ -> rdart) (rface_subproof u).

Fact snipr_subproof : cancel3 redge rnode rface.
Proof.
move=> u; apply: val_inj; rewrite /= /snipr_node /snipr_face edgeK.
have [ru | r'u] := boolP (val u \in r); first by rewrite mem_next ru prev_next.
rewrite edgeK [_ \in r](contraNF _ (valP u)) // => rfeu.
by rewrite inE /= r'u -[sval u]edgeK -(fclosed1 diskN_node) diskN_E inE /= rfeu.
Qed.

Definition snip_rem := Hypermap snipr_subproof.
Definition snipr (u : snip_rem) : G := sval u.
Lemma inj_snipr : injective snipr. Proof. apply: val_inj. Qed.

Lemma codom_snipr : codom snipr =i [predC diskE].
Proof.
move=> z; apply/imageP/idP => [[[y dE'y] _ /= -> //] | dE'z].
by exists (sub z dE'z).
Qed.

Definition snipr_ring : seq snip_rem := preim_seq snipr (rev r).

Lemma map_snipr_ring : map snipr snipr_ring = rev r.
Proof. by apply: map_preim => x rx; rewrite codom_snipr !inE -mem_rev rx. Qed.

Lemma ucycle_snipr_ring : ufcycle node snipr_ring.
Proof.
have Ubr: uniq snipr_ring.
  by rewrite (@map_uniq _ _ snipr) // map_snipr_ring rev_uniq.
rewrite /ucycle Ubr andbT; apply: (cycle_from_next Ubr) => u b_u /=.
rewrite -val_eqE /= /snipr_node -/(snipr u) -mem_rev -(next_rev Ur).
by rewrite -map_snipr_ring map_f // (next_map inj_snipr).
Qed.

Lemma snip_patch : patch snipd snipr snipd_ring snipr_ring.
Proof.
split.
- exact inj_snipd.
- exact inj_snipr.
- exact scycle_snipd_ring.
- exact ucycle_snipr_ring.
- by rewrite map_snipd_ring; apply map_snipr_ring.
- move=> x; rewrite /= map_snipd_ring !inE codom_snipd codom_snipr.
  by rewrite !inE negb_and negbK orbC.
- case=> x dNx; rewrite !inE -(mem_map inj_snipd) map_snipd_ring /= => r'x.
  by rewrite /snipd_edge (negPf r'x).
- by case.
- by case.
move=> u; rewrite inE /= -(mem_map inj_snipr) map_snipr_ring mem_rev /= => r'u.
by rewrite /snipr_node (negPf r'u).
Qed.

Lemma planar_snipd : planar snip_disk.
Proof. by move: planarG; rewrite (planar_patch snip_patch); case/andP. Qed.

Lemma planar_snipr : planar snip_rem.
Proof. by move: planarG; rewrite (planar_patch snip_patch); case/andP. Qed.

End Snip.

Arguments snipd {G planarG r scycRr} u.
Arguments snipr {G planarG r scycRr} u.

Section SnipRot.

(* Disks only depend on the extent of their ring; hence, they are invariant *)
(* under rotation.                                                          *)

Variables (n0 : nat) (G : hypermap) (r : seq G).

Lemma diskN_rot : diskN (rot n0 r) =i diskN r.
Proof.
move=> x; apply: (etrans (has_rot _ _ _) (eq_has _ _)) => y.
by apply: {x y}eq_connect => x y; rewrite /dlink /= mem_rot.
Qed.

Lemma diskE_rot : diskE (rot n0 r) =i diskE r.
Proof. by move=> x; rewrite inE /= mem_rot diskN_rot. Qed.

Lemma diskF_rot : diskF (rot n0 r) =i diskF r.
Proof. by move=> x; rewrite inE /= fband_rot diskN_rot. Qed.

Lemma diskFC_rot : diskFC (rot n0 r) =i diskFC r.
Proof. by move=> x; rewrite !inE fband_rot diskN_rot. Qed.

End SnipRot.
