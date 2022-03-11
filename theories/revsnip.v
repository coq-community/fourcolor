(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype path fingraph.
From fourcolor Require Import hypermap geometry patch sew snip color chromogram.
From fourcolor Require Import coloring kempe.

(******************************************************************************)
(*   Dissecting a connected plain map along a proper ring, and its reverse    *)
(* edge-conjugate. This gives a symmetric cover (compare with snip.v, where   *)
(* the construction is asymmetric).                                           *)
(*   For a hypermap G, and assuming r : seq G is a ring, we define            *)
(*    proper_ring r <=> r is non-empty and not an E-path of size 2.           *)
(* nontrivial_ring m r <=> there are more than m faces in both strictly       *)
(*                      inside and strictly outside r, i.e., included in      *)
(*                      diskF r and diskFC r, respectively.                   *)
(*       rev_ring r <=> the dual of a ring r, that goes, around the outside   *)
(*                      of r, though the same faces as r, in reverse order,   *)
(*                   := rev (map edge r).                                     *)
(*    chord_ring r x == the ring consisting of x followed by a portion of r,  *)
(*                      when x is a "chord" of r, linking two faces of r,     *)
(*                      i.e., both x and edge x are in fband r.               *)
(* The properties established here feed directly into birkhoff.v; the chord   *)
(* constructions are also used in embed.v when using induction over the disk  *)
(* size of a ring.                                                            *)
(*   If geoG : planar_bridgeless_plain_connected, plG : planarG, and          *)
(* cycRr : scycle rlink r, then we also define:                               *)
(*    rev_snip_disk geoG plG cycRr == the disk hypermap obtained by cutting   *)
(*         rev_ring r, and whose dart set is the exact complement of diskN r. *)
(*     rev_snip_rem geoG plG cycRr == the corresponding remainder hypermap.   *)
(*            rev_snipd, rev_snipr == the injections to G from the above.     *)
(*  rev_snipd_ring, rev_snipr_ring == the border rings for the above.         *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section ProperRing.

(* A proper ring is a non-empty ring that is NOT an edge orbit.           *)
(* A nontrivial ring of order m must have more that m face orbits in both *)
(* its inner and outer face disks.                                        *)

Variables (n0 : nat) (G : hypermap).
Hypothesis plainG : plain G.

Definition proper_ring (r : seq G) : bool :=
  match r with
  | [:: _, _, _ & _] => true
  | [:: x; y] => edge x != y
  | _ => false
  end.

Lemma size_proper_ring r : 2 < size r -> proper_ring r.
Proof. by case: r => [|x [|y [|z r]]]. Qed.

Lemma proper_ring_rot r : proper_ring (rot n0 r) = proper_ring r.
Proof.
case lt2r: (2 < size r); first by rewrite !size_proper_ring ?size_rot.
case: n0 r lt2r => [|[|i]] [|x [|y [|z r]]] //= _.
by rewrite (canF_eq (plain_eq plainG)) eq_sym.
Qed.

Definition nontrivial_ring m (r : seq G) :=
  (m < fcard face (diskF r)) && (m < fcard face (diskFC r)).

Lemma fcard0P (A : pred G) :
  fclosed face A -> reflect (exists x, x \in A) (0 < fcard face A).
Proof.
move=> clFA; rewrite ltnNge leqn0.
apply: (iffP pred0Pn) => [[x /andP[]] | [x]] /= Ax; first by exists x.
exists (froot face x); rewrite (roots_root cfaceC).
by rewrite -(closed_connect clFA (connect_root _ x)).
Qed.

Lemma fcard1P (A : pred G) :
    fclosed face A ->
  reflect (exists2 x, x \in A & exists2 y, y \in A & ~~ cface x y)
          (1 < fcard face A).
Proof.
move=> clAf; apply: (iffP idP) => [lt1fA | [x Ax [y Ay not_xFy]]].
  have /card_gt0P[x /andP[/= rFx Ax]] := ltnW lt1fA; exists x => //.
  rewrite [fcard _ _](cardD1 x) inE /= rFx Ax ltnS in lt1fA.
  have /card_gt0P[y /and3P[/= neq_xy rFy Ay]] := lt1fA; exists y => //.
  by rewrite cfaceC (sameP (rootP cfaceC) eqP) (eqP rFx) (eqP rFy).
rewrite [fcard _ _](cardD1 (froot face x)) (cardD1 (froot face y)).
rewrite !inE !(roots_root cfaceC) -!(closed_connect clAf (connect_root _ _)).
by rewrite Ax Ay (sameP eqP (rootP cfaceC)) cfaceC not_xFy.
Qed.

Lemma nontrivial0P r :
  reflect ((exists x, x \in diskF r) /\ (exists x, x \in diskFC r))
          (nontrivial_ring 0 r).
Proof.
rewrite /nontrivial_ring.
have [nzFr|] := fcard0P (diskF_face r); last by right; case.
by apply: (iffP (fcard0P (diskFC_face r))) => [|[]].
Qed.

Lemma nontrivial1P r :
 reflect ((exists2 x, x \in diskF r & exists2 y, y \in diskF r & ~~ cface x y)
      /\ (exists2 x, x \in diskFC r & exists2 y, y \in diskFC r & ~~ cface x y))
   (nontrivial_ring 1 r).
Proof.
rewrite /nontrivial_ring.
have [nzFr|] := fcard1P (diskF_face r); last by right; case.
by apply: (iffP (fcard1P (diskFC_face r))) => [|[]].
Qed.

End ProperRing.

Section RevSnip.

Variable G : hypermap.
Hypothesis geoG : planar_bridgeless_plain_connected G.
Let bridge'G : bridgeless G := geoG.
Let plainG : plain G := geoG.
Let ccG : connected G := geoG.
Let ee := plain_eq plainG.
Let e'id := plain_neq plainG.

Definition rev_ring (r : seq G) := rev (map edge r).

Lemma rev_rev_ring r : rev_ring (rev_ring r) = r.
Proof. by rewrite /rev_ring map_rev revK (mapK ee). Qed.

Lemma proper_rev_ring r : proper_ring (rev_ring r) = proper_ring r.
Proof.
case lt2r: (2 < size r); first by rewrite !size_proper_ring ?size_rev ?size_map.
by case: r lt2r => [|x [|y []]] //= _; rewrite ee eq_sym.
Qed.

(* We use a redundant assumption to facilitate matching in lemmas with        *)
(* dependently typed terms.                                                   *)
Hypothesis planarG : planar G.

Variable r : seq G.
Hypothesis scycRr : scycle rlink r.
Let cycRr:= scycle_cycle scycRr.
Let sFr := scycle_simple scycRr.
Let Ur := scycle_uniq scycRr.

Lemma mem_rev_ring x : (x \in rev_ring r) = (edge x \in r).
Proof. by rewrite -{1}[x]ee mem_rev (mem_map edgeI). Qed.

Lemma cycle_rev_ring : cycle rlink (rev_ring r).
Proof.
case Dr: r => [|x p] //.
rewrite (cycle_path x) -{2}Dr /rev_ring rev_cons last_rcons.
apply/(pathP x) => i; rewrite size_rev size_map => lt_i_r.
rewrite -rev_rcons -map_rcons !nth_rev ?size_map ?size_rcons ?leqW //.
rewrite subSn //; set j := size r - i.+1.
have ltjr: j < size r by rewrite -subSn // subSS leq_subr.
rewrite !(nth_map x) ?size_rcons // /rlink cfaceC ee.
have:= cycRr; rewrite Dr in ltjr * => /(pathP x)/(_ j).
by rewrite -rcons_cons nth_rcons size_rcons ltjr; apply.
Qed.

Lemma froot_face_rev_ring :
  map (froot face) (rev_ring r) = rev (rot 1 (map (froot face) r)).
Proof.
rewrite map_rev -map_rot; congr (rev _).
case: r cycRr => // x0 p; rewrite rot1_cons /=; move: {1 3}x0.
by elim: p => [|y p IHp] x /= /andP[xRy yRp]; rewrite (rootP cfaceC xRy) ?IHp.
Qed.

Lemma simple_rev_ring : simple (rev_ring r).
Proof. by rewrite /simple froot_face_rev_ring rev_uniq rot_uniq. Qed.

Lemma scycle_rev_ring : scycle rlink (rev_ring r).
Proof. by rewrite /scycle cycle_rev_ring simple_rev_ring. Qed.
Let scycRrr := scycle_rev_ring.

Lemma fband_rev_ring : fband (rev_ring r) =i fband r.
Proof.
move=> x; apply/hasP/hasP => [] [y r_y xFy].
  rewrite mem_rev_ring in r_y.
  exists (next r (edge y)); first by rewrite mem_next.
  by rewrite (same_cface xFy) -{1}[y]ee [cface _ _](next_cycle cycRr).
exists (edge (prev r y)); first by rewrite mem_rev_ring ee mem_prev.
by rewrite (same_cface xFy) cfaceC [cface _ _](prev_cycle cycRr).
Qed.

Section RingPartitions.

Hypothesis nt_r : proper_ring r.

Lemma pick_in_ring : {x | x \in r}.
Proof. by case: r nt_r => // x p; exists x; rewrite mem_head. Qed.

Lemma diskN_edge_ring x : x \in r -> (edge x \in diskN r) = false.
Proof.
move=> r_x; rewrite diskN_E inE /= -(fclosed1 (diskE_edge geoG _)) //.
rewrite inE /= r_x orbF; apply: contraTF nt_r => r_ex.
have Dex: edge x = next r x.
  by apply: (scycle_cface scycRr) (next_cycle cycRr r_x); rewrite ?mem_next.
have Dx: x = next r (edge x).
  apply: (scycle_cface scycRr); rewrite ?mem_next //.
  by rewrite -{1}[x]ee; apply: (next_cycle cycRr r_ex).
have [i p Dr] := rot_to r_x; rewrite -(proper_ring_rot i) //.
move: Dex Dx Ur; rewrite -!(next_rot i Ur) -(rot_uniq i) {i}Dr.
case: p => [|y [|z p]] //= ->; rewrite !eqxx ?negbK // !inE eq_sym.
by case: ifP => // _ ->; rewrite eqxx.
Qed.

Lemma diskN_rev_ring : diskN (rev_ring r) =i [predC diskN r].
Proof.
case: pick_in_ring => [y r_y] x; move: r_y; rewrite inE /= -(ee y).
have{y} [p xCp ->] := connected_clink x (edge y) ccG.
elim: p x xCp => [|y p IHp] x /= => [_ r_ex | /andP[xCy yCP] Lp].
  by rewrite diskN_E inE /= mem_rev_ring r_ex /= -(ee x) diskN_edge_ring.
have [-> | fxy] := clinkP xCy.
  by rewrite -!(fclosed1 (diskN_node _) y) //; apply: IHp.
rewrite diskN_E inE /= mem_rev_ring.
case r_ex: (edge x \in r); first by rewrite -[x]ee diskN_edge_ring.
rewrite (fclosed1 (diskE_edge geoG scycRrr)) diskN_E 4!inE /=.
rewrite mem_rev_ring negb_or ee; apply: andb_id2l => r'x.
rewrite (fclosed1 (diskE_edge geoG scycRr)) inE /= r_ex.
by rewrite (canRL edgeK (ee x)) fxy -!(fclosed1 (diskN_node _)); apply: IHp.
Qed.

Lemma diskF_rev_ring : diskF (rev_ring r) =i [predD [predC diskN r] & fband r].
Proof. by move=> x; rewrite !inE diskN_rev_ring fband_rev_ring. Qed.

Definition chord_ring x := x :: (arc r (fproj r (edge x)) (fproj r x)).

Lemma scycle_chord_ring x :
  x \in fband r -> edge x \in fband r -> scycle rlink (chord_ring x).
Proof.
rewrite /chord_ring; case/fprojP; set y1 := fproj r x => r_y1 xFy1.
case/fprojP; set y2 := fproj r _ => r_y2 exFy2.
have neq_y21: y2 != y1.
  apply: contraNneq bridge'G => eq_y21; apply/existsP; exists x.
  by rewrite (same_cface xFy1) cfaceC -eq_y21.
case/andP: scycRr; have [i p1 p2 <- _ Dr] := rot_to_arc Ur r_y2 r_y1 neq_y21.
rewrite -(rot_cycle i) -(simple_rot i) Dr /= rcons_cat cat_path /=.
rewrite {2}/rlink -(same_connect_r cfaceC xFy1) => /and3P[y2Rp1 p1Rx _].
rewrite -cat_cons -cat_rcons simple_cat -rot1_cons simple_rot => /andP[sFxp1 _].
rewrite /scycle (cycle_path x) /= [rlink _ _]p1Rx y2Rp1 [rlink _ _]exFy2.
by rewrite /simple /= (rootP cfaceC xFy1).
Qed.

Variable x : G.
Hypothesis dEx : x \in diskE r.
Hypotheses (rFx : x \in fband r) (rFex : edge x \in fband r).

Let dEe y : (edge y \in diskE r) = (y \in diskE r).
Proof. by rewrite -(fclosed1 (diskE_edge geoG scycRr)). Qed.
Let rFeex : edge (edge x) \in fband r. Proof. by rewrite ee. Qed.
Let dEex : edge x \in diskE r. Proof. by rewrite dEe. Qed.

Let x1 := fproj r x.
Let x2 := fproj r (edge x).
Let rx1 : x1 \in r. Proof. by case/fprojP: rFx. Qed.
Let rx2 : x2 \in r. Proof. by case/fprojP: rFex. Qed.
Let xFx1 : cface x x1. Proof. by case/fprojP: rFx. Qed.
Let xFx2 : cface (edge x) x2. Proof. by case/fprojP: rFex. Qed.
Let neq_x12 : x1 != x2.
Proof.
apply: contraNneq bridge'G => eq_x12; apply/existsP; exists x.
by rewrite (same_cface xFx1) cfaceC eq_x12.
Qed.

Let r1 := arc r x1 x2.
Let r2 := arc r x2 x1.
Let ix := let: RotToArcSpec i _ _ _ _ _ := rot_to_arc Ur rx1 rx2 neq_x12 in i.
Let Dr : rot ix r = r1 ++ r2.
Proof. by rewrite /ix /r1 /r2; case: rot_to_arc => i p1 p2 <- <-. Qed.
Let Dr12 : r =i [predU r1 & r2].
Proof. by move=> y; rewrite -(mem_rot ix) Dr mem_cat. Qed.
Let Dr1 : {p1 | r1 = x1 :: p1}.
Proof. by have [i p1 p2] := rot_to_arc Ur rx1 rx2 neq_x12; exists p1. Qed.
Let Dr2 : {p2 | r2 = x2 :: p2}.
Proof. by have [i p1 p2] := rot_to_arc Ur rx1 rx2 neq_x12; exists p2. Qed.

Let cr1 := chord_ring x.
Let cr2 := chord_ring (edge x).
Let Dcr1 : cr1 = x :: r2. Proof. by []. Qed.
Let Dcr2 : cr2 = edge x :: r1. Proof. by rewrite /cr2 /chord_ring ee. Qed.

Let d1Ee y : (edge y \in diskE cr1) = (y \in diskE cr1).
Proof. by rewrite -(fclosed1 (diskE_edge geoG (scycle_chord_ring _ _))). Qed.
Let d2Ee y : (edge y \in diskE cr2) = (y \in diskE cr2).
Proof. by rewrite -(fclosed1 (diskE_edge geoG (scycle_chord_ring _ _))). Qed.

Lemma proper_chord_ring : proper_ring cr1.
Proof.
rewrite Dcr1; have [[|z p] -> //=] := Dr2.
by apply: contraTneq dEex => ->; rewrite inE /= rx2.
Qed.

Lemma diskN_chord_ring : diskN cr1 =i [predD diskN r & diskN cr2].
Proof.
move=> y; suffices: (y \in diskN cr1) + (y \in diskN cr2) = (y \in diskN r).
  by rewrite inE /= /in_mem /=; do 3?case: (diskN _ y).
have{y} [p xCp ->] := connected_clink x y ccG.
elim/last_ind: p xCp => [_ | p y IHp] /=.
  rewrite !{1}diskN_E !{1}[x \in _]inE /= dEx orbT addnC -{1}d2Ee Dcr2 2!inE /=.
  by case/andP: dEx; rewrite !mem_head eq_sym e'id /= Dr12 => /norP[/=/negPf->].
rewrite last_rcons rcons_path !{1}(fclosed1 (diskN_node _) y) => /andP[xCp pCy].
have:= IHp xCp; have{pCy} [<- //| /(canRL faceK)->] := clinkP pCy.
move/node: y => y; rewrite !{1}diskN_E {-3}/in_mem /= {1}d1Ee d2Ee.
rewrite {1 3}Dcr1 {1 3}Dcr2 !in_cons (can_eq ee) (canF_eq ee).
have [-> _ | _] := altP (y =P edge x).
  rewrite e'id /= dEex orbT d1Ee inE /= mem_head orbF.
  by case/andP: dEex; rewrite /= Dr12 => /norP[/= _ /negPf->].
have [-> _ | _] /= := altP (y =P x).
  rewrite dEx orbT -d2Ee Dcr2 inE /= mem_head orbF.
  by case/andP: dEx; rewrite /= Dr12 => /norP[/= /negPf->].
have [r_y|] := boolP (y \in r); last rewrite Dr12 => /norP[/=/negPf-> /negPf->].
  rewrite -diskN_E (diskN_edge_ring r_y) /= [diskE]lock.
  do 2![rewrite addnC orbC; case: (y \in _) => //] => _; rewrite !orbF.
  move: Ur r_y; rewrite -(rot_uniq ix) Dr12 Dr cat_uniq inE orbC /=.
  by case/and3P=> _ /hasPn/(_ y)/implyP; case: (y \in r2) => /= [/negPf| _ _]->.
rewrite -(dEe y) {-3 6}[diskE]lock !inE Dr12 !inE /=.
rewrite -{1 3}lock -(d1Ee y) -lock -(d2Ee y).
case r1ey: (edge y \in r1).
  rewrite /= orbC; case: {1 2}(edge y \in diskE cr1) => // _.
  by rewrite inE /= Dcr2 mem_behead.
by case r2ey: (edge y \in r2) => //= [] [<-]; rewrite {1}inE /= mem_behead.
Qed.

Lemma fband_chord_ring : [predU fband cr1 & fband cr2] =i fband r.
Proof.
move=> y; rewrite Dcr1 Dcr2 !inE !fband_cons orbAC orbA -orbA -fband_cat -Dr.
by rewrite fband_rot orb_idl // => /orP[] /(closed_connect (fbandF r))->.
Qed.

Lemma diskF_chord_ring : diskF cr1 =i [predD diskF r & diskF cr2].
Proof.
move=> y; rewrite [diskF cr1]lock [cr2]lock !inE -fband_chord_ring !inE -!lock.
case: (y \in fband cr2) / (altP hasP) => [[z cr2z yFz] | _]; last first.
  by rewrite inE /= {1}diskN_chord_ring inE /= orbF andbCA.
rewrite orbT andbF (closed_connect (diskF_face _) yFz) inE /= diskN_chord_ring.
by rewrite inE /= diskN_E inE /= cr2z andbF.
Qed.

Lemma nontrivial_chord_ring :
    x2 != next r x1 -> (exists y, diskF cr1 y) ->
  nontrivial_ring 0 cr1 /\ size cr1 < size r.
Proof.
rewrite -(next_rot ix Ur) -(size_rot ix r) Dr.
have [[|x3 p1] Dp1] := Dr1; rewrite Dp1.
  by have [p2 ->] := Dr2; rewrite /= !eqxx.
move=> _ nt_cr1F; split; last by rewrite size_cat Dcr1 /= !addSnnS leq_addl.
have r1x3: x3 \in r1 by rewrite Dp1 mem_behead // mem_head.
apply/nontrivial0P; split=> //; exists x3; apply/andP; split=> /=; last first.
  by rewrite inE /= diskN_chord_ring inE /= diskN_E inE /= Dcr2 mem_behead.
have r_x3: x3 \in r by rewrite Dr12 !inE r1x3.
have:= Ur; rewrite -(rot_uniq ix) Dr Dcr1 Dp1 /= mem_cat orbC inE.
apply: contraL; rewrite fband_cons cfaceC (same_cface xFx1).
case/orP=> [|/hasP[y r2y]] /(scycle_cface scycRr)->; rewrite ?eqxx //.
  by rewrite r2y andbF.
by rewrite Dr12 !inE r2y orbT.
Qed.

End RingPartitions.

Section NonTrivialRing.

Variable m : nat.
Hypothesis nt_r : nontrivial_ring m r.

Lemma nontrivial_ring_proper : proper_ring r.
Proof.
case Dr: {1 3}r (andP nt_r) => [|x r1] [ntFr ntFCr].
  by rewrite [fcard _ _]eq_card0 // in ntFr => y; apply: andbF. 
case: r1 {ntFr} => [|ex [|z r2]] // in Dr *.
  by have:= cycRr; rewrite Dr /= [rlink _ _]cfaceC bridgeless_cface.
apply: contraTneq ntFCr => Dex; rewrite [fcard _ _]eq_card0 // => y.
suffices dNy: y \in diskN r by rewrite !inE dNy !andbF.
have{y} [p xCp ->] := connected_clink x y ccG.
have rx: x \in r by rewrite Dr mem_head.
elim/last_ind: p xCp => [|p y IHp]; first by rewrite /= diskN_E !inE rx.
rewrite last_rcons rcons_path (fclosed1 (diskN_node r)) => /andP[/IHp dNp].
case/clinkP=> [<- // | /(canRL faceK) enx]; rewrite diskN_E inE /= orbC.
rewrite (fclosed1 (diskE_edge geoG scycRr)) inE /= -{2}enx dNp andbT.
by rewrite -(mem_rot 1) Dr !inE -Dex (can_eq ee) (canF_eq ee) orNb.
Qed.
Let r_ok := nontrivial_ring_proper.

Lemma nontrivial_rev_ring : nontrivial_ring m (rev_ring r).
Proof.
have [[[ntFr ntFCr] rN] rF] := (andP nt_r, diskN_rev_ring r_ok, fband_rev_ring).
apply/andP; split; [congr (_ <= _): ntFCr | congr (_ <= _): ntFr].
  by apply: eq_n_comp_r => x; rewrite !inE /= rN rF.
by apply: eq_n_comp_r => x; rewrite !inE /= rN -rF negbK.
Qed.

Local Notation Gd := (snip_disk planarG scycRr).
Local Notation bGd := (snipd_ring planarG scycRr).
Let pfd x : pred Gd := preim snipd (cface x).

Let pfdP x yd :
  cface x (snipd yd) -> {zd | pick (pfd x) = Some zd & cface yd zd}.
Proof.
move=> xFyd; case: pickP=> [zd xFzd | /(_ yd)/negP//]; exists zd => //.
by rewrite -cface_snipd -(same_cface xFyd).
Qed.

Definition rev_snipd_disk := snip_disk planarG scycRrr.

Definition rev_snipr_disk := snip_rem planarG scycRrr.

Definition rev_snipd_ring : seq rev_snipd_disk :=
  snipd_ring planarG scycRrr.

Definition rev_snipr_ring : seq rev_snipr_disk :=
  snipr_ring planarG scycRrr.

Lemma rev_snipr_ring_eq : map snipr rev_snipr_ring = map edge r.
Proof. by rewrite /rev_snipr_ring map_snipr_ring revK. Qed.

Local Notation Grd := rev_snipd_disk.
Local Notation bGrd := rev_snipd_ring.
Local Notation Grr := rev_snipr_disk.
Local Notation bGrr := rev_snipr_ring.
Let ppGr := snip_patch planarG scycRrr.

Let pfrr x : pred Grr := preim snipr (cface x).
Let pfrrP x yr :
  cface x (snipr yr) -> {zr | pick (pfrr x) = Some zr & cface yr zr}.
Proof.
move=> xFyr; case: pickP => [zr xFzr | /(_ yr)/negP//]; exists zr => //.
by rewrite (patch_face_r (snip_patch _ _)) -(same_cface xFyr).
Qed.

Lemma rev_ring_cotrace et : ring_trace bGd et <-> ring_trace (rotr 1 bGrr) et.
Proof.
set pd := snipd_ring planarG scycRr; set pr := rotr 1 bGrr.
have eqFpdr: map (froot face) (map snipr pr) = map (froot face) (map snipd pd).
  rewrite /pd map_snipd_ring // /pr !map_rotr map_snipr_ring map_rev.
  by rewrite froot_face_rev_ring revK rotK.
split=> [[kd [kdE kdF]] | [kr [krE krF]]] ->{et}.
  pose kr (xr : Grr) := oapp kd Color0 (pick (pfd (snipr xr))).
  have plainGrr: plain rev_snipr_disk.
    by move: plainG; rewrite (plain_patch ppGr) => /andP[].
  have krF: invariant face kr =1 Grr.
    move=> xr; apply/eqcP; congr (oapp kd _ _); apply: eq_pick => yd.
    by apply: same_cface; rewrite -(patch_face_r ppGr) cfaceC fconnect1.
  have krE xr: snipr xr \notin rev_ring r -> (kr (edge xr) == kr xr) = false.
    set x := snipr xr => rr'x; rewrite /kr.
    have{rr'x} /imageP[xd _ Dx]: x \in codom (snipd : Gd -> G).
      apply/negbNE; rewrite codom_snipd -[_ \notin _]diskN_rev_ring //.
      by rewrite diskN_E negb_or /= rr'x (valP xr).
    have [|yd -> xdFyd /=] := @pfdP x xd; first by rewrite Dx.
    have [|zd -> fexdFzd /=] := @pfdP (edge x) (face (edge xd)).
      by rewrite Dx -{1}[xd]edgeK cface1 nodeK.
    rewrite -(fconnect_invariant kdF xdFyd) -(fconnect_invariant kdF fexdFzd).
    by rewrite (eqcP (kdF _)); apply: kdE.
  exists kr; [split=> // xr | congr (trace _)].
    have [rr_x | /krE//] := boolP (snipr xr \in rev_ring r).
    rewrite /= eq_sym -{1}[xr]plain_eq //; apply: krE.
    rewrite !mem_rev_ring in rr_x *.
    by have:= diskN_edge_ring r_ok rr_x; rewrite ee diskN_E => /norP[].
  elim: pd pr eqFpdr => [|xd pd IHpd] [|xr pr] //=.
  case=> /(rootP cfaceC) xdFxr /IHpd->; congr (_ :: _); rewrite /kr.
  by have [yd -> xdFyd /=] := pfdP xdFxr; apply: fconnect_invariant xdFyd.
pose kd (xd : Gd) := oapp kr Color0 (pick (pfrr (snipd xd))).
have kdF: invariant face kd =1 Gd.
  move=> xd; apply/eqcP; congr (oapp kr _ _); apply: eq_pick => yr.
  by apply: same_cface; rewrite cface_snipd cfaceC fconnect1.
exists kd; [split=> // xd | congr (trace _)].
  rewrite /= -(eqcP (kdF (edge xd))) -{2}[xd]edgeK; move: {xd}(face _) => xd.
  rewrite /kd; set x := snipd xd.
  have /imageP[nxr _ Dnx]: node x \in codom (snipr : Grr -> G).
    rewrite codom_snipr // !inE diskN_rev_ring // !inE andbC.
    by rewrite -(fclosed1 (diskN_node r)) (valP xd).
  have [|yr -> nxFyr /=] := @pfrrP (node x) nxr; first by rewrite -Dnx.
  have [|zr -> xFzr /=] := @pfrrP x (edge nxr). 
    by rewrite (canRL nodeK Dnx) -cface1.
  rewrite -(fconnect_invariant krF nxFyr) -(fconnect_invariant krF xFzr).
  exact: krE.
elim: pd pr eqFpdr => [|xd pd IHpd] [|xr pr] //=.
case=> /esym/(rootP cfaceC) xrFxd /IHpd->; congr (_ :: _).
by rewrite /kd; have [yr -> /= /fconnect_invariant->] := pfrrP xrFxd.
Qed.

Lemma ring_disk_closed : cubic G -> Kempe_closed (ring_trace bGd).
Proof.
move=> cubicG et; move/rev_ring_cotrace=> tr_et.
have geoGrr: (ucycle_planar_plain_quasicubic (rotr 1 bGrr)).
  split; last exact: (planar_snipr planarG scycRrr).
  split; last by rewrite /ucycle rot_cycle rotr_uniq; case: ppGr.
  split; first by have:= plainG; rewrite (plain_patch ppGr) => /andP[].
  have:= cubicG; rewrite (cubic_patch ppGr) => /andP[_]; apply: etrans.
  by apply: eq_subset => x; rewrite !inE mem_rotr.
have{tr_et} [tr_et [w etMw rUw]] := Kempe_map geoGrr tr_et.
split=> [g | {tr_et}]; first exact/rev_ring_cotrace.
by exists w => {et etMw}// et /rUw/rev_ring_cotrace.
Qed.

Lemma colorable_from_ring et :
  ring_trace bGd et -> ring_trace bGrd (rev et) -> four_colorable G.
Proof.
case/rev_ring_cotrace=> kr col_kr Det tr_etr.
apply/(colorable_patch ppGr); exists (rev et) => //; exists kr => //.
by rewrite revK Det map_rotr -trace_rot rotrK.
Qed.

Lemma ring_disk_chord :
    ~~ chordless bGd ->
  exists2 r', scycle rlink r' & @nontrivial_ring G 0 r' /\ size r' < size r.
Proof.
have Id : injective (snipd : Gd -> G) by apply: inj_snipd.
have Dbd : map snipd bGd = r by apply: map_snipd_ring.
have Ubd : uniq bGd := ucycle_uniq (ucycle_snipd_ring _ _).
case/subsetPn=> xd; rewrite -(mem_map Id) Dbd => rx.
case/pred0Pn=> yd /andP[/adjP[zd]]; rewrite [rlink _ _]cface1 -!cface_snipd.
rewrite -[snipd (face _)]nodeK -cface1 [node _](congr1 snipd (edgeK zd)) !inE.
rewrite -!(inj_eq Id) -(next_map Id Ubd) -(prev_map Id Ubd) -(mem_map Id) {}Dbd.
move/snipd: xd rx; move/snipd: yd zd => y [z dNz] x rx /= xFz zRy.
rewrite -(canF_eq (prev_next Ur)) -(eq_sym x) => /and3P[x1'y y1'x ry].
have rFz: z \in fband r by apply/hasP; exists x; rewrite // cfaceC.
have rFez: edge z \in fband r by apply/hasP; exists y.
have dEz: z \in diskE r.
  rewrite !inE dNz andbT; apply: contra x1'y => rz.
  rewrite (scycle_cface scycRr rx rz xFz).
  apply/eqP/(scycle_cface scycRr); rewrite ?mem_next // -(same_cface zRy).
  exact: (next_cycle cycRr rz).
have dEez: edge z \in diskE r by rewrite -(fclosed1 (diskE_edge _ _)).
have rF := scycle_fproj scycRr.
have rFz_x: fproj r z = x by rewrite -(fproj_cface r xFz) rF.
have{rF} rFez_y: fproj r (edge z) = y by rewrite (fproj_cface r zRy) rF.
have [|t dFt]:= fcard0P (diskF_face r) _; first by case/andP: nt_r => /subnKC<-.
have [dzFt | ] := boolP (t \in diskF (chord_ring z)).
  exists (chord_ring z); first exact: scycle_chord_ring.
  by apply: nontrivial_chord_ring; rewrite ?rFz_x ?rFez_y //; exists t.
rewrite diskF_chord_ring // inE /= dFt andbT negbK => dezFt.
exists (chord_ring (edge z)); first by apply: scycle_chord_ring; rewrite ?ee.
by apply: nontrivial_chord_ring; rewrite ?ee ?rFz_x ?rFez_y //; exists t.
Qed.

End NonTrivialRing.

End RevSnip.
