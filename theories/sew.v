(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype path fingraph.
From fourcolor Require Import hypermap geometry color patch.

(******************************************************************************)
(*   This file provides the means for "sewing" two hypermaps Gd and Gr along  *)
(* a common cycle; the resulting map G will satisfy the "patch" predicate.    *)
(*  If Gd, Gr : hypermap, bGd : seq Gd, bGr : seq Gr, then                    *)
(*    sew_map cycEbGd cycNbGr sz_bG == a hypermap obtained by "glueing" Gd    *)
(*      Gr along bGd and BGr, provided (cycEbGd) bGq is a simple E-cycle of   *)
(*      of Gd, (cycNbGr) bGr is a node (uniq N-cycle) of Gr, and (sz_bG) both *)
(*      cycles have the same length.                                          *)
(*    sew_dart Gd bGr == the dart type of sew_map _ _ _ above.                *)
(*            sew_tag == the 2-element tag type for sew_map.                  *)
(*         sewd bGr x == the image of x : Gd in sew_dart Gd bGr.              *)
(*      sewr Gd bGr y == the image of x : Gr in sew_dart Gd bGr.              *)
(* When G := sew_map cycEbGd cycNbGr sz_bG is defined, we always have         *)
(*  patch (sewd Gd bGr : Gd -> G) (sewr Gd bGr : Gr -> G) bGd bGr             *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Sew.

Variables (Gd Gr : hypermap) (bGd : seq Gd) (bGr : seq Gr).

Hypothesis cycEbGd : sfcycle edge bGd.
Hypothesis cycNbGr : ufcycle node bGr.
Hypothesis sz_bG : size bGd = size bGr.

Let EbGdE xd : xd \in bGd -> forall yd, cedge xd yd = (yd \in bGd).
Proof. by move=> b_xd yd; apply: fconnect_cycle; case/andP: cycEbGd. Qed.

Let EbGdE1 xd : edge xd \in bGd -> xd \in bGd.
Proof. by move=> b_exd; rewrite -(EbGdE b_exd) cedgeC fconnect1. Qed.

Let EbGrN xr : xr \in bGr -> forall yr, cnode xr yr = (yr \in bGr).
Proof. by move=> b_xr yr; apply: fconnect_cycle; case (andP cycNbGr). Qed.

Let EbGrN1 xr : node xr \in bGr -> xr \in bGr.
Proof. by move=> b_xr; rewrite -(EbGrN b_xr) cnodeC fconnect1. Qed.

Let in_bGd xd : {xr0 : Gr | xd \in bGd} + {xd \notin bGd}.
Proof.
case b_xd: (xd \in bGd); [left | by right].
by case: bGr b_xd sz_bG => [|xr0 pr]; [case bGd | exists xr0].
Qed.

Let in_bGr xr : {xd0 : Gd | xr \in bGr} + {xr \notin bGr}.
Proof.
case b_xr: (xr \in bGr); [left | by right].
by case: bGd b_xr sz_bG => [|xd0 pd]; [case bGr | exists xd0].
Qed.

Let hdr xr0 xd := nth xr0 (rev bGr) (index xd bGd).

Let hrd xd0 xr := nth xd0 bGd (index xr (rev bGr)).

Let bGr_hdr {xr0} xd : xd \in bGd -> hdr xr0 xd \in bGr.
Proof.
by move=> b_xd; rewrite -mem_rev mem_nth // size_rev -sz_bG index_mem.
Qed.

Let bGd_hrd {xd0} xr : xr \in bGr -> hrd xd0 xr \in bGd.
Proof.
by move=> b_xr; rewrite mem_nth // sz_bG -size_rev index_mem mem_rev.
Qed.

Let hrd_hdr {xd0 xr0} xd : xd \in bGd -> hrd xd0 (hdr xr0 xd) = xd.
Proof.
move=> b_xd; rewrite /hrd /hdr index_uniq ?nth_index //.
  by rewrite size_rev -sz_bG index_mem.
by rewrite rev_uniq; case: (andP cycNbGr).
Qed.

Let hdr_hrd {xd0 xr0} xr : xr \in bGr -> hdr xr0 (hrd xd0 xr) = xr.
Proof.
move=> b_xr; rewrite /hrd /hdr index_uniq ?nth_index ?mem_rev //.
  by rewrite sz_bG -size_rev index_mem mem_rev.
by apply simple_uniq; case: (andP cycEbGd).
Qed.

Let node_hdr {xr0} xd :
  xd \in bGd -> node (hdr xr0 xd) = hdr xr0 (node (face xd)).
Proof.
have [[cEbd /simple_uniq Ubd] [cNbr Ubr]] := (andP cycEbGd, andP cycNbGr).
move=> b_xd; set xr := hdr xr0 xd; have b_xr: xr \in bGr by apply: bGr_hdr.
rewrite -(eqP (prev_cycle cEbd b_xd)) edgeK (eqP (next_cycle cNbr b_xr)).
rewrite -(revK bGr) next_rev ?rev_uniq // !prev_nth b_xd mem_rev b_xr.
case DbGr: {1}(rev bGr) => [|xr1 bGr']; first by rewrite -mem_rev DbGr in b_xr.
rewrite /xr {1}/hdr.
case DbGd: {1 2}bGd => [|xd1 bGd'] /=; first by rewrite DbGd in b_xd.
set i := index xd bGd'.
have ltib: i < size bGd by rewrite DbGd /= ltnS /i index_size.
rewrite [hdr _ _](set_nth_default xr1) ?size_rev -?sz_bG // index_uniq //.
congr (nth _ _ _); move: Ubr; rewrite -rev_uniq {1}DbGr /= => /andP[br1'x Ubr'].
move: Ubd; rewrite DbGd /= => /andP[bd1'x _].
have:= sz_bG; rewrite DbGd -(size_rev bGr) DbGr /= => [[sz_bG']].
move: b_xd; rewrite DbGd inE eq_sym /i; case: eqP => [<- _ | _].
  rewrite /= /i -(cats0 bGr') -(cats0 bGd') !index_cat !addn0.
  by rewrite (negPf br1'x) (negPf bd1'x).
by rewrite /= -index_mem sz_bG' => /index_uniq ->.
Qed.

Let edge_hrd {xd0} xr :
  xr \in bGr -> edge (hrd xd0 xr) = hrd xd0 (face (edge xr)).
Proof.
move=> b_xr; set yr := face (edge xr).
have b_yr: yr \in bGr by rewrite EbGrN1 ?edgeK.
rewrite -{1}[xr]edgeK -/yr -{1}(@hdr_hrd xd0 xr yr) //.
set yd := hrd xd0 yr; have b_yd: yd \in bGd by rewrite bGd_hrd.
by rewrite node_hdr // hrd_hdr ?faceK // EbGdE1 ?faceK.
Qed.

Inductive sew_tag := SewDisk | SewRest.
Definition sew_tag_code pt := if pt is SewDisk then true else false.
Definition sew_tag_decode b := if b then SewDisk else SewRest.
Fact sew_tag_subproof : cancel sew_tag_code sew_tag_decode. Proof. by case. Qed.
HB.instance Definition _ := Countable.copy sew_tag (can_type sew_tag_subproof).
#[non_forgetful_inheritance]
HB.instance Definition _ : isFinite sew_tag := CanFinMixin sew_tag_subproof.

Definition sew_dart_at i : finType :=
  match i with
  | SewDisk => Gd
  | SewRest => [the finType of {xr | xr \notin bGr}]
  end.

Definition sew_dart := {i : sew_tag & sew_dart_at i}.
HB.instance Definition _ := Finite.copy sew_dart [finType of sew_dart].

Definition sewd xd : sew_dart := @Tagged _ SewDisk sew_dart_at xd.

Definition sewr_r xr b'xr : sew_dart :=
  @Tagged _ SewRest sew_dart_at (sub xr b'xr).

Definition sewr xr :=
  match in_bGr xr with
  | inleft u => sewd (hrd (sval u) xr)
  | inright b'xr => sewr_r b'xr
  end.

Lemma inj_sewd : injective sewd.
Proof. by move=> xd yd /eqP; rewrite /= eq_Tagged => /eqP. Qed.

Lemma inj_sewr : injective sewr.
Proof.
move=> xr yr /eqP; rewrite /sewr.
case: (in_bGr xr) (in_bGr yr) => [[xd0 b_xr] | b'xr] [[xd1 b_yr] | b'yr] //=.
  by move/eqP/inj_sewd/(congr1 (hdr xr)); rewrite !hdr_hrd.
by rewrite eq_Tagged -val_eqE /= => /eqP.
Qed.

Let sewr_bGr {xd0} xr : xr \in bGr -> sewr xr = sewd (hrd xd0 xr).
Proof.
rewrite /sewr => b_xr; case: (in_bGr xr) => [[xd1 /= _] | b'xr].
  by rewrite -{1}(@hdr_hrd xd0 xr xr b_xr) hrd_hdr ?bGd_hrd.
by case/idPn : b_xr.
Qed.

Let sewr_Gr xr b'xr : sewr xr = @sewr_r xr b'xr.
Proof.
rewrite /sewr; case: (in_bGr xr) => [[xd0 /= /idPn[] //] | b'xr1].
by apply/eqP; rewrite eq_Tagged -val_eqE.
Qed.

Let sewr_hdr {xr0} xd : xd \in bGd -> sewr (hdr xr0 xd) = sewd xd.
Proof. by move=> b_xd; rewrite (@sewr_bGr xd) ?hrd_hdr ?bGr_hdr. Qed.

Definition sew_edge (w : sew_dart) : sew_dart :=
  match w with
  | existT SewDisk xd =>
    if in_bGd xd is inleft u then sewr (edge (hdr (sval u) xd)) else
    sewd (edge xd)
  | existT SewRest ur =>
    sewr (edge (sval ur))
  end.

Definition sew_face_r (xr : Gr) : sew_dart :=
  match sewr (face xr) with
  | existT SewDisk xd => sewd (face xd)
  | ufr => ufr
  end.

Definition sew_face (w : sew_dart) : sew_dart :=
  match w with
  | existT SewDisk xd =>
    if in_bGd xd is inleft ur then sew_face_r (hdr (sval ur) xd) else
    sewd (face xd)
  | existT SewRest ur =>
    sew_face_r (sval ur)
  end.

Definition sew_node (w : sew_dart) : sew_dart :=
  match w with
  | existT SewDisk xd => sewd (node xd)
  | existT SewRest ur => sewr (node (sval ur))
  end.

Fact sew_map_subproof : cancel3 sew_edge sew_node sew_face.
Proof.
case=> [[xd | [xr b'xr]]] /=.
  case: (in_bGd xd) => [[xr0 b_xd] | b'xd] /=; last first.
    case: (in_bGd (edge xd)) => [[xr0 b_exd] | b'exd]; rewrite /= ?edgeK //.
    by rewrite EbGdE1 in b'xd.
  set exr := edge (hdr xr0 xd); transitivity (sew_node (sew_face_r exr)).
    rewrite /sewr; case: (in_bGr exr) => [[xd0 b_exr] | _] //=.
    by case: (in_bGd _) => [[xr1 _] | ] /=; rewrite (bGd_hrd, hdr_hrd).
  rewrite /sew_face_r (@sewr_bGr xd); last by rewrite EbGrN1 // edgeK bGr_hdr.
  by rewrite /= -edge_hrd ?bGr_hdr // edgeK hrd_hdr.
transitivity (sew_node (sew_face_r (edge xr))).
  rewrite /sewr; case: (in_bGr (edge xr)) => [[xd0 b_exr] | b'exr] //=.
  by case: (in_bGd _) => [[xr0 b_exd] | ] /=; rewrite (hdr_hrd, bGd_hrd).
have b'fexr: face (edge xr) \notin bGr.
  by apply: contra b'xr => /EbGrN <-; rewrite cnode1 edgeK.
by rewrite /sew_face_r (sewr_Gr b'fexr) /= edgeK (sewr_Gr b'xr).
Qed.

Definition sew_map := Hypermap sew_map_subproof.

Lemma sewr_rev_sewd : map sewr bGr = rev (map sewd bGd).
Proof.
apply: canRL (@revK _) _; rewrite -map_rev.
have [_ /simple_uniq Ubd] := andP cycEbGd.
move: (@sewr_hdr) sz_bG; rewrite /hdr -(size_rev bGr).
elim: bGd (rev bGr) Ubd => [|xd pd IHp] [|xr pr] //= /andP[p'xd Upd] Edr [szp].
rewrite -(Edr xr) ?mem_head // eqxx /= {}IHp // => yr0 yd p_yd.
by rewrite -(Edr yr0) 1?mem_behead //; case: eqP p'xd => // -> /negP.
Qed.

Lemma sew_map_patch : @patch sew_map _ _ sewd sewr bGd bGr.
Proof.
split=> //; first 1 [exact: inj_sewd | exact: inj_sewr | exact: sewr_rev_sewd].
- case=> -[xd | [xr b'xr]].
    rewrite -[_ xd]/(sewd xd) !inE codom_f (mem_map inj_sewd) /=.
    have [[xr0 b_xd] | b'xd] := in_bGd xd.
      rewrite b_xd; apply/imageP; exists (hdr xr0 xd) => //=.
      by rewrite (sewr_hdr b_xd).
    rewrite (negPf b'xd); apply: contraNF b'xd => /imageP[xr _]; rewrite /sewr.
    by case: (in_bGr xr) => [[xd0 b_xr] | ] //= /inj_sewd->; apply: bGd_hrd.
  rewrite -[existT _ _ _]/(sewr_r b'xr) !inE -{1}sewr_Gr codom_f.
  by case: imageP => [[]|].
- by move=> xd b'xd /=; case: (in_bGd xd) => // [[xr0 /=/idPn]].
- move=> xr; rewrite {2}/sewr; case: (in_bGr xr) => [[xd0 b_xr] | ] //=.
  by case: (in_bGd _) => [[xr0 _] | ] /=; rewrite (hdr_hrd, bGd_hrd).
by move=> xr b'xr; rewrite /= (sewr_Gr b'xr).
Qed.

End Sew.
