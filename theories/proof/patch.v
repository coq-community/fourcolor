(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype path fingraph.
From fourcolor Require Import hypermap geometry jordan color coloring.

(******************************************************************************)
(*   Patching two maps to cover a larger one. The relations established here  *)
(* are used in both directions: with sew, to deduce the properties of the new *)
(* map created by glueing, and in snip, to deduce the properties of the two   *)
(* maps created by cutting along a ring (i.e., a simple R-cycle).             *)
(*   It is important to note that the relations between the two parts is not  *)
(* quite symmetrical: the border of the inside ("disk") map is an edge cycle, *)
(* while the border of the outer ("remainder") part is a node orbit.          *)
(*   The disk border E-cycle must be simple, but only in the disk map; the    *)
(* corresponding R-cycle in the main map, and N-cycle in the remainder map    *)
(* need only be duplicate-free (uniq).                                        *)
(*   patch hd hd bGd bGr <-> hypermap G is the glueing via hd : Gd -> G and   *)
(*       hr : Gr -> G of the disk hypermap Gd and the remainder hypermap Gr,  *)
(*       along their respective edge and node borders bGd and bGr: bGd is a   *)
(*       simple E-cycle of Gd, bGr a uniq N-cycle of Gr, hd and hr are        *)
(*       injective, their codomains cover G and intersect exactly on the      *)
(*       border R-ring, map hr bGr = rev (map hd bGd); except on the border,  *)
(*       hd preserves E-links and hr preserves N-links.                       *)
(*   At the end of this file we give a first application of patching: we      *)
(* prove that a minimal counter example must be connected, using              *)
(*     gcomp_disk z == the "disk" hypermap whose set of darts is the          *)
(*                     connected component of z in a hypermap G.              *)
(*      gcomp_rem z == the "remainder" hypermap whose set of darts is the     *)
(*                     complement of the connected component of z.            *)
(*         gcompd u == the projection of u : gcomp_disk z in G.               *)
(*         gcompr u == the projection of u : gcomp_rem z in G.                *)
(* For any dart z in a hypermap G, patch (@gcompd G z) (@gcompr G z) nil nil  *)
(* holds, though gcomp_rem z is empty when G is connected.                    *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Patch.

Variables (G Gd Gr : hypermap) (hd : Gd -> G) (hr : Gr -> G).
Variables (bGd : seq Gd) (bGr : seq Gr).

Record patch : Prop := Patch {
  patch_injd : injective hd;
  patch_injr : injective hr;
  patch_cycle_d : sfcycle edge bGd;
  patch_cycle_r : ufcycle node bGr;
  patch_map_ring_r : map hr bGr = rev (map hd bGd);
  patch_codom_r : codom hr =i [predU [predC codom hd] & map hd bGd];
  patch_edge_d : {in [predC bGd], {morph hd : xd / edge xd}};
  patch_node_d : {morph hd : xd / node xd};
  patch_edge_r : {morph hr : xr / edge xr};
  patch_node_r : {in [predC bGr], {morph hr : xr / node xr}}
}.

Hypothesis patchG : patch.

Let Ihd : injective hd := patch_injd patchG.
Let Ihr : injective hr := patch_injr patchG.
Let cycEbGd : sfcycle edge bGd := patch_cycle_d patchG.
Let cycNbGr : ufcycle node bGr := patch_cycle_r patchG.
Let bG := map hd bGd.
Let DbGr : map hr bGr = rev bG := patch_map_ring_r patchG.
Let im_hr : codom hr =i [predU [predC codom hd] & bG] := patch_codom_r patchG.
Let EbGr : map hr bGr =i bG. Proof. by move=> u; rewrite DbGr mem_rev. Qed.
Let im_hd : codom hd =i [predU [predC codom hr] & bG].
Proof.
move=> x; rewrite !inE im_hr negb_or negbK /= orbC orb_andr orbN andbT.
by rewrite orb_idl // => /mapP[xd _ ->]; apply: codom_f.
Qed.
Let hdE : {in [predC bGd], {morph hd : xd / edge xd}} := patch_edge_d patchG.
Let hdN : {morph hd : xd / node xd} := patch_node_d patchG.
Let hrE : {morph hr : xr / edge xr} := patch_edge_r patchG.
Let hrN : {in [predC bGr], {morph hr : xr / node xr}} := patch_node_r patchG.
Let UbGd : uniq bGd. Proof. by have /andP[] := scycle_ucycle cycEbGd. Qed.
Let UbGr : uniq bGr. Proof. by have /andP[] := cycNbGr. Qed.
Let UbG : uniq bG. Proof. by rewrite (map_inj_uniq Ihd). Qed.

Let EbGdr xd : (hd xd \in codom hr) = (xd \in bGd).
Proof. by rewrite im_hr !inE codom_f (mem_map Ihd). Qed.

Let EbGdE xd : xd \in bGd -> forall yd, cedge xd yd = (yd \in bGd).
Proof. by apply: fconnect_cycle; case/andP: cycEbGd. Qed.

Let EbGrd xr : (hr xr \in codom hd) = (xr \in bGr).
Proof. by rewrite im_hd !inE codom_f -EbGr (mem_map Ihr). Qed.

Let EbGrN xr : xr \in bGr -> forall yr, cnode xr yr = (yr \in bGr).
Proof. by apply: fconnect_cycle; case (andP cycNbGr). Qed.

Let EhdUr : [predU codom hd & codom hr] =1 G.
Proof. by move=> x; rewrite /= im_hr !inE orbA orbN. Qed.

Let EhdIr : [predI codom hd & codom hr] =i bG.
Proof.
move=> x; rewrite !(inE, im_hr) andb_orr andbN andb_idl //.
by case/mapP=> xd _ ->; apply: codom_f.
Qed.

Lemma card_patch : #|Gd| + #|Gr| = size bG + #|G|.
Proof.
rewrite -(card_codom Ihd) -(card_codom Ihr) -cardUI (eq_card EhdUr) addnC.
by rewrite (eq_card EhdIr) (card_uniqP UbG).
Qed.

Let clEbGd : fclosed edge bGd.
Proof.
by apply: (intro_closed cedgeC) => xd _ /eqP <- /EbGdE <-; apply: fconnect1.
Qed.

Let clNbGr : fclosed node bGr.
Proof.
by apply: (intro_closed cnodeC) => xr _ /eqP <- /EbGrN <-; apply: fconnect1.
Qed.

Let hdErN xd xr : (hd (edge xd) == hr xr) = (hd xd == hr (node xr)).
Proof.
case b_xd: (xd \in bGd); last first.
  apply/eqP/eqP => Dx; case/idP: b_xd; last first.
    by rewrite -(mem_map Ihd) -EhdIr !inE codom_f Dx codom_f.
  by rewrite (clEbGd (eqxx _)) -(mem_map Ihd) -EhdIr !inE codom_f Dx codom_f.
have [[cycEb _] [cycNb _]] := (andP cycEbGd, andP cycNbGr).
rewrite (eqP (next_cycle cycEb b_xd)) -(next_map Ihd UbGd) -/bG.
rewrite (canF_eq (prev_next UbG)) -(next_rev UbG) -DbGr (next_map Ihr UbGr).
case b_xr: (xr \in bGr); first by rewrite -(eqP (next_cycle cycNb b_xr)).
apply/eqP/eqP => Dx; case/idP: b_xr.
  by rewrite -mem_next -(mem_map Ihr) EbGr -Dx map_f.
by rewrite (clNbGr (eqxx _)) -(mem_map Ihr) EbGr -Dx map_f.
Qed.

Let bGdP xd : xd \in bGd -> {xr | hd (edge xd) = hr xr & hd xd = hr (node xr)}.
Proof.
move=> b_xd; have xrP: hd xd \in codom hr by rewrite EbGdr.
exists (face (edge (iinv xrP))); last by rewrite edgeK f_iinv.
by apply/eqP; rewrite hdErN edgeK f_iinv.
Qed.

Let bGrP xr : xr \in bGr -> {xd | hd (edge xd) = hr xr & hd xd = hr (node xr)}.
Proof.
move=> b_xr; have xdP: hr xr \in codom hd by rewrite EbGrd.
exists (node (face (iinv xdP))); first by rewrite faceK f_iinv.
by apply/eqP; rewrite -hdErN faceK f_iinv.
Qed.

Let hdF : {in [predC bGd], {morph hd: xd / face xd}}.
Proof.
move=> xd b'xd; apply: (canRL (canF_sym faceK)).
by rewrite -hdN -?hdE ?faceK // !inE (clEbGd (eqxx _)) faceK.
Qed.

Let hrF : {in preim face [predC bGr], {morph hr : xr / face xr}}.
Proof. by move=> xr b'fxr; rewrite /= -{2}[xr]faceK hrE hrN ?nodeK. Qed.

Let hdFrF xd xr : (hd (face xd) == face (hr xr)) = (hd xd == hr (face xr)).
Proof. by rewrite -{2}[xd]faceK hdErN hdN (canF_eq nodeK) -hrE faceK. Qed.

Local Notation Fbd := (fband bGd).

Lemma patch_fcard_face_d : fcard face Gd = size bG + fcard face (predC Fbd).
Proof. by rewrite size_map -(scycle_fcard_fband cycEbGd) -n_compC. Qed.

Definition outer := fclosure face (codom hr).

Lemma closed_Gr : fclosed edge (codom hr).
Proof.
apply: (intro_closed cedgeC) => x _ /eqP <- xrP.
by rewrite -(f_iinv xrP) -hrE codom_f.
Qed.

Lemma closed_outer : fclosed face outer.
Proof. exact: (closure_closed cfaceC). Qed.

Remark closed_outerC : fclosed face [predC outer].
Proof. exact: (predC_closed closed_outer). Qed.

Lemma closed_Gd : fclosed node (codom hd).
Proof.
apply: (intro_closed cnodeC) => x _ /eqP <- xdP.
by rewrite -(f_iinv xdP) -hdN codom_f.
Qed.

Lemma plain_patch : plain G = plainb [predC bGd] && plainb Gr.
Proof.
congr (is_true _); apply/idP/andP => [plainG | [plainGd plainGr]].
  have{plainG} [De2 neq_e] := (plain_eq plainG, plain_neq plainG).
  do [split; apply/plainP] => [xd b'xd | xr _].
    split; last by rewrite -(inj_eq Ihd) hdE ?neq_e.
    by apply Ihd; rewrite !hdE ?De2 // -(predC_closed clEbGd (eqxx _)).
  by split; [apply Ihr; rewrite !hrE De2 | rewrite -(inj_eq Ihr) hrE neq_e].
apply/plainP=> x _; have [xrP|] := boolP (x \in codom hr).
  by rewrite -(f_iinv xrP) -!hrE (inj_eq Ihr) plain_eq // plain_neq.
rewrite im_hr !inE => /norP[/negbNE/imageP[xd _ ->{x}]].
rewrite (mem_map Ihd) => b'xd; have [eexd xd'exd] := plainP plainGd _ b'xd.
by rewrite -!hdE ?eexd ?(inj_eq Ihd) // -(predC_closed clEbGd (eqxx _)).
Qed.

Lemma cubic_patch : cubic G = cubicb Gd && cubicb [predC bGr].
Proof.
congr (is_true _); apply/idP/andP => [cubicG | [cubicGd cubicGr]].
  have{cubicG} [Dn3 neq_n] := (cubic_eq cubicG, cubic_neq cubicG).
  do [split; apply/cubicP] => [xd _ | xr b'x].
    by split; [apply Ihd; rewrite !hdN Dn3 | rewrite -(inj_eq Ihd) hdN neq_n].
  split; last by rewrite -(inj_eq Ihr) hrN ?neq_n.
  by apply Ihr; rewrite !hrN ?Dn3 // -!(fclosed1 (predC_closed clNbGr)).
apply/cubicP => x _; have [xdP | ] := boolP (x \in codom hd).
  by rewrite -(f_iinv xdP) -!hdN (inj_eq Ihd) cubic_eq ?cubic_neq.
rewrite im_hd !inE => /norP[/negbNE/imageP[xr _ ->]]. 
rewrite -EbGr (mem_map Ihr) => b'xr; have [n3xr x'nxr] := cubicP cubicGr _ b'xr.
by rewrite -!hrN -?(fclosed1 (predC_closed clNbGr)) // n3xr (inj_eq Ihr).
Qed.

Lemma outer_hd xd : (hd xd \in outer) = (xd \in Fbd).
Proof.
apply/idP/idP.
  case/exists_inP=> /= _ /connectP[p xFp ->].
  elim: p xd xFp => [|y p IHp] xd /= => [_ | /andP[]].
    by rewrite EbGdr => /(subsetP (ring_fband _)).
  have [b_xd | b'xd] := boolP (xd \in bGd).
    by rewrite (subsetP (ring_fband _)).
  rewrite -hdF // => /eqP <-; rewrite [xd \in _](eq_has (cface1 xd)).
  exact: IHp.
case/hasP=> zd b_zd xFzd; case/connectP: xFzd b_zd => p xdFp ->{zd}.
elim: p xd xdFp => [|yd p IHp] xd /= => [_ b_xd | /andP[/eqP <- {yd}]].
  by apply: (subsetP (subset_closure _ _)); rewrite EbGdr.
have [b_xd | b'xd] := boolP (xd \in bGd).
  by rewrite (subsetP (subset_closure _ _)) ?EbGdr.
by rewrite (closure_closed cfaceC _ (eqxx _)) -hdF //; apply: IHp.
Qed.

Let adj_hd : fun_adjunction hd face face [predC outer].
Proof.
apply: (strict_adjunction cfaceC closed_outerC Ihd) => [|xd yd /=].
  apply/subsetP=> x out'x; rewrite im_hd !inE (contra _ out'x) //.
  exact: (subsetP (subset_closure _ _)).
rewrite negbK inE /= outer_hd => b'xd; rewrite -hdF ?(inj_eq Ihd) //.
by apply: contra b'xd => /(subsetP (ring_fband _)).
Qed.

Lemma patch_face_d xd yd :
  ~~ outer (hd xd) -> cface xd yd = cface (hd xd) (hd yd).
Proof. exact: (rel_functor adj_hd). Qed.

Let cFhd xd : cface (hd xd) (hd (face xd)).
Proof.
have [b_xd | b'x] := boolP (xd \in bGd); last by rewrite hdF ?fconnect1.
have /connectP[p]: cface (face xd) xd by rewrite cfaceC fconnect1.
elim: p (face xd) => [|zd p IHp] yd /= => [_ <- // | xFp Lp].
have [b_yd | b'_yd] := boolP (yd \in bGd).
  rewrite (scycle_cface cycEbGd b_yd b_xd) //.
  by apply/connectP; exists (zd :: p).
have [/eqP Dzd yFp] := andP xFp.
by rewrite (connect_trans (IHp _ yFp Lp)) // cfaceC -Dzd hdF ?fconnect1.
Qed.

Lemma patch_face_d' xd yd : cface xd yd -> cface (hd xd) (hd yd).
Proof.
case/connectP=> p xFp ->{yd}.
by elim: p xd xFp => //= _ p IHp xd /andP[/eqP <- /IHp]; apply: connect_trans. 
Qed.

Lemma patch_face_r xr yr : cface xr yr = cface (hr xr) (hr yr).
Proof.
apply/idP/idP.
  case/connectP=> p xFp ->{yr}.
  elim: p xr xFp => //= _ p IHp xr /andP[/eqP <- /IHp]; apply: connect_trans.
  have [b_fxr | /hrF->] := boolP (face xr \in bGr); last exact: fconnect1.
  have [xd Dfxr Dxd] := bGrP b_fxr; rewrite -{}Dfxr -[xr]faceK hrE -{}Dxd.
  by rewrite -{1}[xd]edgeK hdN cface1 nodeK patch_face_d' // cfaceC fconnect1.
set x := hr xr => /connectP[p xFp Lp].
pose cFdr := exists2 xd, _ = hd xd & exists2 yd, hd yd = hr _ & cface yd xd.
have: if x \in codom hr then x = hr xr else cFdr x xr by rewrite codom_f.
elim: p {xr}x (xr) xFp Lp => [|z p IHp] x xr /= => [_ | /andP[/eqP-Dz zFp]] Lp.
  by rewrite -Lp codom_f => /Ihr->.
have [xrP Dx | b'xd [xd Dxd [yd Dyd ydFxd]]] := ifPn.
  rewrite cface1 (IHp z) {p IHp zFp Lp}// -{z}Dz.
  have [fxrP | ] := ifP.
    have [b_fxr | /hrF->] := boolP (face xr \in bGr); last by rewrite Dx.
    have [xd Dfxr Dxd] := bGrP b_fxr; rewrite -Dfxr Dx -[xr]faceK hrE -Dxd.
    rewrite -{1}[xd]edgeK hdN nodeK; congr (hd _).
    apply/esym/(scycle_cface cycEbGd); last exact: fconnect1.
      by rewrite -EbGdr Dfxr codom_f.
    by rewrite -EbGdr -[hd _]nodeK -hdN edgeK Dxd -hrE faceK -Dx.
  rewrite im_hr !inE=> /norP[/negbNE/imageP[xd _ Dfx]].
  rewrite Dfx (mem_map Ihd) => b'xd; exists xd => //.
  exists (edge (node xd)); last by rewrite -{2}[xd]nodeK fconnect1.
  by apply/eqP; rewrite hdErN hdN -Dfx Dx -{1}[xr]faceK hrE edgeK.
rewrite (IHp z) {p IHp zFp Lp}// -{z}Dz.
rewrite !im_hr !inE Dxd codom_f (mem_map Ihd) /= in b'xd *.
rewrite -hdF // codom_f (mem_map Ihd) /=.
have [b_fxd | b'fxd] := ifPn.
  rewrite -Dyd [yd](scycle_cface cycEbGd _ b_fxd) -?cface1r //.
  by rewrite -EbGdr Dyd codom_f.
by exists (face xd) => //; exists yd; last by rewrite -cface1r.
Qed.

Lemma patch_bridgeless : bridgeless G -> bridgeless Gd /\ bridgeless Gr.
Proof.
move=> br'G; do [split; apply: contra br'G => /existsP[]] => [xd | xr] xFex.
  apply/existsP; exists (hd xd).
  by rewrite -{2}[xd]edgeK hdN cface1r nodeK patch_face_d' -?cface1r.
by apply/existsP; exists (hr xr); rewrite -hrE -patch_face_r.
Qed.

Lemma bridgeless_patch :
  bridgeless Gd -> bridgeless Gr -> chordless bGd -> bridgeless G.
Proof.
move=> bridge'Gd bridge'Gr chord'Gd; apply/existsP=> [[x xFex]].
have [/imageP[xr _ Dx] | ] := boolP (x \in codom hr).
  by case/existsP: bridge'Gr; exists xr; rewrite patch_face_r hrE -Dx.
rewrite im_hr => /norP[/negbNE/imageP[xd _ Dx]].
rewrite Dx /= (mem_map Ihd) => b'xd; rewrite Dx -hdE // in xFex.
have [out_x | out'x] := boolP (hd xd \in outer); last first.
  by case/existsP: bridge'Gd; exists xd; rewrite patch_face_d.
have: hd (edge xd) \in outer  by rewrite -(closed_connect closed_outer xFex).
move: out_x; rewrite !outer_hd => /hasP[yd b_yd xFyd] /hasP[zd b_zd exFzd].
case/exists_inP: (subsetP chord'Gd _ b_yd); exists zd; rewrite !inE /=.
  by apply/adjP; exists xd; first by rewrite cfaceC.
have [[yr Dyr Dnyr] [cEbd _]] := (bGdP b_yd, andP cycEbGd).
apply/and3P; split=> //; apply/eqP=> Dzd; case/existsP: bridge'Gr.
  exists (node yr); rewrite cface1r nodeK.
  rewrite patch_face_r -Dnyr -Dyr (eqP (next_cycle cEbd b_yd)) -Dzd.
  by rewrite -(same_cface (patch_face_d' xFyd)) (same_cface xFex) patch_face_d'.
exists (node (node yr)); rewrite cface1r nodeK patch_face_r -Dnyr cfaceC.
rewrite -(same_cface (patch_face_d' xFyd)) (same_cface xFex).
suffices /eqP <-: hd zd == hr (node (node yr)) by apply: patch_face_d'.
by rewrite -hdErN -Dnyr Dzd (eqP (prev_cycle cEbd b_yd)).
Qed.

Let a := closure glink (codom hr).
Let clGa : closed glink a. Proof. exact: (closure_closed glinkC). Qed.

Let oaGr : n_comp glink Gr = n_comp glink a.
Proof.
have [cG cGr] := (@glinkC G, @glinkC Gr).
rewrite (adjunction_n_comp hr cG cGr clGa).
  by apply: eq_card => xr; congr (_ && _); apply/esym/mem_closure/codom_f.
split=> [x a_x | xr zr _].
  apply: sigW; have [y /= yGx /imageP[yr _ Dy]] := exists_inP a_x.
  by exists yr; rewrite -Dy.
do [apply/idP/idP; rewrite -clink_glink => /connectP[p xCp]] => [->{zr} | Lp].
  elim: p xr xCp => //= yr p IH xr /andP[xCy /IH]; apply: {p IH}connect_trans.
  have hGFr zr: gcomp (hr zr) (hr (face zr)).
    have: cface (hr zr) (hr (face zr)) by rewrite -patch_face_r fconnect1.
    by apply: {zr}connect_sub => x _ /eqP <-; apply: (connect1 (glinkF _)).
  have [Dxr | <- //] := clinkP xCy.
  by rewrite (same_connect1 cG (glinkE _)) -[yr]nodeK -Dxr -hrE.
set x := hr xr in xCp Lp.
have: if x \in codom hr then x = hr xr else xr \in bGr by rewrite codom_f.
elim: p {xr}x (xr) xCp Lp => [|y p IHp] x xr /= => [_ | /andP[xCy yCp]] Lp.
  by rewrite -Lp codom_f => /Ihr->.
have{p IHp yCp Lp} yGzr := IHp y _ yCp Lp _.
have [/imageP[yd _ Dyd] | ] := boolP (y \in codom hd).
  have bGzr tr (b_tr : tr \in bGr):  gcomp tr zr.
    case: imageP yGzr => [[yr _ Dy] /(_ _ Dy) | _ -> //]; apply: connect_trans.
    have: cnode tr yr by rewrite (EbGrN b_tr) -EbGrd -Dy Dyd codom_f.
    by apply: connect_sub => ur _ /eqP <-; apply: connect1 (glinkN _).
  case: ifP => [_ Dx | _ /bGzr//]; rewrite {x}Dx in xCy.
  have [xr_ny | fxr_y] := clinkP xCy.
    by rewrite bGzr // -EbGrd xr_ny Dyd -hdN codom_f.
  rewrite (same_connect1 cGr (glinkF _)) bGzr //.
  by apply: wlog_neg => /hrF h_fxr; rewrite -EbGrd h_fxr fxr_y Dyd codom_f.
rewrite im_hd !inE => /norP[/negbNE/imageP[yr _ Dy]].
rewrite Dy -EbGr (mem_map Ihr) => b'yr Dx.
apply: connect_trans {yGzr}(yGzr yr _); last by rewrite Dy codom_f.
rewrite -clink_glink connect1 //; have [xny | fxy] := clinkP xCy.
  by rewrite xny Dy -hrN // codom_f in Dx; rewrite -(Ihr Dx) clinkN.
rewrite (canRL faceK fxy) Dy -hrN // -hrE codom_f in Dx.
by rewrite -[yr]nodeK -(Ihr Dx) clinkF.
Qed.

Lemma patch_connected_r : connected G -> Gr -> connected Gr.
Proof.
move=> ccG xr; rewrite /connected oaGr -(@eq_n_comp_r _ _ G) // => y.
apply/esym/exists_inP; exists (hr xr) => /=; last exact: codom_f.
by rewrite inE -clink_glink; apply/connectP/connected_clink.
Qed.

Lemma patch_fcard_face_r : fcard face Gr = fcard face outer.
Proof.
rewrite /= (adjunction_n_comp hr cfaceC cfaceC closed_outer).
  by apply: eq_card => xr; rewrite !inE mem_closure ?codom_f.
split=> [x out_x | xr yr _]; last exact: patch_face_r.
apply: sigW; have [y /= xFy /imageP[yr _ Dy]] := exists_inP out_x.
by exists yr; rewrite -Dy.
Qed.

Lemma genus_patch : genus G = genus Gd + genus Gr.
Proof.
pose eb := nilp bG; have ebPd: if eb then bGd = [::] else exists xd, xd \in bGd.
  by rewrite /eb /bG; case: bGd => [|xd p] //; exists xd; apply: mem_head.
have ebPr: if eb then bGr = [::] else exists xr, xr \in bGr.
  rewrite /eb /nilp -size_rev -DbGr; case: bGr => [|xr p] //=.
  by exists xr; apply: mem_head.
have oGdE: fcard edge Gd = ~~ eb + fcard edge [predC codom hr].
  rewrite (n_compC (mem bGd)); congr (_ + _).
    case: (eb) ebPd => [-> | [xd b_xd]].
      by apply: eq_card0 => x; rewrite !inE andbF.
    by rewrite -(eq_n_comp_r (EbGdE b_xd)) (n_comp_connect cedgeC).
  have clGr' := predC_closed closed_Gr.
  rewrite (adjunction_n_comp hd cedgeC cedgeC clGr').
    by apply: eq_n_comp_r => x; rewrite !(im_hr, inE) codom_f (mem_map Ihd).
  apply (strict_adjunction cedgeC clGr' Ihd) => [|xd yd].
    by apply/subsetP=> x; rewrite !(im_hr, inE) => /norP[/negbNE].
  rewrite !(inE, im_hr) negbK codom_f (mem_map Ihd) /= => b'xd.
  by rewrite -hdE // (inj_eq Ihd).
have oGdF: fcard face Gd = size bG + fcard face (predC outer).
  rewrite patch_fcard_face_d; congr (_ + _).
  rewrite (adjunction_n_comp _ cfaceC cfaceC closed_outerC adj_hd).
  by apply: eq_card => xd; rewrite !inE outer_hd.
have oGdN: fcard node Gd = fcard node (codom hd).
  rewrite (adjunction_n_comp hd cnodeC cnodeC closed_Gd).
    by apply: eq_card => xd; rewrite !inE codom_f.
  apply: (strict_adjunction cnodeC closed_Gd Ihd (subxx _)) => xd yd _ /=.
  by rewrite -hdN (inj_eq Ihd).
have oGdG: n_comp glink Gd = ~~ eb + n_comp glink (predC a).
  have [cG cGd] := (@glinkC G, @glinkC Gd).
  have hdG xd yd: xd \notin bGd -> glink (hd xd) (hd yd) = glink xd yd.
    by move=> b'xd; rewrite {1}/glink /= -hdN -hdE -?hdF // !(inj_eq Ihd).
  have clGa' := predC_closed clGa.
  have adj_Gd: rel_adjunction hd glink glink (predC a).
    apply (strict_adjunction cGd clGa' Ihd) => [|xd yd /negbNE/= a'x].
      apply/subsetP=> x a'x; have /orP[//| /= xrP] := EhdUr x.
      by rewrite !inE mem_closure in a'x.
    by rewrite hdG // -EbGdr (contra ((subsetP (subset_closure _ _)) _) a'x).
  rewrite (adjunction_n_comp hd cG cGd clGa' adj_Gd).
  rewrite (n_compC (preim hd a)); congr (_ + _).
  case: (eb) ebPd => [bGd0 | [xd b_xd]] /=.
    apply: eq_card0 => xd; apply/nandP; right; apply/exists_inP=> [[y /=]].
    rewrite inE -clink_glink => /connectP[p xCp ->{y}] /idPn[].
    elim: p xd xCp => /= [|y p IHp] xd; first by rewrite /= EbGdr bGd0.
    case/andP=> /clinkP[/(canLR nodeK) | ] <-.
      by rewrite -[xd]edgeK hdN nodeK; apply: IHp.
    by rewrite -hdF ?bGd0 //; apply: IHp.
  rewrite -(n_comp_connect cGd xd); apply: eq_n_comp_r => yd; rewrite !inE.
  apply/exists_inP/idP=> /= [[z] |].
    rewrite inE -clink_glink => /connectP[p yCp ->{z}].
    elim: p yd yCp => [|z p IHp] yd /= => [_ | /andP[]].
      rewrite EbGdr -{b_xd}(EbGdE b_xd).
      by apply: connect_sub => zd _ /eqP <-; rewrite connect1 ?glinkE.
    case/clinkP=> [/(canLR nodeK) | ] <-{z}.
      rewrite -[yd]edgeK hdN nodeK -(same_connect1r cGd (glinkN _)).
      exact: IHp.
    have [| /hdF <-] := boolP (yd \in bGd); last first.
      by rewrite (same_connect1r cGd (glinkF _)); apply: IHp.
    rewrite -(EbGdE b_xd) => xdNyd _ _.
    by apply: connect_sub xdNyd => zd _ /eqP <-; rewrite connect1 ?glinkE.
  rewrite cGd => /connectP[p yGp Dxd]; rewrite {xd}Dxd in b_xd *.
  elim: p yd yGp b_xd => [|yd p IHp] xd /= => [_ | /andP[xGy yGp]] b_p.
    by exists (hd xd); rewrite ?inE ?EbGdr.
  have [|b'xd] := boolP (xd \in bGd).
    by exists (hd xd); rewrite ?inE ?EbGdr.
  have [x xGyd Gr_x] := IHp _ yGp b_p; exists x => //.
  by apply: connect_trans xGyd; rewrite connect1 ?hdG.
have oGrE: fcard edge Gr = fcard edge (codom hr).
  rewrite (adjunction_n_comp hr cedgeC cedgeC closed_Gr).
    by apply: eq_card => z; rewrite !inE codom_f.
  apply (strict_adjunction cedgeC closed_Gr Ihr (subxx _)) => xr yr _ /=.
  by rewrite -hrE (inj_eq Ihr).
have oGrN: fcard node Gr = ~~ eb + fcard node [predC codom hd].
  have clGd' := predC_closed closed_Gd.
  rewrite (adjunction_n_comp hr cnodeC cnodeC clGd').
    rewrite (n_compC [preim hr of codom hd]); congr (_ + _).
    case: (eb) ebPr => [bGr0 | [xr b_xr]] /=.
      by apply: eq_card0 => x; rewrite !inE EbGrd bGr0 andbF.
    rewrite -(n_comp_connect cnodeC xr); apply: eq_n_comp_r => y /=.
    by rewrite !inE EbGrd (EbGrN b_xr).
  apply (strict_adjunction cnodeC clGd' Ihr) => [|xr yr /=].
    by apply/subsetP => x; rewrite !(im_hd, inE) => /norP[/negbNE].
  by rewrite negbK !inE EbGrd -(inj_eq Ihr) => /hrN->.
rewrite {1}/genus -(subnDl (Euler_lhs Gd + Euler_lhs Gr)).
rewrite addnC {1 4 5}/Euler_lhs !even_genusP /Euler_rhs (n_compC a).
rewrite (n_compC (mem (codom hr))) (n_compC (mem (codom hd))) (n_compC outer).
rewrite oGdE oGdF -oGdN oGdG -oGrE -patch_fcard_face_r oGrN -oaGr !doubleD.
rewrite -!addnA -(addnn (~~ eb)) (addnCA #|Gd|) (addnA #|Gd|) card_patch.
rewrite -!addnA -!(addnCA (~~ eb)) !subnDl addnCA !subnDl.
rewrite -(addnCA #|G|) subnDl addnC -!addnA !(addnCA (genus Gr).*2).
rewrite -doubleD; do 2!rewrite addnA addnCA subnDl.
rewrite -!addnA !subnDl; do 2!rewrite addnCA subnDl.
by rewrite addKn half_double addnC.
Qed.

Lemma planar_patch : planar G = planarb Gd && planarb Gr.
Proof. by rewrite /planar genus_patch addn_eq0. Qed.

Lemma colorable_patch :
  four_colorable G <->
    (exists2 et, ring_trace bGd et & ring_trace bGr (rot 1 (rev et))).
Proof.
split=> [[k [kE kF]] | [et [kd [kdE kdF] Tkd] [kr [krE krF] Tkr]]].
  exists (trace (map k bG)).
    exists (k \o hd); last by rewrite -map_comp.
    have kdF xd: k (hd (face xd)) == k (hd xd).
      exact/eqP/esym/(fconnect_invariant kF)/patch_face_d'/fconnect1.
    split=> // xd /=; rewrite -{2}[xd]edgeK -(eqP (kdF _)) /= hdN.
    by move: (hd _) => y; rewrite -{1}[y]nodeK (eqcP (kF _)) [_ == _]kE.
  exists (k \o hr); last by rewrite -trace_rev -map_rev -DbGr -map_comp.
  split=> x /=; first by rewrite hrE [_ == _]kE.
  by apply/eqcP/esym/(fconnect_invariant kF); rewrite -patch_face_r fconnect1.
pose c0 := head_color (map kd (rev bGd)) +c head_color (map kr bGr).
pose kd' := addc c0 \o kd; have Ic0 := can_inj (addKc c0).
have{kdE} kd'E: invariant edge kd' =1 pred0.
  by move=> x; rewrite -(kdE x); apply: invariant_inj.
have{Ic0 kdF} kd'F: invariant face kd' =1 Gd.
  by move=> x; rewrite -(kdF x); apply: invariant_inj.
have{Tkd Tkr} Tkd': rev (map kd' bGd) = map kr bGr.
  move: Tkr; rewrite Tkd -trace_rev -!map_rev [in X in _ -> X]map_comp /c0.
  case: (rev bGd) => [|xd bGd']; first by case: bGr => // xr [].
  case: bGr => [|xr bGr'] Ekdr; first by case: bGd' Ekdr.
  rewrite /= -untrace_trace -map_cons trace_addc addcC addKc.
  by rewrite -map_cons Ekdr map_cons untrace_trace.
move: {kd c0}kd' kd'E kd'F Tkd' => kd kdE /(_ _)/eqcP/= kdF Tkdr.
have eq_kdr xd xr: hd xd = hr xr -> kd xd = kr xr.
  move=> eq_xdr; have b_xd: xd \in bGd by rewrite -EbGdr eq_xdr codom_f.
  have b_xr: xr \in rev bGr by rewrite mem_rev -EbGrd -eq_xdr codom_f.
  rewrite -(nth_index xd b_xd) -(nth_index xr b_xr).
  rewrite -!index_mem in b_xd b_xr.
  rewrite -(nth_map xr Color0) -?(nth_map xd Color0) // map_rev -Tkdr revK.
  by rewrite -(index_map Ihd) -(index_map Ihr) map_rev DbGr revK eq_xdr.
have kP x : {xr | x = hr xr} + {xd | xd \notin bGd & x = hd xd}.
  have [xrP | xrP'] := boolP (x \in codom hr); [left | right].
    by exists (iinv xrP); rewrite f_iinv.
  have xdP: x \in codom hd by case/orP: (EhdUr x) => // /idPn[].
  by exists (iinv xdP); rewrite -?EbGdr f_iinv.
pose k x := match kP x with inl u => kr (sval u) | inr u => kd (s2val u) end.
exists k; split=> x; rewrite /k /=.
  case: (kP x) => [[xr /= ->] | [xd b'xd /= ->]]; rewrite -(hrE, hdE) //.
    by case: (kP _) => [[_ /=/Ihr<-] | [_ _ /=/esym/eq_kdr->]]; apply: krE.
  by case: (kP _) => [[_ /=/eq_kdr<-] | [_ _ /=/Ihd<-]]; apply: kdE.
apply/eqP/esym; case: (kP x) => [[xr /= ->] | [xd b'xd /= ->]].
  case: (kP _) => [[yr /= Dy] | [yd _ /=/esym/eqP]].
    by apply: (fconnect_invariant krF); rewrite patch_face_r -Dy fconnect1.
  by rewrite -[yd]nodeK hdFrF -(eqcP (krF _)) kdF => /eqP/eq_kdr.
by rewrite -hdF // -kdF; case: (kP _) => [[_ /=/eq_kdr <-] | [_ _ /=/Ihd <-]].
Qed.

End Patch.

(* Patching disjoint components of the map along empty borders. Used to *)
(* show that the minimal counter example is connected.                  *)

Section PatchGcomp.

Variables (G : hypermap) (z : G).

Definition gcompd_dart := {x | gcomp z x}.
HB.instance Definition _ := Finite.on gcompd_dart.
Implicit Type u : gcompd_dart.

Fact gcompd_edge_subproof u : gcomp z (edge (val u)).
Proof. exact: connect_trans (valP u) (connect1 (glinkE _)). Qed.

Fact gcompd_node_subproof u : gcomp z (node (val u)).
Proof. exact: connect_trans (valP u) (connect1 (glinkN _)). Qed.

Fact gcompd_face_subproof u : gcomp z (face (val u)).
Proof. exact: connect_trans (valP u) (connect1 (glinkF _)). Qed.

Definition gcompd_edge u : gcompd_dart := Sub _ (gcompd_edge_subproof u).
Definition gcompd_node u : gcompd_dart := Sub _ (gcompd_node_subproof u).
Definition gcompd_face u : gcompd_dart := Sub _ (gcompd_face_subproof u).

Fact gcompd_subproof : cancel3 gcompd_edge gcompd_node gcompd_face.
Proof. by move=> u; apply/val_inj/edgeK. Qed.

Definition gcomp_disk := Hypermap gcompd_subproof.
Definition gcompd (u : gcomp_disk) := val u.

Lemma inj_gcompd : injective gcompd. Proof. exact: val_inj. Qed.
Lemma codom_gcompd : codom gcompd =i gcomp z.
Proof.
by move=> x; apply/imageP/idP => [[[y zGy] _ -> //] | zGx]; exists (Sub x zGx).
Qed.

Definition gcompr_dart := {x | ~~ gcomp z x}.
HB.instance Definition _ := Finite.on gcompr_dart.
Implicit Type v : gcompr_dart.

Local Notation glink1r gstep := (same_connect_r glinkC (connect1 gstep)).
Local Notation glink1 gstep := (same_connect glinkC (connect1 gstep)).

Fact gcompr_edge_subproof v : predC (gcomp z) (edge (val v)).
Proof. by rewrite /= -(glink1r (glinkE _)) (valP v). Qed.

Fact gcompr_node_subproof v : predC (gcomp z) (node (val v)).
Proof. by rewrite /= -(glink1r (glinkN _)) (valP v). Qed.

Fact gcompr_face_subproof v : predC (gcomp z) (face (val v)).
Proof. by rewrite /= -(glink1r (glinkF _)) (valP v). Qed.

Definition gcompr_edge v : gcompr_dart := Sub _ (gcompr_edge_subproof v).
Definition gcompr_node v : gcompr_dart := Sub _ (gcompr_node_subproof v).
Definition gcompr_face v : gcompr_dart := Sub _ (gcompr_face_subproof v).

Fact gcompr_subproof : cancel3 gcompr_edge gcompr_node gcompr_face.
Proof. by move=> v; apply/val_inj/edgeK. Qed.

Definition gcomp_rem := Hypermap gcompr_subproof.
Definition gcompr (u : gcomp_rem) := val u.
Lemma inj_gcompr : injective gcompr. Proof. exact: val_inj. Qed.
Lemma codom_gcompr : codom gcompr =i predC (gcomp z).
Proof.
move=> x; apply/imageP/idP => [[[y z'Gy] _ ->] // | z'Gx].
by exists ((Sub _ : _ -> gcomp_rem) z'Gx).
Qed.

Lemma patch_gcomp : patch gcompd gcompr [::] [::].
Proof.
do ?split; do [by [] | apply: val_inj | ] => // x; rewrite !inE /= orbF.
by rewrite codom_gcompd codom_gcompr.
Qed.

End PatchGcomp.

Lemma minimal_counter_example_is_connected : forall G,
  minimal_counter_example G -> connected G.
Proof.
move=> G cexG; apply/idPn => cc'G.
apply: (minimal_counter_example_is_noncolorable cexG).
case: (pickP G) => [z _| no_z]; last first.
  by exists (fun _ => Color0); split=> x; have:= no_z x.
have ppG := patch_gcomp z; have minG := minimal_counter_example_is_minimal cexG.
have: planar G := cexG; rewrite (planar_patch ppG) => /andP[planarGd planarGr].
have [bridge'Gd bridge'Gr] := patch_bridgeless ppG cexG.
have: plain G := cexG; rewrite (plain_patch ppG) => /andP[plainGd plainGr].
have: cubic G := cexG; rewrite (cubic_patch ppG) => /andP[cubicGd cubicGr].
move/cubic_precubic in cubicGd; move/cubic_precubic in cubicGr.
apply/(colorable_patch ppG); exists nil.
  have [//||k colk] := minG (gcomp_disk z); last by exists k.
  rewrite card_sub (ltn_leqif (subset_leqif_card (subset_predT _))).
  apply: contra cc'G => /predT_subset allGz; rewrite -(n_comp_connect glinkC z).
  exact/eqP/esym/eq_n_comp_r.
have [//||k colk] := minG (gcomp_rem z); last by exists k.
rewrite card_sub (ltn_leqif (subset_leqif_card (subset_predT _))).
by apply/negP=> /predT_subset/(_ z); rewrite !inE connect0.
Qed.

Coercion minimal_counter_example_is_connected :
  minimal_counter_example >-> connected.

Definition minimal_counter_example_is_planar_bridgeless_plain_connected G :
  minimal_counter_example G -> planar_bridgeless_plain_connected G.
Proof. by move=> cexG; split; apply: cexG. Defined.

Coercion minimal_counter_example_is_planar_bridgeless_plain_connected :
  minimal_counter_example >-> planar_bridgeless_plain_connected.

Definition minimal_counter_example_is_planar_plain_cubic_connected G :
  minimal_counter_example G -> planar_plain_cubic_connected G.
Proof. by move=> cexG; do!split; apply: cexG. Defined.

Coercion minimal_counter_example_is_planar_plain_cubic_connected :
  minimal_counter_example >-> planar_plain_cubic_connected.
