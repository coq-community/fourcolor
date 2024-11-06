(* (c) Copyright 2006-2015 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype path fingraph.
From fourcolor Require Import hypermap walkup geometry color coloring patch.
From fourcolor Require Import snip revsnip birkhoff.

(******************************************************************************)
(* The proof that there exists a contract coloring for any valid contract.    *)
(* We will show in embed.v that contract validity is lifted by the embedding, *)
(* except for the ring condition, which becomes moot.                         *)
(* Definitions:                                                               *)
(*   contract_ring cc r <-> r is a proper ring (simple R-cycle) that is       *)
(*                contracted to its first dart by applying the contract cc -- *)
(*                i.e., the rest of r is in the edge-closure of cc.           *)
(*  We show that valid contracts do not admit contract rings, using the       *)
(* Birkhoff theorem, sparsity, and triads for ring size 5 / contract size 4.  *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition contract_ring (G : hypermap) (cc r : seq G) : Prop :=
  [/\ scycle rlink r, proper_ring r & {subset behead r <= insertE cc}].

Section ContractLemmas.

Variable G : hypermap.
Hypothesis cexG : minimal_counter_example G.

Let planarG : planar G := cexG.
Let bridge'G := bridgeless_cface cexG.
Let plainG : plain G := cexG.
Let cubicG : cubic G := cexG.
Let pentaG : pentagonal G := cexG.
Let ccG : connected G := cexG.
Let noncolG := minimal_counter_example_is_noncolorable cexG.
Let minG := minimal_counter_example_is_minimal cexG.
Let ee := plain_eq cexG.
Let e'id := plain_neq cexG.
Let nnn := cubic_eq cexG.
Let geoG : planar_bridgeless_plain_connected G := cexG. (* revring assumption *)

Lemma sparse_contract_ring (cc : seq G) :
  sparse (insertE cc) -> forall p, contract_ring cc p -> nontrivial_ring 0 p.
Proof.
rewrite /sparse simple_recI /= => cc_sparse.
suffices dF_cc p: contract_ring cc p -> ~ diskF p =i pred0.
  move=> p cc_p; apply/nontrivial0P; split.
    by apply/existsP/pred0P; apply: dF_cc.
  have{cc_p} [URp nt_p cc_p] := cc_p.
  have URp1: scycle rlink (rot 1 p) by rewrite rot_scycle.
  have/(_ _)/pred0P/existsP[|y] := dF_cc (rev_ring (rot 1 p)); last first.
    by rewrite diskF_rev_ring ?proper_ring_rot // diskFC_rot; exists y.
  split=> [||y py]; first exact: scycle_rev_ring.
    by rewrite proper_rev_ring // proper_ring_rot.
  suff: edge y \in insertE cc by rewrite !mem_insertE // -(eq_has (cedge1 y)).
  apply: cc_p; case: (p) py => //= x p1; rewrite rot1_cons /rev_ring.
  by rewrite -map_rev rev_rcons /= -{1}[y]ee (mem_map edgeI) mem_rev.
elim: {p}_.+1 {-2}p (ltnSn (size p)) => // n IHn p le_p_n [URp nt_p cc_p] dF0.
have [cycRp /simple_uniq Up] := andP URp.
case Dp: p (nt_p) => [|x [|x1 p0]] // _.
have p_x: x \in p by rewrite Dp mem_head.
have dNx: x \in diskN p by rewrite diskN_E inE Dp /= mem_head.
move: (negbT (dF0 (node x))) (negbT (dF0 (node (node x)))).
rewrite !inE -!(fclosed1 (diskN_node p)) dNx !andbT !negbK => pFnx pFnnx.
have{pFnx} p_nx: node x \in p.
  without loss dEnx: / node x \in diskE p.
    by rewrite !inE -(fclosed1 (diskN_node p)) dNx andbT => /wlog_neg.
  have pFenx: edge (node x) \in fband p.
    by apply/hasP; exists x; rewrite // -{2}[x]nodeK fconnect1.
  rewrite (fclosed1 (diskE_edge geoG URp)) in dEnx.
  have [[pjnx nxFj] [pjenx enxFj]] := (fprojP pFnx, fprojP pFenx).
  have Djenx: fproj p (edge (node x)) = x.
    rewrite cface1 nodeK cfaceC in enxFj.
    by apply: (scycle_cface URp); rewrite // Dp mem_head.
  have j'x: x != fproj p (node x).
    apply: contraTneq nxFj => <-; by rewrite -{2}[x]nodeK -cface1r bridge'G.
  have j'x1: x1 != fproj p (node x).
    apply: contraTneq nxFj => <-; rewrite cfaceC -[node x]nodeK -cface1r.
    have:= cycRp; rewrite Dp => /andP[/same_cface <- _].
    by rewrite (canRL nodeK (nnn x)) cface1 bridge'G.
  have [i p1 _ Dp1 -> Eip] := rot_to_arc Up p_x pjnx j'x.
  rewrite -[node x]ee -{3}Djenx -cat_cons in Eip.
  case: (IHn (chord_ring p (edge (node x)))) => [||y]; last 1 first.
  - by rewrite diskF_chord_ring ?ee // inE /= dF0 andbF.
  - rewrite -ltnS (leq_trans _ le_p_n) // ltnS -(size_rot i p) Eip Dp1 size_cat.
    by rewrite {2}Dp /arc /= eqxx /= (negPf j'x) (negPf j'x1) !ltnS leq_addl.
  split=> [||y /= q_y]; try by apply: scycle_chord_ring; rewrite ?ee.
    by apply: (proper_chord_ring cexG); rewrite ?ee.
  have p_y: y \in p by rewrite -(mem_rot i) Eip mem_cat q_y orbT.
  apply: cc_p; rewrite Dp in p_y *; case/predU1P: p_y => // y_x.
  by rewrite -(rot_uniq i) Eip -{1}y_x /= mem_cat q_y orbT in Up.
have{dNx pFnnx p_x n IHn le_p_n dF0 cycRp Up URp} p_nnx: node (node x) \in p.
  without loss dEnnx: / node (node x) \in diskE p.
    by rewrite !inE -!(fclosed1 (diskN_node p)) dNx andbT => /wlog_neg.
  have pFennx: edge (node (node x)) \in fband p.
    by apply/hasP; exists (node x); rewrite // -{2}[node x]nodeK fconnect1.
  have [[pjnnx nnxFj] [pjennx ennxFj]] := (fprojP pFnnx, fprojP pFennx).
  have Djennx: fproj p (edge (node (node x))) = node x.
    by rewrite cface1 nodeK cfaceC in ennxFj; apply: (scycle_cface URp).
  have Lp0: last x1 p0 = node x.
    apply: (can_inj (prev_next Up)).
    rewrite -(next_rotr 1 Up) {1}Dp lastI rotr1_rcons /= eqxx.
    apply/esym/(scycle_cface URp); rewrite ?mem_next //.
    by rewrite -(same_cface (next_cycle cycRp p_nx)) -{2}[x]nodeK fconnect1.
  have j'nx: node x != fproj p (node (node x)).
    apply: contraTneq nnxFj => <-.
    by rewrite -{2}[node x]nodeK -cface1r bridge'G.
  have j'x: x != fproj p (node (node x)).
    apply: contraTneq nnxFj => <-.
    by rewrite (canRL nodeK (nnn x)) cfaceC -cface1r bridge'G.
  have [i p1 _ Dp1 ->] := rot_to_arc Up p_nx pjnnx j'nx.
  rewrite -{3}Djennx -cat_cons {p1}Dp1 -{2}[node (node x)]ee -{2}[p](rotrK 1).
  rewrite arc_rot ?rotr_uniq ?mem_rotr // {2}Dp lastI rotr1_rcons /= Lp0.
  rewrite {1}/arc /= eqxx /= (negPf j'nx) (negPf j'x) => Eip.
  case: (IHn (chord_ring p (edge (node (node x))))) => [||y].
  - rewrite -ltnS (leq_trans _ le_p_n) // ltnS -(size_rot i p) Eip size_cat.
    by rewrite !ltnS leq_addl.
  - split=> [||y /= q_y]; first by apply: scycle_chord_ring; rewrite ?ee.
      by rewrite proper_chord_ring ?ee -?(fclosed1 (diskE_edge cexG _)).
    have p_y: y \in p by rewrite -(mem_rot i) Eip mem_cat q_y orbT.
    apply: cc_p; move: p_y; rewrite Dp => /predU1P[y_x | //].
    move: Up; rewrite -(rot_uniq i) Eip/= -[x as X in X \in _]y_x.
    by rewrite !mem_cat/= q_y orbT andbF.
  rewrite diskF_chord_ring ?ee //; first by rewrite inE /= dF0 andbF.
  by rewrite -(fclosed1 (diskE_edge cexG _)).
have x'nx := cubic_neq cexG x.
have{p_nx} cc_nx: node x \in insertE cc.
  by apply: cc_p; move: p_nx; rewrite Dp inE x'nx.
have{p nt_p p_nnx cc_p x1 p0 Dp} cc_nnx: node (node x) \in insertE cc.
  by apply: cc_p; move: p_nnx; rewrite Dp inE (canF_eq nnn) eq_sym x'nx.
elim: cc cc_sparse cc_nx cc_nnx => [|y cc IHcc] //=.
rewrite unfold_in /= !inE => /and3P[/norP[_ yN'cc] eyN'cc cc_sparse].
case/predU1P=> [->|].
  rewrite (cubic_neq cexG) [_ == _](contraFF _ (bridge'G (node (node y)))).
    by move=> cc_ny; case/hasP: yN'cc; exists (node y); rewrite ?fconnect1.
  by move/eqP=> {2}->; rewrite 2!cface1r -{2}[y]nnn !nodeK.
case/predU1P=> [-> | cc_nx].
  rewrite (cubic_neq cexG) [_ == _](contraFF _ (bridge'G (face y))) => [?|].
    by case/hasP: eyN'cc; exists (node (edge y)); last apply: fconnect1.
  by rewrite 2!cface1r -(canRL nodeK (nnn _)) (canRL ee (faceK _)) => /eqP->.
case/predU1P=> [nnx_y | /predU1P[nnx_ey | /IHcc[]//]].
  by case/hasP: yN'cc; exists (node x); last by rewrite cnode1r nnx_y.
by case/hasP: eyN'cc; exists (node x); last by rewrite /= cnode1r nnx_ey.
Qed.

Lemma contract_ring_max (cc p : seq G) :
  contract_ring cc p -> size p <= (size cc).+1.
Proof.
case=> URp nt_p cc_p; pose df x := [predI cc & pred2 x (edge x)].
have Ddf x: x \in behead p -> ~ df x =1 pred0.
  move=> p1x dfx0; have{p1x}:= cc_p x p1x.
  rewrite mem_insertE // => /hasP[y cc_y xEy].
  by rewrite plain_orbit // !inE in xEy; case/andP: (dfx0 y).
have Udf: {in behead p &, injective (fun x => odflt x (pick (df x)))}.
  move=> x y p1x p1y; have [px py] := (mem_behead p1x, mem_behead p1y).
  case: pickP => [x1 /andP[/= _ Dx1] | /(Ddf x p1x)[]//].
  case: pickP => [y1 /andP[/= _ Dy1] | /(Ddf y p1y)[]] //= eq_xy1.
  move: eq_xy1 Dx1 Dy1 => -> /pred2P[] -> /pred2P[] // xey; last exact: edgeI.
    by have:= diskN_edge_ring cexG URp nt_p py; rewrite diskN_E inE /= -xey px.
  by have:= diskN_edge_ring cexG URp nt_p px; rewrite diskN_E inE /= xey py.
have Up1: uniq (behead p).
  by case: (p) (andP URp) => // x p' [_ /simple_uniq/andP[]].
rewrite -add1n -leq_subLR subn1 -size_behead -(card_uniqP Up1).
rewrite -(card_in_image Udf) (leq_trans _ (card_size cc)) //.
apply/subset_leq_card/subsetP=> _ /imageP[x p1x ->].
by case: pickP => [x1 /andP[] | /(Ddf x p1x)].
Qed.

Lemma contract3_valid (cc : seq G) :
  sparse (insertE cc) -> size cc <= 3 -> forall p, ~ contract_ring cc p.
Proof.
move=> cc_sparse cc_le3 p cc_p; have [URp _ _] := cc_p.
have: size p <= 4 by apply: leq_trans (contract_ring_max cc_p) _.
rewrite -ltnS ltn_neqAle => /andP[/negPf p_not5 p_le5].
case/negP: (Birkhoff cexG p_le5 URp); rewrite p_not5.
exact: sparse_contract_ring cc_p.
Qed.

Lemma triad_valid (cc : seq G) x0 :
    sparse (insertE cc) -> size cc = 4 -> triad (insertE cc) x0 ->
  forall p, ~ contract_ring cc p.
Proof.
move=> cc_sparse cc4 triad_x0 p cc_p.
have p_le5: size p <= 5 by rewrite -cc4; apply: (contract_ring_max cc_p).
have{cc_p}[[URp nt_p cc_p] nt0p] := (cc_p, sparse_contract_ring cc_sparse cc_p).
case: (size p =P 5) (Birkhoff cexG p_le5 URp) => [sz_p triv1p | _ /idP[]//].
have [y0 sAy0Fp]: exists y0, {subset adj y0 <= fband p}.
  have [y sAyFp | no_y] := pickP (fun y => adj y \subset fband p).
    by exists y; apply: (subsetP sAyFp).
  have [[y0 dFy0] [y1 dFCy1]] := nontrivial0P _ nt0p.
  case/nontrivial1P: triv1p; split.
    have /subsetPn[y /adjP[z y0Fz zRy] pF'y] := no_y y0.
    exists y0 => //; exists (face (edge z)); last first.
      by rewrite (same_cface y0Fz) -cface1r bridge'G.
    rewrite /rlink cface1 (closed_connect (diskF_face p) y0Fz) in zRy dFy0. 
    rewrite !inE (closed_connect (fbandF p) zRy) (fclosed1 (diskN_node p)).
    by rewrite pF'y edgeK; case/andP: dFy0.
  have /subsetPn[y /adjP[z y1Fz zRy] pF'y] := no_y y1.
  exists y1 => //; exists (face (edge z)); last first.
    by rewrite (same_cface y1Fz) -cface1r bridge'G.
  rewrite /rlink cface1 (closed_connect (diskFC_face p) y1Fz) in zRy dFCy1.
  rewrite !inE (closed_connect (fbandF p) zRy) (fclosed1 (diskN_node p)).
  by rewrite pF'y edgeK; case/andP: dFCy1.
have sFpAy0: {subset fband p <= adj y0}.
  move=> x pFx; apply: contraLR (pentaG y0) => not_y0Ax.
  rewrite -size_spoke_ring -sz_p -ltnNge.
  have URy0 := scycle_spoke_ring cexG y0.
  rewrite -(scycle_fcard_fband URp) -(scycle_fcard_fband URy0).
  rewrite [rhs in _ < rhs](cardD1 (froot face x)) inE (roots_root cfaceC).
  rewrite /= -(closed_connect (fbandF p) (connect_root _ x)) pFx.
  apply/subset_leq_card/subsetP => y /andP/=[Dy].
  rewrite fband_spoke_ring => y0Ay.
  rewrite !inE Dy sAy0Fp // -(eqP Dy) (sameP eqP (rootP cfaceC)).
  by rewrite cfaceC (no_adj_adj not_y0Ax y0Ay).
have [z /andP/=[pF'z] | p_cc] := pickP [predD insertE cc & fband p].
  rewrite mem_insertE // => /hasP[z1 /rot_to[i cc1 Dcc1] z1Ez].
  case/eqP/idPn: sz_p; rewrite neq_ltn orbC ltnNge p_le5 -cc4 ltnS.
  rewrite -(size_rot i cc) Dcc1 /=; apply: contract_ring_max; split=> // t p1t.
  have{p1t} [p_t] := (mem_behead p1t, cc_p t p1t).
  rewrite !mem_insertE // -(has_rot i) Dcc1 /=; case/orP=> //.
  rewrite cedgeC -(same_cedge z1Ez) plain_orbit // !inE => /pred2P[] Dt.
    by case/hasP: pF'z; exists t => //; rewrite Dt.
  case/hasP: pF'z; exists (next p t); first by rewrite mem_next.
  by rewrite -[z]ee -Dt; case/andP: URp => cycRp _; apply: (next_cycle cycRp).
have [[x0Fy0 [_] | x0F'y0 []]] := (boolP (cface x0 y0), andP triad_x0).
  case/subsetP=> x cc_c; rewrite inE (adjF x0Fy0) [adj _ _]sFpAy0 //.
  by apply: contraFT (p_cc x); rewrite !inE => ->.
rewrite ltnNge (leq_trans _ (fcard_adj_max cexG x0F'y0)) //.
apply: (@leq_trans (count (mem (fband (insertE cc))) (spoke_ring x0))).
  rewrite /spoke_ring count_map; elim: (orbit face x0) => //= z q IHq.
  rewrite rev_cons -cats1 count_cat /= -(fclosed1 (fbandF _)) addn0.
  by rewrite addnC leq_add2r.
rewrite -size_filter -simple_fcard_fband; last first.
  have /andP[_] := scycle_spoke_ring cexG x0; rewrite !simple_recI.
  elim: (spoke_ring x0) => //= z q IHq /andP[qF'z /IHq].
  case: ifP => //= ccEFz; rewrite (contra _ qF'z) => // /hasP[t].
  by rewrite mem_filter => /andP[_ qt] tFz; apply/hasP; exists t.
apply/subset_leq_card/subsetP => z; rewrite !inE => /andP[-> /hasP[t]].
rewrite mem_filter /= => /andP[/hasP[u ccEu tFu] x0r_t] zFt; apply/andP; split.
  apply: contraFT (p_cc u) => /= /contra-> //. 
  by rewrite (adjFr zFt) (adjFr tFu) => /sFpAy0.
by rewrite -fband_spoke_ring; apply/hasP; exists t.
Qed.

Theorem contract_coloring (r cc : seq G) :
  valid_contract r cc -> cc_colorable cc.
Proof.
case=> _ cc_sparse cc_1to4 cc_triad.
have{r cc_sparse cc_triad}: forall p, ~ contract_ring cc p.
  case/or4P: cc_1to4 => /eqP Ecc; try by apply: contract3_valid; rewrite ?Ecc.
  by have /exists_inP[x0 _]:= cc_triad Ecc; apply: triad_valid.
have{cc_1to4}: #|G| < (0  < size cc) + #|G| by case: (size cc) cc_1to4.
move: {2}(size cc) (leqnn (size cc)) => n.
move: {-2}#|G| minG (cexG : planar_bridgeless_plain_precubic G) => nG min_nG.
elim: n G cc => [|n IHn] G0 [|x cc] geoG0 //=.
- by move=> _ /min_nG[] // k; exists k.
- exact: (IHn G0 [::]).
rewrite /= add1n !ltnS => le_cc_n G0_lenG ring'cc.
have plainG0: plain G0 := geoG0; have ee0 := plain_eq geoG0.
have bridge'G0 := bridgeless_cface geoG0.
have D_E0 (y : G0): cedge x y = (y == x) || (y == edge x).
  by rewrite (plain_orbit geoG0) !inE.
pose G1 := WalkupF x; pose h1 (u : G1) : G0 := val u.
have Ih1: injective h1 by apply: val_inj.
have x'ex: edge x != x by rewrite (plain_neq geoG0).
pose uex : G1 := Sub (edge x) x'ex.
pose G2 := WalkupF uex; pose h2 (w : G2) : G1 := val w.
have Ih2: injective h2 by apply: val_inj.
pose h w := h1 (h2 w); have Ih: injective h := inj_comp Ih1 Ih2.
have Eh: codom h =i predC (cedge x).
  move=> y; rewrite inE D_E0; apply/imageP/norP => [[w _ ->] | [x'y ex'y]].
    by rewrite (valP w) (valP (val w)).
  by exists ((Sub (Sub y x'y : G1) : _ -> G2) ex'y).
have xE'h w: cedge x (h w) = false.
  by apply: negPf; rewrite -[~~ _]Eh codom_f.
have hN w w': cnode w w' = cnode (h w) (h w') by rewrite !fconnect_skip.
have hE w w': cedge w w' = cedge (h w) (h w') by rewrite !fconnect_skip.
have h_e w: h (edge w) = edge (h w).
  have ewP: edge (h w) \in codom h by rewrite Eh inE -cedge1r -[~~ _]Eh codom_f.
  rewrite -(f_iinv ewP); congr h; symmetry.
  by do 2 apply: (valE_skip nodeI); apply: (f_iinv ewP).
pose xR y := has (cface y) [:: x; edge x].
have hF w w': cface w w' = (if xR (h w) then xR (h w') else cface (h w) (h w')).
  transitivity (cface (h2 w) (h2 w')).
    rewrite [cface _ _](eq_fconnect (glink_fp_skip_edge _)) ?fconnect_skip //.
    by rewrite /glink /= orbCA -val_eqE /= ee0 !eqxx.
  case: ifP => xRw; last exact: (same_cskip_edge (negbT _)).
  by apply: cskip_edge_merge; first rewrite /cross_edge /= bridge'G0.
have ee2 w: edge (edge w) = w :> G2 by apply: Ih; rewrite !h_e ee0.
have plainG2: plain G2.
  by apply/plainP => w _; split; rewrite // -(inj_eq Ih) h_e plain_neq.
have geoG2: planar_bridgeless_plain_precubic G2.
  repeat split; auto; first exact (planar_WalkupF _ (planar_WalkupF _ geoG0)).
    apply/existsP=> [] [w wFew].
    have [y xEy cycRwy]: exists2 y, cedge x y & cycle rlink [:: h w; y].
      move: wFew; rewrite hF h_e /= bridge'G0.
      case: ifP => //; rewrite /xR /= !orbF => /orP[wFx | wFex].
        rewrite cfaceC -(same_cface wFx) bridge'G0 /= => ewFex.
        by exists (edge x); rewrite ?fconnect1 /rlink //= ewFex ee0 cfaceC wFx. 
      rewrite orbC cfaceC -(same_cface wFex) bridge'G0 /= => ewFx.
      by exists x; rewrite /rlink //= ewFx cfaceC wFex.
    case: (ring'cc [:: h w; y]); split => [||z].
    - rewrite /scycle cycRwy simple_recI /=; have [ewRy _] := andP cycRwy.
      by rewrite unfold_in /= cfaceC -(same_cface ewRy) cfaceC bridge'G0.
    - by apply: contraTneq (codom_f h w) => Dy; rewrite Eh inE cedge1r Dy xEy.
    by rewrite !inE orbA => /eqP ->; rewrite -D_E0 xEy.
  apply/subsetP=> w _; apply: leq_trans (precubic_leq geoG0 (h w)).
  rewrite /order -(card_image Ih); apply/subset_leq_card/subsetP=> y.
  by case/imageP=> w1 wNw1 ->; rewrite inE -hN.
pose cc1 := filter (predC (cedge x)) cc; pose cc2 := preim_seq h cc1.
have Excc y: (y \in insertE (x :: cc)) = cedge x y || (y \in insertE cc1).
  rewrite /= !inE orbA -D_E0 !mem_insertE //; apply: orb_id2l=> xN'y.
  rewrite !(eq_has (plain_orbit geoG0 y)) !(has_sym [:: y; _]) /=.
  by rewrite !mem_filter !inE -cedge1r xN'y.
have hcc2: map h cc2 = cc1.
  by apply: map_preim => y; rewrite Eh mem_filter => /andP[].
have hEcc1 w1: (h w1 \in insertE cc1) = (w1 \in insertE cc2).
  by rewrite !mem_insertE // -hcc2 has_map; apply: eq_has => w; rewrite /= hE.
have le_cc2_cc: size cc2 <= size cc.
  by rewrite -(size_map h) hcc2 size_filter count_size.
have{IHn} [] := IHn G2 cc2 geoG2 (leq_trans le_cc2_cc le_cc_n).
- rewrite -card_S_Walkup card_Walkup (leq_trans (leq_pred _)) //.
  by rewrite (leq_trans G0_lenG) // leq_addl.
- move=> p [URp nt_p cc_p] //.
  have [cycRp UpF] := andP URp; have Up := simple_uniq UpF.
  have UhpF: simple (map h p).
    rewrite /simple -map_comp map_inj_in_uniq // => w1 w2 pw1 pw2.
    move/(rootP cfaceC)=> w1Fw2; apply: (simple_cface UpF) pw1 pw2 _.
    by rewrite hF /xR (eq_has (same_cface w1Fw2)); case: (has _ _).
  have cc_hp: {subset map h (behead p) <= insertE cc}.
    move=> _ /mapP[w1 pw1 ->].
    by have:= Excc (h w1); rewrite /= !inE orbA -D_E0 xE'h hEcc1 cc_p.
  suffices cycRhp: scycle rlink (map h p).
    have [] := ring'cc (map h p); split=> //.
      by case: (p) nt_p => [|w0 [|w1 [|w2 p2]]]; rewrite /= -?h_e.
    by rewrite behead_map => y /cc_hp cc_y; rewrite 2?mem_behead.
  apply: wlog_neg; rewrite UhpF andbT => cyc'Rhp.
  pose prevRh := [pred w | rlink (h (prev p w)) (h w)].
  have{cyc'Rhp} /hasP[w1 pw1 /= prevRh'w1]: has (predC prevRh) p.
    rewrite has_predC; apply: contra cyc'Rhp => /allP cycRhp.
    rewrite cycle_from_prev ?map_inj_uniq // => _ /mapP[w1 pw1 ->].
    by rewrite prev_map //; apply: cycRhp.
  have [i1 p1 Dp1] := rot_to pw1; pose w0 := last w1 p1.
  have p1'w1: w1 \notin p1 by move: Up; rewrite -(rot_uniq i1) Dp1 => /andP[].
  have /andP[w0Rw1 w1Rp1]: rlink w0 w1 && path rlink w1 p1.
    by have:= cycRp; rewrite -(rot_cycle i1) Dp1 (cycle_path w1).
  have{prevRh'w1} hw0R'w1: ~~ rlink (h w0) (h w1).
    move: prevRh'w1; rewrite -(prev_rot i1) // prev_nth Dp1 mem_head.
    by rewrite -{2}[p1]cats0 index_cat (negPf p1'w1) addn0 nth_last.
  have /andP[xRew0 xRw1]: xR (edge (h w0)) && xR (h w1).
    by move: w0Rw1; rewrite /rlink hF h_e [cface _ _](negPf hw0R'w1).
  have /hasP[x1 xEx1 w1Fx1] := xRw1 : has _ [:: x; _].
  have /hasP[x0 xEx0 ew0Fx0] := xRew0 : has _ [:: x; _].
  have ex0_x1: edge x0 = x1.
    have: cedge x0 x1.
      by rewrite -!plain_orbit // in xEx0 xEx1; rewrite -(same_cedge xEx0).
    rewrite plain_orbit // !inE => /pred2P[] // x01.
    by rewrite /rlink (same_cface ew0Fx0) -x01 cfaceC w1Fx1 in hw0R'w1.
  pose q1 := x0 :: (map h (w1 :: p1)).
  have p1R'x: ~~ has (preim h xR) p1.
    apply: contra p1'w1 => /hasP[w2 p1w2 /= xRw2].
    have w1Fw2: cface w1 w2 by rewrite hF xRw1.
    by rewrite (scycle_cface URp _ _ w1Fw2) // -(mem_rot i1) Dp1 mem_behead.
  have cycRq1: cycle rlink q1.
    rewrite (cycle_path x0) /= {1 2}/rlink last_map ew0Fx0 ex0_x1 cfaceC w1Fx1.
    elim: (p1) (w1) p1R'x w1Rp1 => //= w3 p2 IHp w2 /norP[xR'w3 xR'p2] /andP[].
    by rewrite {1 3}/rlink cfaceC hF (negPf xR'w3) cfaceC h_e => -> /IHp->.
  case Dp: p => // [w p0] in nt_p.
  have /rot_to[i2 q2 Dq2]: h w \in q1.
    by rewrite /q1 -Dp1 inE mem_map // mem_rot Dp mem_head orbT.
  have URq2: scycle rlink (h w :: q2).
    rewrite -Dq2 /scycle rot_cycle cycRq1 /= simple_rot /q1 simple_cons.
    apply/andP; split; last by rewrite -Dp1 /= map_rot simple_rot.
    rewrite unfold_in; apply: contra p1R'x => /hasP[x3].
    rewrite /= inE -has_map => /predU1P[-> /idPn[] | p1x3 x0Fx3].
      by rewrite cfaceC (same_cface w1Fx1) -ex0_x1 cfaceC bridge'G0.
    by apply/hasP; exists x3 => //=; apply/hasP; exists x0; rewrite // cfaceC.
  case: (ring'cc (h w :: q2)); split=> //.
    move: nt_p; rewrite -Dp -Dq2 proper_ring_rot // -(proper_ring_rot i1) //.
    by rewrite Dp1 /q1 /=; case: (p1).
  move=> y q2y; rewrite /= !inE orbA -mem_seq2.
  move: (mem_behead q2y); rewrite -Dq2 mem_rot /q1 -Dp1 /= inE map_rot mem_rot.
  move/predU1P=> [->|]; first by rewrite xEx0.
  rewrite Dp /= inE (negPf (memPn _ y q2y)) => [/mapP[u p0u ->]|].
    by rewrite orbC cc_hp // map_f // Dp.
  by case/andP: URq2 => _ /simple_uniq/andP[].
move=> k [kE /fconnect_invariant kF].
pose a y := [pred w | cface y (h w)].
have nt_ah w: ~ a (h w) =1 pred0 by move/(_ w); rewrite /= connect0.
have ae0 y: a y =1 pred0 -> a (edge y) =1 pred0.
  move=> ay0 w; have [hy | h'y] := boolP (y \in codom h).
    by case/idP: (ay0 (iinv hy)); rewrite /= f_iinv connect0.
  have [hfy | h'fy] := boolP (face y \in codom h).
    by case/idP: (ay0 (iinv hfy)); rewrite /= f_iinv fconnect1.
  move: h'y h'fy; rewrite !Eh !negbK => /same_cedge xEy.
  rewrite xEy plain_orbit // mem_seq2 orbC => /pred2P[fy_ey | fy_y].
    by have:= bridge'G0 y; rewrite -fy_ey fconnect1.
  move: (precubic_leq geoG0 y) (f_finv nodeI y); rewrite /finv.
  rewrite -[_ <= 3](mem_iota 0 4) !inE -{1}orderSpred /=.
  case/or3P=> /eqP-> /= => [ny_y | nny_y | n3y_y]; last 1 first.
  - have:= bridge'G0 (face (edge y)); rewrite -{2}(canRL nodeK n3y_y).
    by rewrite 2!cface1r nodeK -{2}fy_y -{2}[y]ee0 edgeK connect0.
  - by have:= bridge'G0 y; rewrite -{1}[y]nodeK ny_y -cface1 connect0.
  have cycFy1: fcycle face [:: edge y].
    by rewrite /= -(canRL nodeK nny_y) (canF_eq nodeK) ee0 fy_y eqxx.
  rewrite (fconnect_cycle cycFy1) ?inE ?eqxx //.
  by move: (xE'h w); rewrite xEy plain_orbit // mem_seq2 => /norP[_ /negPf].
pose k0 y := oapp k Color0 (pick (a y)).
have k0h w: k0 (h w) = k w.
  rewrite /k0; case: pickP => [w1 /= wFw1 | /nt_ah//]; apply: kF.
  by rewrite hF cfaceC wFw1 /xR (eq_has (same_cface wFw1)); case: (has _ _).
have k0ex: k0 x = k0 (edge x).
  rewrite /k0; case: pickP => [w /= wFx | /ae0 aex0]; last first.
    by case: pickP => // w1; rewrite aex0.
  case: pickP => /= [w1 w1Fex | /ae0/(_ w)]; last by rewrite ee0 /= wFx.
  by apply: kF; rewrite hF /xR /= cfaceC wFx /= orbCA cfaceC w1Fex.
exists k0; split=> y; last first.
  by apply/eqP; rewrite /k0 -(@eq_pick _ (a y)) // => w /=; rewrite cface1.
rewrite Excc !inE /invariant in kE *.
have [] := boolP (cedge x y).
  by rewrite plain_orbit // mem_seq2 => /pred2P[]->; rewrite ?ee0 -k0ex eqxx.
by rewrite -[~~ _]Eh => hy; rewrite -(f_iinv hy) -h_e !k0h [_ == _]kE hEcc1.
Qed.

End ContractLemmas.
