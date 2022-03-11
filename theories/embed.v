(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype path fingraph.
From fourcolor Require Import hypermap geometry color chromogram coloring patch.
From fourcolor Require Import snip revsnip kempe birkhoff contract.

(******************************************************************************)
(*   This is the crux of the Four Color Theorem proof: we build an injective  *)
(* embedding of a configuration map from the partial embedding constructed by *)
(* the part quiz and derive a contradiction from the reducibility property.   *)
(*   Since we end with a contradiction all definitions here are local, in the *)
(* context of a C-reducible configuration remainder hypermap Gc with          *)
(* embeddable perimeter rc, with a preembedding h from ac := kernel rc into a *)
(* minimal counterexample hypermap Gm.                                        *)
(*  pre_hom_ring x p <-> both x :: p and its image under h are R-link paths,  *)
(*               and x :: p in included in ac.                                *)
(*    embed == an extension of h from ac to an embedding of bc = [predC rc].  *)
(*  embed_disk == the disk hypermap delimited by rev_ring rc in Gc, but       *)
(*               constructed explicitly with contents bc.                     *)
(*  embd_ring, embd, embdd == perimeter, and injections of embed_disk into Gc *)
(*               and Gm (via embed), respectively.                            *)
(*  embed_rem == the remainder hypermap whose contents is the complement of   *)
(*               the codomain of embdd (i.e., the image of bc by embed).      *)
(*  embr_ring, embr == perimeter and injection of embed_ring into Gm.         *)
(* embed_cotrace et <-> et is the trace on rotr 1 embr_ring of a coloring of  *)
(*               embed_rem.                                                   *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Embeddings.

Variables (Gm Gc : hypermap) (rc cc : seq Gc) (h : Gc -> Gm).

Let rrc := rev rc.
Notation ac := (kernel rc).
Notation bc := [predC rc].
Let ac_bc : {subset ac <= bc} := subsetP (kernel_off_ring rc).
Let acF := kernelF rc.

Hypothesis cexGm : minimal_counter_example Gm.
Hypothesis embedGc : embeddable rc.
Hypothesis embed_h : preembedding ac h.
Hypothesis Cred_cc : C_reducible rc cc.

Let planarGm : planar Gm := cexGm.
Let bridge'Gm := bridgeless_cface cexGm.
Let plainGm : plain Gm := cexGm.
Let e2m := plain_eq cexGm.
Let n3m := cubic_eq cexGm.
Let pentaGm : pentagonal Gm := cexGm.
Let geoGm : planar_bridgeless_plain_connected Gm := cexGm.

Let planarGc : planar Gc := embedGc.
Let bridge'Gc := bridgeless_cface embedGc.
Let plainGc : plain Gc := embedGc.
Let cubicGc : quasicubic rc := embedGc.
Let e2c := plain_eq embedGc.
Let n3c := quasicubic_eq cubicGc.
Let geoGc : planar_bridgeless_plain_connected Gc := embedGc.
Let UNrc : sfcycle node rc := embedGc.
Let cycNrc := scycle_cycle UNrc.
Let Urc := scycle_uniq UNrc.
Let UrcF := scycle_simple UNrc.

Notation hc := (edge_central h).
Let hcE : {mono edge : x / x \in hc}. Proof. exact: edge_central_edge. Qed.
Let hF := preembedding_face embed_h.
Notation h_spoke := ((preembedding_simple_path embed_h acF) _ _).

Lemma embed_functor x : x \in ac -> edge x \in ac -> h (edge x) = edge (h x).
Proof.
suffices{x}: ~ exists2 x, x \in [predD ac & hc] &
  exists2 p, scycle rlink (x :: p) & {subset p <= [predI ac & hc]}.
- move=> IH ac_x ac_ex; apply/eqP/idPn=> eh'hex; case: IH.
  exists x => [|{eh'hex}]; first by rewrite !inE eh'hex.
  case: {ac_ex ac_x}(h_spoke ac_ex ac_x) => p []; case/lastP: p => // p y xRp.
  rewrite last_rcons all_rcons => yFx _ [Up /andP[_ /allP ac_p]].
  exists p => //; rewrite /scycle /= rcons_path -(rlinkFr yFx) -rcons_path xRp.
  by rewrite simple_cons -(closed_connect (fbandF p) yFx) -simple_rcons.
suffices: ~ exists2 x, x \notin hc & exists2 p, scycle rlink (x :: p) &
  {subset p <= hc} /\ {subset diskN (x :: p) <= ac}.
- move=> IH [x /andP[/= eh'hex ac_x] [p URp hac_p]].
  have ac_xp: {subset (x :: p) <= ac} by move=> y /predU1P[-> | /hac_p/andP[]].
  have [dF'rc|] := boolP (all [predC diskF (x :: p)] rc).
    case: IH; exists x => //; exists p => //.
    split=> [y | y dNy]; first by case/hac_p/andP.
    case xpFy: (y \in fband (x :: p)).
      case/(@hasP _ _ (x :: p)): xpFy => z pz yFz.
      by rewrite (closed_connect acF yFz) ac_xp.
    apply: contraL dF'rc => /hasP[z rc_z yFz].
    rewrite all_predC negbK; apply/hasP; exists z => //=.
    by rewrite -(closed_connect (diskF_face _) yFz) !inE xpFy.
  have rr_xp1: rev_ring (rot 1 (x :: p)) = edge x :: rev_ring p.
    by rewrite {1}/rev_ring map_rot /= rot1_cons rev_rcons.
  have URp1: scycle rlink (rot 1 (x :: p)) by rewrite rot_scycle.
  rewrite all_predC negbK => /= dF'rc.
  case: IH; exists (edge x); first by rewrite hcE.
  exists (rev_ring p); first by rewrite -rr_xp1; apply: scycle_rev_ring.
  split=> y; first by rewrite -hcE /= mem_rev_ring // => /hac_p/andP[].
  have proper_xp1: proper_ring (rot 1 (x :: p)).
    rewrite proper_ring_rot //; case: (p) URp hac_p => [|x2 []] //=.
      by rewrite /scycle /= /rlink cfaceC bridge'Gc.
    move=> _ /allP/=/andP[/andP[_ hcx2] _]; apply: contraTneq hcx2 => <-.
    by rewrite /= hcE.
  rewrite /= -rr_xp1 diskN_rev_ring // inE => /= dNr'y.
  apply/hasP => [] [z rcz yFz].
  have: z \in diskF (x :: p).
    apply/andP; split.
      apply/hasP=> [] [t rct tFz]; case/ac_xp/hasP: rct.
      by exists z; rewrite // cfaceC.
    case/hasP: dF'rc => t; rewrite -(fconnect_cycle cycNrc rcz) => zNt /=.
    by rewrite (closed_connect (diskN_node _) zNt) => /andP[].
  rewrite -(closed_connect (diskF_face _) yFz) => /andP[_].
  rewrite /= unfold_in => /hasP[y1 xpy1 yDy1].
  case/hasP: dNr'y; exists y1; first by rewrite mem_rot.
  apply: etrans yDy1; apply: {y1 xpy1}eq_connect => y1 y2.
  by rewrite /dlink /= mem_rot.
case=> x hc'x [p URp []]; move: {2}_.+1 (ltnSn #|diskN (x :: p)|) URp => n.
elim: n => // n IHn in x hc'x p *; rewrite ltnS => le_dN_n URp p_hc dN_ac.
set xp := x :: p in le_dN_n URp p_hc dN_ac.
have dNx: x \in diskN xp by rewrite diskN_E inE /= mem_head.
have dNnx: node x \in diskN xp by rewrite -(fclosed1 (diskN_node xp)).
have dNnnx: node (node x) \in diskN xp by rewrite -(fclosed1 (diskN_node xp)).
have [cycRp UpF] := andP URp; have Up := simple_uniq UpF; rewrite /xp in cycRp.
case Dp0: p (cycRp) => [|x0 p0]; first by rewrite /= /rlink cfaceC bridge'Gc.
clear 1; pose enx := edge (node x); pose p1 := rcons p enx.
have xRp1: path rlink x p1.
  by rewrite rcons_path /= {2}/rlink cface1r /enx nodeK -rcons_path.
have{UpF} Up1: simple p1.
  have enxFx: cface enx x by rewrite cface1 nodeK.
  by rewrite /p1 simple_rcons (closed_connect (fbandF p) enxFx) -simple_cons.
have [n3x x'nx] := cubicP cubicGc _ (ac_bc (dN_ac x dNx)).
case hc_nx: (node x \in hc).
  case hc_nnx: (node (node x) \in hc).
    case/eqP: hc'x; apply: faceI; rewrite -(canRL nodeK (n3m _)).
    do 2!apply: (canRL (canF_sym nodeK)); rewrite -{1}n3x -hF; last first.
      by rewrite inE /= (fclosed1 (fbandF rc)) nodeK [~~ _]dN_ac.
    rewrite nodeK -(eqP hc_nnx) -hF; last first.
      by rewrite inE /= (fclosed1 (fbandF rc)) nodeK [~~ _]dN_ac.
    rewrite nodeK -(eqP hc_nx) -hF ?nodeK //.
    by rewrite inE /= (fclosed1 (fbandF rc)) nodeK [~~ _]dN_ac.
  pose ennx := edge (node (node x)).
  pose i := find (cface ennx) p1; pose q := ennx :: take i p1.
  have le_i_p1: i <= size p1 by apply: find_size.
  have URq: scycle rlink q.
    have{xRp1} ennxRp1: path rlink ennx p1.
      move: xRp1; rewrite -(drop0 p1) (drop_nth x) ?nth0 ?size_rcons //=.
      by rewrite {3}/rlink /= e2c (canRL nodeK n3x) -cface1.
    apply/andP; move: le_i_p1 ennxRp1 Up1; rewrite leq_eqVlt.
    case/predU1P=> [eq_i_p1 | lt_i_p1].
      rewrite /q eq_i_p1 take_size /= rcons_path simple_cons => -> ->.
      rewrite last_rcons /rlink /= cface1r nodeK e2c [_ \in _]has_find -/i.
      by rewrite eq_i_p1 ltnn.
    rewrite -(cat_take_drop i.+1 p1) (take_nth x) //= cat_path last_rcons.
    have ennxFi: cface ennx (nth x p1 i) by apply: nth_find; rewrite has_find.
    rewrite !rcons_path -(rlinkFr ennxFi) simple_cat => /andP[-> _] /andP[].
    rewrite -rot1_cons simple_rot !simple_cons.
    by rewrite -(closed_connect (fbandF _) ennxFi).
  have p1_hc: {subset take i p1 <= hc}.
    move=> y /mem_take; rewrite mem_rcons => /predU1P[-> | /p_hc//].
    by rewrite hcE.
  have dNq'x: (x \in diskN q) = false.
    rewrite 2!(fclosed1 (diskN_node q)) -[node _]e2c.
    apply: (diskN_edge_ring geoGc URq _ (mem_head _ _)).
    rewrite /q; case Dp2: (take i p1) => [|x1 [|x2 p2]] //.
      by rewrite /scycle /q Dp2 /= /rlink cfaceC bridge'Gc in URq.
    apply: contraFN hc_nnx; rewrite e2c => /eqP->.
    by rewrite p1_hc //= Dp2 ?mem_head.
  suffices dNq_dN: {subset diskN q <= diskN xp}.
    have{hc_nnx} hc'ennx: ennx \notin hc by rewrite hcE hc_nnx.
    case: {IHn}(IHn _ hc'ennx (take i p1)) => // [|_ /dNq_dN/dN_ac//].
    apply: leq_trans le_dN_n; rewrite -/q [rhs in _ < rhs](cardD1 x) dNx ltnS.
    apply/subset_leq_card/subsetP=> y dNq_y; rewrite !inE dNq_dN // andbT.
    by apply: contraFN dNq'x => /eqP <-.
  move=> t; rewrite unfold_in => /hasP[z q_z /connectP[r yDr ->{t}]].
  move: yDr; set y := finv node z.
  have: y \in diskN xp /\ y \in diskN q.
    rewrite !(fclosed1 (diskN_node _) y)(f_finv nodeI) !diskN_E !in_simpl /=.
    rewrite q_z /= inE /= orbAC orbC -implyNb; split=> //; apply/implyP=> p'z.
    move: q_z; rewrite inE /p1 -cats1 take_cat // 2!fun_if mem_cat.
    case/predU1P=> [-> | ].
      rewrite -(fclosed1 (diskE_edge planarGc URp)) inE /= dNnnx orbC.
      rewrite (contraFN _ hc_nnx) // inE -(inj_eq nodeI) n3x.
      by rewrite eq_sym (negPf x'nx) => /p_hc.
    rewrite (contraNF (@mem_take i _ p z) p'z) (negPf p'z).
    rewrite ltn_neqAle; case: eqP => [-> | _ /=]; first by rewrite subnn.
    rewrite -ltnS -(size_rcons p enx) -has_find; case: ifPn => // p1F'ennx.
    case: (i - _) => //= _; rewrite inE => /eqP Dz.
    rewrite Dz -(fclosed1 (diskE_edge planarGc URp)) inE orbC /= dNnx.
    rewrite inE (negPf x'nx) (contra _ p1F'ennx) // => pnx.
    apply/hasP; exists (node x); first by rewrite mem_rcons mem_behead.
    by rewrite cface1 nodeK.
  elim: {z q_z}r y => [|z r IHr] y [dNy dNq_y] //=.
  rewrite {1}/dlink /= -andbA => /and3P[q'y yCz]; apply: {r}IHr.
  rewrite !(fclosed1 (diskN_node _) z).
  have{z yCz} [<- // | <-] := clinkP yCz.
  rewrite !diskN_E !in_simpl /= !(fclosed1 (diskE_edge _ _) (node _)) //.
  rewrite !faceK !in_simpl /= q'y {}dNy dNq_y orbT andbT; split=> //.
  apply/orP; right; rewrite inE; case: eqP (dNq'x) => [<- /idP// | _ _] /=.
  apply: contra q'y => py; rewrite !inE -[p1]cats1 take_cat orbC {le_i_p1}.
  case: ifP => lt_i_p; last by rewrite mem_cat py.
  without loss{py}: / y \in drop i p.
    by move: py; rewrite -{1}(cat_take_drop i p) mem_cat => /orP[] -> // ->.
  rewrite (drop_nth x) // => p_y; case/idP: dNq'x.
  move: (mem_rot 1 xp) cycRp Up; rewrite -(rot_uniq 1) rot1_cons /=.
  rewrite -(cat_take_drop i.+1 p) rcons_cat.
  case/splitPl: p_y => r0 r Lr0; rewrite rcons_cat cat_uniq catA.
  rewrite -[x in x \in _](last_rcons y r); move: {r}(rcons r x) => r.
  rewrite has_cat cat_path last_cat (take_nth x) // last_rcons {}Lr0.
  move=> Dxp /andP[_ yRr] /and3P[_ /norP[_ Ur] _].
  have{r0 Dxp Ur}: ~~ has (mem (fband q)) r.
    apply: contra Ur => /hasP[z rz /= qFz]; apply/hasP; exists z => //=.
    have /hasP[t p_t zFt]: z \in fband (rcons (take i p) (nth x p i)).
      move: qFz; rewrite -rot1_cons fband_rot !fband_cons -[p1]cats1 take_cat.
      rewrite lt_i_p; congr (_ || _); apply: (same_connect_r cfaceC).
      suffices: cface ennx (nth x p1 i) by rewrite nth_rcons lt_i_p.
      by apply: nth_find; rewrite has_find size_rcons leqW.
    by rewrite (scycle_cface URp _ _ zFt) // -Dxp !mem_cat (p_t, rz) ?orbT.
  elim: r y dNq_y yRr => //= z r IHr y dNq_y /andP[yRz rRr] /norP[qF'z qF'r].
  suffices: z \in diskF q by case/andP=> _ /IHr->.
  rewrite /rlink cface1 in yRz; rewrite -(closed_connect (diskF_face q) yRz).
  rewrite inE /= (closed_connect (fbandF q) yRz) qF'z.
  by rewrite (fclosed1 (diskN_node q)) edgeK.
have dNenx: enx \in diskN xp.
  rewrite diskN_E inE orbC /= -(fclosed1 (diskE_edge _ _)) // inE /= dNnx.
  by rewrite (contraFN _ hc_nx) // inE (negPf x'nx); apply: p_hc.
have ac_eenx: edge enx \in ac by rewrite e2c dN_ac.
have [q1 [enxRq1 Lq1 ntq1] [Uq1 q1_ac]] := h_spoke ac_eenx (dN_ac _ dNenx).
pose i := find (mem (fband p1)) q1; pose q2 := take i q1.
have Upq2: ~~ has (mem (fband q2)) p1.
  apply/hasP=> [] [y p1y] /(has_nthP x)[j].
  rewrite size_take leq_min => /andP[ltji _]; rewrite nth_take // => yFq1j.
  by have /hasP[] := before_find x ltji; exists y; last by rewrite cfaceC.
have p1Fq1: has (mem (fband p1)) q1.
  apply/hasP; exists (last enx q1).
    by case: (q1) ntq1 => //= nx' q11 _; apply: mem_last.
  by apply/hasP; exists enx; first by rewrite mem_rcons mem_head.
have lt_i_q1: i < size q1 by rewrite -has_find.
have /hasP[y p1y y1Fy] := nth_find x p1Fq1.
move: (simple_uniq Up1) Upq2 (last_rcons y p enx) {Up}; rewrite -/p1.
case/splitPr Dp: p1 / p1y => [p2 p3] Up.
rewrite last_cat /= has_cat => /norP[Up2q Up3q] Lp3.
pose q3 := q2 ++ belast y p3; pose q := enx :: q3.
have{y1Fy} URq: scycle rlink q.
  apply/andP; split.
    rewrite /= -{2}Lp3 rcons_cat -lastI cat_path.
    rewrite -(cat_take_drop i q1) -/q2 (drop_nth x) // cat_path in enxRq1.
    case/and3P: enxRq1 => ->; rewrite (rlinkFr y1Fy) /= => -> _.
    by have:= xRp1; rewrite Dp cat_path /= => /and3P[].
  rewrite -(simple_rot 1) rot1_cons rcons_cat -Lp3 -lastI simple_cat Up3q /=.
  have:= Uq1; rewrite -(cat_take_drop i q1) simple_cat => /andP[-> _].
  by have:= Up1; rewrite Dp simple_cat => /and3P[].
have p3_p: {subset (belast y p3) <= p}.
  have ->: p = behead (belast x p1) by rewrite belast_rcons.
  rewrite Dp belast_cat /= -cat_rcons -lastI /=.
  by move=> z p3z; rewrite mem_cat p3z orbT.
have q3_hc: {subset q3 <= hc}.
  move=> z; rewrite mem_cat => /orP[/mem_take q1z | /p3_p/p_hc//].
  by have /andP[] := allP q1_ac z q1z.
have dNq'x: (x \in diskN q) = false.
  rewrite (fclosed1 (diskN_node q)) -[node x]e2c -/enx.
  apply: diskN_edge_ring (mem_head _ _) => //.
  case/andP: URq (q3_hc (node x)); rewrite /q hc_nx.
  case: (q3) => [|y2 [_ _|]] //=; first by rewrite /rlink e2c bridge'Gc.
  by move/implyP; rewrite inE implybF e2c.
suffices{IHn} dNq_dN: {subset diskN q <= diskN xp}.
  have{hc_nx} hc'enx: enx \notin hc by rewrite hcE hc_nx.
  case: {IHn}(IHn _ hc'enx q3) => // [|_ /dNq_dN/dN_ac//].
  apply: leq_trans le_dN_n; rewrite -/q [rhs in _ < rhs](cardD1 x) dNx ltnS.
  apply/subset_leq_card/subsetP=> z dNq_z; rewrite !inE dNq_dN // andbT.
  by apply: contraFN dNq'x => /eqP <-.
move=> z0 /(@hasP _ _ q)[z2 qz2 /connectP[r z1Dr ->]]; move: z1Dr.
set z1 := finv node z2.
have{qz2}: z1 \in diskN xp /\ z1 \in diskN q.
  rewrite !(fclosed1 (diskN_node _) z1) (f_finv nodeI).
  split; last by rewrite diskN_E inE /= qz2.
  move: qz2; rewrite -[q]cat_cons mem_cat => /orP[q2z2 | p3z2]; last first.
    by rewrite diskN_E !inE p3_p ?orbT.
  have Uq2p: ~~ has (mem (fband xp)) q2.
    have: ~~ has (mem (fband q2)) p1 by rewrite Dp has_cat negb_or Up2q.
    apply: contra => /hasP[t q2t /(@hasP _ _ xp)[u pu uFt]].
    move: pu; rewrite inE => /predU1P[Du | pu].
      apply/hasP; exists enx; first by rewrite mem_rcons mem_head.
      by apply/hasP; exists t; rewrite // cface1 nodeK -Du cfaceC.
    apply/hasP; exists u; first by rewrite mem_rcons mem_behead.
    by apply/hasP; exists t; last by rewrite cfaceC.
  case/andP: URq Uq2p; rewrite /q /= rcons_cat /q3.
  case/splitPl: q2z2 => q4 q5 <-; rewrite -catA cat_path has_cat.
  case/andP=> enxRq4 _ _ /norP[Uq4p _] {q5}.
  elim: q4 (enx) enxRq4 dNenx Uq4p => //= v q4 IHq u.
  rewrite {1}/rlink cface1 => /andP[fuRv vRq4] dNu /norP[xpF'x xpF'q4].
  suffices: v \in diskF xp by case/andP=> _ /IHq->.
  rewrite -(closed_connect (diskF_face xp) fuRv) inE /=.
  rewrite (closed_connect (fbandF xp) fuRv) xpF'x.
  by rewrite (fclosed1 (diskN_node xp)) edgeK dNu.
elim: r {z2}z1 => [|z2 r IHr] z1 [dNz1 dNq_z1] //= /andP[] /andP[q'z1 z1Cz2].
apply: {r}IHr; rewrite !(fclosed1 (diskN_node _) z2).
case/clinkP: z1Cz2 => <- //; rewrite -(canRL edgeK (e2c _)).
rewrite !diskN_E !in_simpl /= -!(fclosed1 (diskE_edge _ _)) // !in_simpl /=.
rewrite {}dNz1 dNq_z1 q'z1 orbT andbT orbC; split=> //.
have {1}->: xp = belast x p1 by rewrite belast_rcons.
rewrite Dp belast_cat /= -cat_rcons -lastI {q'z1}(contra _ q'z1) //.
rewrite -[q]cat_cons !mem_cat => /orP[xp2z1 | ->]; last exact: orbT.
have Uqp2: ~~ has (mem (fband q)) p2.
  apply/hasP=> [] [t p2t /(@hasP _ _ q)[u qu tFu]].
  have:= qu; rewrite -(mem_rot 1) rot1_cons rcons_cat -Lp3 -lastI mem_cat.
  case/orP=> [q2u | p3u].
    by case/hasP: Up2q; exists t; last by apply/hasP; exists u.
  have:= Up1; rewrite Dp simple_cat => /and3P[_ /hasP[]].
  by exists u; last by apply/hasP; exists t; rewrite 1?cfaceC.
case/negP: dNq'x; have:= xRp1; rewrite Dp cat_path => /andP[xRp2 _].
case/splitPl: xp2z1 xRp2 Uqp2 dNq_z1 => p4 p5 <- {z1}.
rewrite cat_path has_cat => /andP[xRp4 _] /norP[qF'p4 _] {p5}.
elim/last_ind: p4 xRp4 qF'p4 => // r z IHr.
rewrite last_rcons rcons_path has_rcons {2}/rlink /= cface1.
case/andP=> xRp ferFz /norP[qF'z qF'r] dNq_z.
have: z \in diskF q by apply/andP.
rewrite -(closed_connect (diskF_face q) ferFz) => /andP[_] /=.
by rewrite (fclosed1 (diskN_node q)) edgeK; apply: IHr.
Qed.

Let cface_ac_h x y : x \in ac -> cface x y -> cface (h x) (h y).
Proof.
move=> ac_x /connectP[p xFp ->] {y}.
elim: p x ac_x xFp => //= y p IHp x ac_x /andP[/eqP Dy yFp].
by rewrite cface1 -hF //= Dy IHp // -Dy -fclosed1.
Qed.

Let cface_h_ac x u :
  x \in ac -> cface (h x) u -> exists2 y, cface x y & h y = u.
Proof.
move=> ac_x /connectP[p xFp ->] {u}.
elim: p x ac_x xFp => [|y p IHp] x ac_x /=; first by exists x.
rewrite -hF // => /andP[/eqP <-{y} /IHp[|z xFz <-]]; first by rewrite -fclosed1.
by exists z; first by rewrite cface1.
Qed.

Let hFn := preembedding_arity embed_h.

Lemma cface_inj_embed x y : x \in ac -> cface x y -> h x = h y -> x = y.
Proof.
move=> ac_x xFy eq_hxy.
have iter_hF n: h (iter n face x) = iter n face (h x).
  by elim: n (x) ac_x => // n IHn z ac_z; rewrite !iterSr -hF ?IHn -?fclosed1.
have eq_iFxy: findex face (h x) (h y) = findex face x y.
  by rewrite -{1}(iter_findex xFy) iter_hF findex_iter // hFn // findex_max.
by rewrite -(iter_findex xFy) -eq_iFxy eq_hxy findex0.
Qed.

Definition pre_hom_ring x p :=
  [/\ path rlink x p, {subset x :: p <= ac} & scycle rlink (map h (x :: p))].

Lemma intro_pre_hom_ring x p :
    path rlink x p -> rlink (h (last x p)) (h x) ->
    {subset x :: p <= ac} -> simple (map h (x :: p)) -> 
  pre_hom_ring x p.
Proof.
move=> xRp Lhp p_ac Uhp; split=> //; rewrite /scycle {}Uhp andbT.
rewrite /= rcons_path last_map {}Lhp andbT.
move/allP: p_ac; elim: p x xRp => //= y p IHp x /andP[xRy yRp] /andP[ac_x p_ac].
have ac_ex: edge x \in ac by rewrite (closed_connect acF xRy); case/andP: p_ac.
by rewrite IHp // /rlink -embed_functor ?cface_ac_h.
Qed.

Lemma trivial_hom_ring x p :
    pre_hom_ring x p ->
  fcard face (diskF (map h (x :: p))) <= 0 -> rlink (last x p) x.
Proof.
rewrite leqNgt => xHRp /(fcard0P (diskF_face _))/existsP/pred0P pF_0.
elim: {p}_.+1 x {-2}p (ltnSn (size p)) pF_0 xHRp => // n IHn x p.
rewrite ltnS; set xp := x :: p => le_p_n pF_0 [xRp p_ac URhp].
set y := last x p; have xp_y: y \in xp := mem_last x p.
have xp_hy: h y \in map h xp := map_f h xp_y.
have ac_y: ac y := p_ac y xp_y.
have xpFnhy: node (h y) \in fband (map h xp).
  apply: contraFT (pF_0 (node (h y))); rewrite !inE => ->.
  by rewrite -(fclosed1 (diskN_node _)) diskN_E inE /= xp_hy.
have:= xpFnhy; rewrite unfold_in has_map => /hasP[z xpz] /=.
rewrite cfaceC => zFnhy.
have p_hz: h z \in map h xp by apply: map_f.
case/splitPl Dp: p / (xpz) => [p1 p2 Lp1].
case/lastP: p2 Dp => [|p2 y1] Dp.
  by rewrite /y Dp cats0 Lp1 -{1}[h z]nodeK -cface1 cfaceC bridge'Gm in zFnhy.
have Dy1: y1 = y by rewrite /y Dp last_cat last_rcons.
case/lastP: p1 => [|p1 z1] /= in Lp1 Dp.
  case/andP: URhp; rewrite /= Dp map_rcons !rcons_path last_rcons => /andP[_].
  rewrite Lp1 (rlinkFr zFnhy) Dy1 -[node (h y)]nodeK.
  by rewrite /rlink -cface1r cface1 (canRL nodeK (n3m _)) bridge'Gm.
rewrite last_rcons in Lp1; rewrite {z1}Lp1 {y1}Dy1 in Dp.
pose eny := edge (node y).
have ac_eny: eny \in ac by rewrite (fclosed1 acF) nodeK.
have h_eny: h eny = edge (node (h y)) by rewrite -[y]nodeK hF ?faceK.
have enyRz: rlink eny z.
  case p_hny: (node (h y) \in map h xp).
    case/mapP: p_hny => [t xpt Dht].
    case/splitPl Dp3: p / (xpt) => [p3 p4 Lp3].
    have Dp4: p4 = [:: y].
      case: p4 => [|t1 [|t2 p4]] in Dp3 *.
      - rewrite cats0 in Dp3; rewrite -Dp3 -/y in Lp3.
        by have /idP[] := bridge'Gm (h t); rewrite -{2}Dht cface1r nodeK Lp3.
      - by rewrite /y Dp3 last_cat.
      case/andP: URhp; rewrite /= Dp3 map_cat rcons_cat -cat_cons cat_path.
      rewrite last_map Lp3 simple_cat /= => /and3P[_ htRt1 _] /and3P[_ _].
      rewrite simple_cons -map_cons unfold_in => /andP[/hasP[]].
      exists (h y); first by rewrite map_f // /y Dp3 last_cat /= mem_last.
      by rewrite -(same_cface htRt1) -Dht cface1 nodeK.
    have Dt: t = node y.
      move: xRp; rewrite Dp3 cat_path Lp3 Dp4 => /and3P[_ tRy _].
      have ac_et: edge t \in ac by rewrite (closed_connect acF tRy).
      apply/edgeI/cface_inj_embed=> //; first by rewrite cface1r nodeK.
      by rewrite embed_functor -?Dht // p_ac.
    case: p2 Dp (congr1 (last x \o belast x) Dp) => [|z1 p2] Dp.
      rewrite Dp3 Dp4 /= !belast_cat !last_cat /= last_rcons Lp3 => <-.
      by rewrite /rlink e2c Dt.
    rewrite Dp3 Dp4 /= !belast_cat /= Lp3 !last_cat /= belast_rcons /= => Lp2.
    case/andP: URhp => _; rewrite Dp (lastI z1) -Lp2 cat_rcons -cat_cons.
    rewrite map_cat !map_cons simple_cat !simple_cons => /and4P[_ _].
    by rewrite unfold_in !map_rcons !has_rcons orbCA -Dht zFnhy. 
  pose q := rcons p2 eny.
  have henyFy: cface (h eny) (h y) by rewrite cface1 h_eny nodeK.
  have zHRq: pre_hom_ring z q.
    apply: intro_pre_hom_ring => [||t|].
    - move: xRp; rewrite Dp cat_path last_rcons => /andP[_].
      by rewrite !rcons_path {4}/rlink cface1r nodeK.
    - by rewrite /rlink last_rcons cfaceC (same_cface zFnhy) h_eny e2m.
    - rewrite -rcons_cons mem_rcons inE => /predU1P[-> // | p2t].
      by rewrite p_ac // Dp cat_rcons -rcons_cons -cats1 inE !mem_cat p2t !orbT.
    rewrite -{q}rcons_cons map_rcons simple_rcons.
    rewrite (closed_connect (fbandF _) henyFy) -simple_rcons.
    case/andP: URhp => _; rewrite Dp cat_rcons -cat_cons -rcons_cons.
    by rewrite map_cat -map_rcons simple_cat => /and3P[].
  rewrite -(last_rcons z p2 eny) -/q IHn // => [|u].
    apply: leq_trans le_p_n; rewrite Dp size_cat !size_rcons.
    by rewrite addSnnS leq_addl.
  have hxpFeny: h eny \in fband (map h xp) by apply/hasP; exists (h y).
  have Ehzq: chord_ring (map h xp) (h eny) = map h (rotr 1 (z :: q)).
    rewrite -rcons_cons rotr1_rcons !map_cons; congr (_ :: _).
    have <-: h y = fproj (map h xp) (h eny).
      have [xpj] := fprojP hxpFeny.
      by rewrite (same_cface henyFy); apply: (scycle_cface URhp).
    rewrite h_eny e2m.
    have <-: h z = fproj (map h xp) (node (h y)).
      have [xpj] := fprojP xpFnhy.
      by rewrite -(same_cface zFnhy); apply: (scycle_cface URhp).
    case/andP: URhp => _ /simple_uniq.
    rewrite -map_cons -/xp -(rotrK 1 xp) map_rot rot_uniq => Up.
    rewrite arc_rot //; last by apply map_f; rewrite mem_rotr.
    move: Up; rewrite /xp Dp -cat_cons -rcons_cat rotr1_rcons -rcons_cons.
    by rewrite cat_rcons map_cons map_cat !map_cons; apply: right_arc.
  rewrite -[z :: q](rotrK 1) map_rot /= diskF_rot -Ehzq.
  rewrite diskF_chord_ring // ?h_eny ?e2m //; first by rewrite inE pF_0 andbF.
    by rewrite /xp Dp (headI p2); case: (p1) => [|? []].
  rewrite -(fclosed1 (diskE_edge _ _)) // inE /= p_hny -map_cons -/xp.
  by rewrite -(fclosed1 (diskN_node _)) diskN_E inE /= xp_hy.
have ac_ny: node y \in ac.
  by rewrite -[node y]e2c (closed_connect acF enyRz) p_ac.
have h_ny: h (node y) = node (h y).
  by apply edgeI; rewrite -h_eny -embed_functor.
pose enny := edge (node (node y)).
have ac_enny: enny \in ac by rewrite (fclosed1 acF) nodeK.
have h_enny: h enny = edge (node (node (h y))).
  by rewrite -h_ny -[node y]nodeK (hF ac_enny) faceK.
have hyRx: rlink (h y) (h x).
  by case/andP: URhp; rewrite /= rcons_path last_map => /andP[_].
have ennyRx: rlink enny x.
   have [|p'nnhy] := boolP (node (node (h y)) \in map h xp).
    case/mapP=> t xpt Dht; case/splitPl Dp4: p / xpt => [p3 p4 Lp3].
    have Dp3: p3 = [::].
      case: p3 => //= t1 p3 in Dp4 Lp3 *; case/andP: URhp => _.
      rewrite /rlink -[h y]n3m cface1 nodeK Dht in hyRx.
      rewrite map_cons simple_cons {1}Dp4 -cat_cons lastI Lp3 cat_rcons.
      by rewrite map_cat fband_cat /= fband_cons cfaceC hyRx !orbT.
    rewrite -{}Lp3 {p3 p4 Dp4}Dp3 /= in Dht.
    have Dp1: p1 = [::]; last rewrite {p1}Dp1 /= in Dp.
      case: p1 Dp => // x1 p1 Dp.
      case/andP: URhp; rewrite Dp /= => /andP[hxRx1 _].
      rewrite !simple_cons cat_rcons map_cat fband_cat /= => /and3P[_ /negP[]].
      rewrite orbC fband_cons -(same_cface hxRx1) cfaceC -Dht cface1r nodeK.
      by rewrite zFnhy.
    suffices Dx: x = node (node y) by rewrite /rlink e2c -Dx.
    move: xRp; rewrite Dp /= => /andP[xRz _].
    have ac_ex: edge x \in ac by rewrite (closed_connect acF xRz) p_ac.
    rewrite /rlink e2c -[node y]nodeK -/enny -cface1 in enyRz.
    rewrite cfaceC -(same_cface xRz) in enyRz; apply/edgeI/cface_inj_embed=> //.
    by rewrite (embed_functor (p_ac _ (mem_head _ _)) ac_ex) -Dht.
  pose q := rcons p1 enny.
  have hennyFz: cface (h enny) (h z) by rewrite cface1 h_enny nodeK cfaceC.
  have xHRq: pre_hom_ring x q.
    apply: intro_pre_hom_ring => [||t|].
    - move: xRp; rewrite Dp cat_path andbC => /andP[_].
      by rewrite !rcons_path -(rlinkFr enyRz) e2c {4}/rlink cface1r nodeK.
    - by rewrite last_rcons h_enny /rlink e2m (canRL nodeK (n3m _)) -cface1.
    - rewrite -rcons_cons mem_rcons inE => /predU1P[-> //|p1t].
      by rewrite p_ac // Dp cat_rcons -cat_cons mem_cat p1t.
    rewrite {}/q -rcons_cons map_rcons simple_rcons.
    rewrite (closed_connect (fbandF _) hennyFz) -simple_rcons.
    case/andP: URhp => _; rewrite -map_rcons Dp -cat_cons map_cat.
    by rewrite simple_cat => /and3P[].
  rewrite -(last_rcons x p1 enny) -/q IHn // => [|u].
    apply: leq_trans le_p_n; rewrite Dp size_cat !size_rcons.
    by rewrite -addSnnS leq_addr.
  have xpFhenny: h enny \in fband (map h xp) by apply/hasP; exists (h z).
  rewrite /rlink -[h y]n3m cface1 nodeK in hyRx.
  have xpFnnhy: node (node (h y)) \in fband (map h xp).
    by apply/hasP; exists (h x); first apply: mem_head.
  have Ehzq: chord_ring (map h xp) (h enny) = map h (rotr 1 (x :: q)).
    rewrite /q -rcons_cons rotr1_rcons map_cons; congr (_ :: _).
    have <-: h z = fproj (map h xp) (h enny).
    have [xpj] := fprojP xpFhenny.
      by rewrite (same_cface hennyFz); apply: (scycle_cface URhp).
    have <-: h x = fproj (map h xp) (edge (h enny)).
      have [xpj] := fprojP xpFnnhy.
      rewrite (same_cface hyRx) h_enny e2m; apply: (scycle_cface URhp) => //.
      exact: mem_head.
    case/andP: URhp => _ /simple_uniq.
    by rewrite /xp Dp cat_rcons map_cons map_cat !map_cons; apply: left_arc.
  rewrite -[x :: q](rotrK 1) map_rot /= diskF_rot -Ehzq.
  rewrite diskF_chord_ring // ?h_enny ?e2m //.
  - by rewrite inE /= [X in _ && X]pF_0 andbF.
  - by rewrite /xp Dp (headI p2); case: (p1) => [|x1 []].
  rewrite -(fclosed1 (diskE_edge _ _)) // inE /= p'nnhy.
  by rewrite -!(fclosed1 (diskN_node _)) diskN_E inE /= xp_hy.
by rewrite /rlink e2c (canRL nodeK (n3c _)) -?cface1 // [~~ _]ac_bc in ennyRx.
Qed.

Let rcN : fclosed node rc.
Proof.
apply: (intro_closed cnodeC) => x _ /eqP <- rc_x.
by rewrite -(fconnect_cycle cycNrc rc_x) fconnect1.
Qed.

Lemma edge_perimeter x : (x \in bc) || (edge x \in bc).
Proof.
rewrite -negb_and; apply/andP => [] [/= rc_x rc_ex].
have fxx: face x = x.
  apply: (scycle_cface UNrc) => //; last by rewrite cfaceC fconnect1.
  by rewrite (fclosed1 rcN) -(canRL edgeK (e2c x)).
have cycFx: fcycle face [:: x] by rewrite /= fxx eqxx.
have /idPn[] := allP (embeddable_ring embedGc) _ rc_x.
by rewrite /good_ring_arity (order_cycle cycFx) // mem_head.
Qed.

Notation erc := (map edge rc).

Let Drrrc : rev_ring rrc = erc.
Proof. by rewrite /rev_ring /rrc map_rev revK. Qed.

Let URrrc : scycle rlink rrc.
Proof.
rewrite /rrc /scycle simple_rev UrcF andbT.
case: rc cycNrc => [|x p] //=; rewrite (cycle_path x) rev_cons last_rcons.
elim: p {1 4}x => /= [|_ p IHp] y /andP[/eqP <- nyRp].
  by rewrite andbT /rlink cface1 nodeK.
by rewrite rcons_path rev_cons last_rcons IHp //= /rlink cface1 nodeK.
Qed.

Let URerc : scycle rlink erc.
Proof. by rewrite -Drrrc; apply: scycle_rev_ring. Qed.

Lemma chordless_perimeter x :
   x \in bc -> edge x \in bc -> (x \in ac) || (edge x \in ac).
Proof.
have EercF: fband erc =i fband rc.
  move=> y; rewrite -Drrrc fband_rev_ring //.
  by apply: eq_has_r => z; rewrite mem_rev.
move=> bc_x bc_ex; have [cycRerc /simple_uniq Uerc] := andP URerc.
rewrite -negb_and; apply/andP=> [] [rcFx rcFex].
have erc_ok: proper_ring erc.
  move: rcFx cycRerc (edge_perimeter (head x rc)).
  case: (rc) => [|x1 [|x2 []]] //= _; first by rewrite /rlink cfaceC bridge'Gc.
  by rewrite !inE eqxx (inj_eq edgeI) => _ /norP[_].
move: x bc_x bc_ex rcFx rcFex.
have rrc_ok: proper_ring rrc by rewrite -(proper_rev_ring geoGc) Drrrc.
have nt_dFerc x:
    x \in fband erc -> edge x \in fband erc -> x \in diskE erc ->
  exists y, y \in diskF (chord_ring erc x).
- move=> ercFx ercFex dEx; set rx := chord_ring erc x.
  have URrx: scycle rlink rx by apply: scycle_chord_ring.
  have rx_ok: proper_ring rx by apply: proper_chord_ring.
  have rx_erc: {subset behead rx <= erc}.
    have [[erc_jx xFj] [erc_jex exFj]] := (fprojP ercFx, fprojP ercFex).
    have [|i p1 _ Dp1 ->] := rot_to_arc Uerc erc_jex erc_jx.
      apply: contraTneq exFj => ->; rewrite cfaceC -(same_cface xFj).
      by rewrite bridge'Gc.
    rewrite -cat_cons {p1}Dp1 => Derc y rx_y.
    by rewrite -(mem_rot i) Derc mem_cat rx_y.
  have{ercFx ercFex dEx} dN_bc: {subset diskN rx <= bc}.
    move=> y; rewrite diskN_chord_ring // => /andP[_ /=].
    by rewrite -Drrrc diskN_rev_ring ?inE //= diskN_E inE /= mem_rev => /norP[].
  move: URrx rx_ok rx_erc dN_bc.
  elim: {x rx}_.+1 {-2}rx (ltnSn (size rx)) => // n IHn p; rewrite ltnS => lepn.
  move=> URp p_ok p_erc dN_bc; apply/existsP/pred0P => dF_0.
  have [cycRp /simple_uniq Up] := andP URp.
  case Dp: p (p_ok) => [|x p1] // _.
  have px: x \in p by rewrite Dp mem_head.
  have dNx: x \in diskN p by rewrite diskN_E !inE px.
  have bcx: x \in bc := dN_bc x dNx.
  have [[pF_F dN_N] dE_E] := (fbandF p, diskN_node p, diskE_edge planarGc URp).
  pose efex := edge (face (edge x)); pose enx := edge (node x).
  have f_efex: face efex = node x by rewrite /efex -{1}(n3c bcx) !nodeK.
  have [dEefex|] := boolP (efex \in diskE p).
    have pFefex: efex \in fband p.
      apply: contraFT (dF_0 (node x)); rewrite (fclosed1 pF_F) f_efex /=.
      by rewrite inE /= -(fclosed1 dN_N) => ->.
    have pFeefex: edge efex \in fband p.
      apply/hasP; exists (next p x); first by rewrite mem_next.
      by rewrite e2c -cface1; apply: next_cycle cycRp px.
    pose y := fproj p efex.
    have p1y: y \in p1.
      have [] := fprojP pFefex; rewrite -/y Dp inE => /predU1P[] // ->.
      by rewrite -{1}[x]nodeK -cface1r cface1 f_efex bridge'Gc.
    case/splitPr Dp1: p1 / p1y => [p2 p3].
    have Dp2: efex :: p2 = chord_ring p efex.
      congr (_ :: _); rewrite -/y e2c /arc; set z := fproj p (face (edge x)).
      have ->: index z p = 1.
        have[]:= fprojP pFeefex; rewrite e2c -/z -cface1 cfaceC {2}Dp /= => pz.
        case: eqP => [<- | _ zFex]; first by rewrite bridge'Gc.
        move: cycRp; rewrite Dp; case: (p1) Dp => [|z1 p5] //= Dp /andP[xRz1 _].
        rewrite -[z1](scycle_cface URp pz) ?eqxx ?(same_cface zFex) //.
        by rewrite Dp !inE eqxx orbT.
      rewrite Dp rot1_cons Dp1 rcons_cat index_cat /= eqxx addn0.
      rewrite [y \in p2](contraTF _ Up) ?take_size_cat //.
      by rewrite Dp /= Dp1 cat_uniq /= => ->; rewrite !andbF.
    have{IHn} [|||z p2z|z|z] := IHn (efex :: p2).
    + by apply: leq_trans lepn; rewrite Dp Dp1 /= size_cat /= addnS leq_addr.
    + by rewrite Dp2; apply scycle_chord_ring.
    + by rewrite Dp2; apply proper_chord_ring.
    + by rewrite p_erc // Dp Dp1 /= mem_cat p2z.
    + by rewrite Dp2 diskN_chord_ring // => /andP[_]; apply: dN_bc.
    by rewrite Dp2 diskF_chord_ring // inE /= [X in _ && X]dF_0 andbF.
  rewrite -(fclosed1 dE_E) inE /= (fclosed1 dN_N) edgeK dNx andbT negbK => pfex.
  case: p1 => [|fex p2] in Dp; first by rewrite Dp in p_ok.
  have Dfex: fex = face (edge x).
    apply: (scycle_cface URp) => //; first by rewrite Dp !inE eqxx orbT.
    by have:= cycRp; rewrite Dp /= /rlink cface1 cfaceC => /andP[].
  have pFenx: enx \in fband p.
    by rewrite (fclosed1 pF_F) nodeK; apply: subsetP (ring_fband _) _ px.
  have pFeenx: edge enx \in fband p.
    apply/hasP; exists (next p fex); first by rewrite mem_next Dfex.
    by rewrite e2c -f_efex -cface1 Dfex; apply: next_cycle cycRp pfex.
  have dEenx: enx \in diskE p.
    rewrite -(fclosed1 dE_E) inE /= -(fclosed1 dN_N) dNx andbT Dp /= inE.
    have [_ /negPf->/=] := cubicP cubicGc x bcx.
    have rc_efex: efex \in rc.
      by rewrite -(mem_map edgeI) e2c -Dfex p_erc // Dp mem_head.
    have: 2 < arity efex < 7.
      by rewrite -mem_iota !inE [_ || _](allP (embeddable_ring embedGc)).
    rewrite ltnNge andbC /arity => /andP[_]; apply: contra => pnx.
    rewrite (eq_card (fconnect_cycle _ (mem_head _ [:: node x]))) ?card_size //.
    have fnxFefex: cface (face (node x)) efex by rewrite -f_efex -!cface1.
    rewrite /= f_efex eqxx andbT; apply/eqP/(scycle_cface UNrc)=> //.
    by rewrite (fclosed1 rcN) -(mem_map edgeI) faceK p_erc ?Dp.
  have Dp2: enx :: p2 = chord_ring p enx.
    congr (_ :: _); apply/esym.
    have <-: x = fproj p enx.
      have [pj enxFj] := fprojP pFenx; apply: (scycle_cface URp) => //.
      by rewrite -{1}[x]nodeK -cface1.
    have: cface (node x) (head x p2).
      by move: cycRp; rewrite -f_efex -cface1 Dp /= headI Dfex => /and3P[].
    case: p2 Dp => [|z p3] Dp /= => [|nxFz].
      by rewrite -{2}[x]nodeK -cface1r bridge'Gc.
    have <-: z = fproj p (edge enx).
      have [pj] := fprojP pFeenx; rewrite {1}e2c (same_cface nxFz).
      by apply: (scycle_cface URp); rewrite // Dp !inE eqxx !orbT.
    by move: Up; rewrite Dp -(cat1s fex); apply: right_arc.
  have{IHn} [|||z /= p2z|z|z] := IHn (enx :: p2).
  - by apply: leq_trans lepn; rewrite Dp.
  - by rewrite Dp2; apply: scycle_chord_ring.
  - by rewrite Dp2; apply: proper_chord_ring.
  - by rewrite p_erc // Dp mem_behead.
  - by rewrite Dp2 diskN_chord_ring // => /andP[_ /dN_bc].
  by rewrite Dp2 diskF_chord_ring // inE /= [X in _ && X]dF_0 andbF.
have dFerc_ac x:
    x \in fband erc -> edge x \in fband erc -> x \in diskE erc ->
  diskF (chord_ring erc x) =i ac.
- move=> ercFx ercFex dEx; set rx := chord_ring erc x.
  have dF_ac: {subset diskF rx <= ac}.
    by move=> y; rewrite diskF_chord_ring // !inE EercF => /and3P[].
  have URrx: scycle rlink rx by apply: scycle_chord_ring.
  have dN_dF: {in ac, {subset diskN rx <= diskF rx}}.
    move=> y; rewrite !inE /= -EercF.
    by rewrite -(fband_chord_ring _ _ ercFx) // -/rx => /norP[-> _].
  move=> z; apply/idP/idP=> [|ac_z]; first exact: dF_ac.
  have [y dFy] := nt_dFerc x ercFx ercFex dEx; rewrite -/rx in dFy.
  have ac_eey: edge (edge y) \in ac by rewrite e2c dF_ac.
  have [p [eyRp Lp nt_p] [_ p_hac]] := h_spoke ac_eey ac_z.
  have{p_hac}: all (mem ac) p by move: p_hac; rewrite all_predI => /andP[].
  case: p nt_p Lp eyRp => //= [y1 p] _ Lp /andP[eyRy1 y1Rp] /andP[_].
  have{eyRy1} dFy1: y1 \in diskF rx.
    by rewrite -(closed_connect (diskF_face rx) eyRy1) e2c.
  rewrite -{Lp}(closed_connect (diskF_face rx) Lp).
  elim: p y1 dFy1 y1Rp => //= y2 p IHp y1 dFy1 /andP[y1Ry2 y2Rp] /andP[ac_y2].
  apply: {p}IHp y2Rp; rewrite /rlink cface1 in y1Ry2.
  rewrite -(closed_connect (diskF_face rx) y1Ry2) dN_dF //.
    by rewrite inE /= (closed_connect (fbandF rc) y1Ry2).
  by rewrite (fclosed1 (diskN_node rx)) edgeK; case/andP: dFy1.
move=> x bc_x bc_ex; rewrite /= -!EercF => ercFx ercFex.
have dEex: edge x \in diskE erc.
  rewrite inE /= (mem_map edgeI) [~~ _]bc_x -Drrrc diskN_rev_ring //= !inE.
  apply: contra bc_ex => /hasP[y rrc_y /connectP[]].
  rewrite mem_rev -{1}(f_finv nodeI y) -(fclosed1 rcN) in rrc_y.
  by case=> [|z p] => [_ -> | ] //=; rewrite {1}/dlink /= mem_rev rrc_y.
have [||y dFy] := nt_dFerc _ ercFex; rewrite ?e2c //.
have ac_y: y \in ac by rewrite dFerc_ac ?e2c in dFy.
have /idPn[]:= dFy; rewrite diskF_chord_ring ?e2c // inE /= dFerc_ac ?ac_y //.
by rewrite (fclosed1 (diskE_edge planarGc URerc)).
Qed.

Lemma fcard_adj_perimeter x :
  x \notin ac -> #|predI (cface x) [preim edge of fband rc]| = 2.
Proof.
case/negbNE/hasP=> y rc_y xFy.
rewrite (cardD1 y) (cardD1 (edge (node y))) !inE xFy cface1r nodeK xFy e2c.
have rc_ny: node y \in rc by rewrite -(fclosed1 rcN).
case: eqP => [eny_y | _].
  by have/norP[]:= edge_perimeter (node y); rewrite eny_y !negbK.
have rcFey: edge y \in fband rc.
  apply/hasP; exists (face (edge y)); last exact: fconnect1.
  by rewrite (fclosed1 rcN) edgeK.
rewrite rcFey (subsetP (ring_fband _)) //=; apply/eqP/existsP=> [[z]].
case/and4P=> eny'z y'z; rewrite {x xFy}(same_cface xFy) => yFz /= rcFez.
have bc_z: z \in bc by apply: contra y'z => /(scycle_cface UNrc rc_y)->.
have bc_ez: edge z \in bc.
  apply: contra eny'z => /= rc_ez; apply/eqP/(scycle_cface URerc).
  - by rewrite -[z]e2c map_f.
  - exact: map_f.
  by rewrite cfaceC cface1 nodeK.
have/norP[]:= chordless_perimeter bc_z bc_ez.
by rewrite !negbK; split=> //; apply/hasP; exists y; rewrite // cfaceC.
Qed.

Lemma adj_kernel_min x : x \notin ac -> exists2 y, y \in ac & cface x (edge y).
Proof.
case/negbNE/hasP=> y rc_y xFy; have:= allP (embeddable_ring embedGc) _ rc_y.
rewrite -[_ y]mem_seq4 (mem_iota 3 4) andbC => /andP[_].
rewrite /order -(cardID [preim edge of fband rc]).
rewrite fcard_adj_perimeter ?(contraL (@ac_bc _)) // !ltnS lt0n.
by case/exists_inP=> z; exists (edge z); rewrite // e2c (same_cface xFy).
Qed.

Lemma adj_kernel_max x :
  x \notin ac -> #|predI (cface x) [preim edge of ac]| <= 4.
Proof.
case/negbNE/hasP=> y rc_y xFy; have:= allP (embeddable_ring embedGc) _ rc_y.
rewrite -[_ y]mem_seq4 (mem_iota 3 4) => /andP[_].
rewrite /order -(cardID [preim edge of fband rc]).
rewrite fcard_adj_perimeter ?(contraL (@ac_bc _)) //.
by congr (_ <= 4); apply: eq_card => z; rewrite !inE (same_cface xFy) andbC.
Qed.

Lemma embed_full : {in ac &, forall x1 x2, edge (h x1) = h x2 -> edge x1 = x2}.
Proof.
suffices IHf5: ~ exists x1, exists2 p,
   [/\ path rlink x1 p, last x1 p != x1 & {subset p <= ac}]
     & edge (h (last x1 p)) = h (edge x1) /\ size p <= 5.
- move=> x1 x2 ac_x1 ac_x2 /= ehx1; apply/eqP/idPn=> x2'ex1; case: IHf5.
  have /radius2P[x0 ac_x0 ac_x0rad2] := embeddable_kernel embedGc.
  have /(at_radius2P acF)[x01 [x10 [x0Fx01 x1Fx10]]] := ac_x0rad2 x1 ac_x1.
  have /(at_radius2P acF)[x02 [x20 [x0Fx02 x2Fx20]]] := ac_x0rad2 x2 ac_x2.
  move=> [ac_ex02 ex02Fex20] [ac_ex01 ex01Fex10].
  exists (edge x1), [:: x10; edge x01; x02; edge x20; x2]; last first.
    by split; rewrite //= e2c -ehx1 e2m.
  rewrite eq_sym; split=> //=.
    rewrite /rlink !e2c x1Fx10 cfaceC ex01Fex10 -(same_cface x0Fx01) x0Fx02.
    by rewrite ex02Fex20 cfaceC x2Fx20.
  apply/allP; rewrite /= ac_ex01 ac_x2 -(closed_connect acF x1Fx10) ac_x1.
  rewrite -(closed_connect acF x0Fx02) ac_x0.
  by rewrite  -(closed_connect acF ex02Fex20) ac_ex02.
suffices IHf5: ~ exists x, exists2 p,
    pre_hom_ring x p /\ ~~ rlink (last x p) x & size p <= 4.
- move=> [x0 [p [x0Rp Lp p_ac] [Lhp ple5]]].
  suffices{Lp Lhp}: exists2 q,
      [/\ path rlink x0 q, last x0 q = last x0 p & {subset q <= ac}]
    & simple (map h q) /\ size q <= size p.
  + case=> [[|x q] [x0Rq Lq q_ac] [Uq leqp]].
      by rewrite -Lq /= eqxx in Lp.
    case: IHf5; exists x, q; last exact: leq_trans leqp ple5.
    have ac_x: x \in ac by rewrite q_ac ?mem_head.
    have{x0Rq Lq} /=[/andP[x0Rx xRq] Lq] := (x0Rq, Lq); split.
      apply: intro_pre_hom_ring; rewrite // Lq /rlink Lhp cfaceC.
      by rewrite cface_ac_h // cfaceC.
    apply: contra Lp => qRx0; apply/eqP/edgeI.
    have ac_eLp: edge (last x0 p) \in ac.
      by rewrite -Lq (closed_connect acF qRx0).
    apply: cface_inj_embed => //.
      by rewrite -Lq (same_cface qRx0) cfaceC.
    by rewrite embed_functor // -Lq q_ac ?mem_last.
  elim: p x0 x0Rp p_ac ple5 => [|x1 p IHp] x0 /=; first by exists [::].
  case/andP=> [x0Rx1 x1Rp] /allP/=/andP[ac_x1 /allP p_ac] ple5.
  have{IHp x1Rp} [q [x1Rq Lq q_ac] [Uq leqp]] := IHp _ x1Rp p_ac (ltnW ple5).
  have [| qF'x1] := boolP (h x1 \in fband (map h q)); last first.
    exists (x1 :: q); split=> //; first by rewrite /= x0Rx1.
      by apply/allP; rewrite /= ac_x1; apply/allP.
    by rewrite map_cons simple_cons qF'x1.
  rewrite unfold_in has_map => /hasP[x2 q_x2]; rewrite /= cfaceC => hx2Fx1.
  have ac_x2: x2 \in ac := q_ac _ q_x2.
  have [x3 x2Fx3 eq_hx13] := cface_h_ac ac_x2 hx2Fx1.
  have ac_x3: x3 \in ac by rewrite -(closed_connect acF x2Fx3).
  case/splitP: {q}q_x2 x1Rq Lq leqp Uq q_ac => [q1 q2].
  rewrite cat_path last_cat last_rcons cat_rcons size_cat /=.
  case/andP=> x1Rq1 x2Rq2 Lq2 leqp Uq q_ac.
  have [eq_x13 | x3'1] := eqVneq x1 x3.
    exists (x2 :: q2); split=> //.
    + by rewrite /= {1}/rlink (same_cface x0Rx1) eq_x13 cfaceC x2Fx3.
    + by move=> z q2z; rewrite q_ac // mem_cat q2z orbT.
    + by move: Uq; rewrite map_cat simple_cat => /and3P[_ _].
    by rewrite (leqW (leq_trans _ leqp)) ?leq_addl.
  case: q1 => [|x q] in leqp Uq q_ac x1Rq1.
    have [x1Rx2 _] := andP x1Rq1.
    have ac_ex1: edge x1 \in ac by rewrite (closed_connect acF x1Rx2).
    have:= cface_ac_h ac_ex1 x1Rx2.
    by rewrite cfaceC embed_functor // (same_cface hx2Fx1) bridge'Gm.
  case: IHf5; exists x, (rcons q x3); last first.
    by rewrite size_rcons (leq_trans _ (leq_trans leqp ple5)) ?leq_addr.
  have ac_x: x \in ac := q_ac x (mem_head _ _).
  move: x1Rq1; rewrite /= rcons_path => /andP[x1Rx xRq].
  have ac_ex1: edge x1 \in ac by rewrite (closed_connect acF x1Rx).
  rewrite last_rcons; split; last first.
    apply: contra x3'1; rewrite -(rlinkFr x1Rx) /rlink cfaceC => ex3Rex1.
    apply/eqP/edgeI/(cface_inj_embed ac_ex1 ex3Rex1).
    by rewrite !embed_functor ?eq_hx13 // -(closed_connect acF ex3Rex1).
  apply: intro_pre_hom_ring => //.
  + by rewrite rcons_path -(rlinkFr x2Fx3).
  + by rewrite last_rcons eq_hx13 /rlink -embed_functor // cface_ac_h.
  + move=> y; rewrite -rcons_cons mem_rcons inE => /predU1P[-> // | qy].
    by rewrite q_ac // mem_cat qy.
  move: Uq; rewrite -rcons_cons -cat_rcons map_cat simple_cat !map_rcons.
  rewrite -!rot1_cons !simple_rot 2!simple_cons andbC => /andP[_].
  by congr (_ && _); rewrite (closed_connect (fbandF _) hx2Fx1) eq_hx13.
suffices IHf5: ~ exists x, exists2 p,
         pre_hom_ring x p /\ ~~ rlink (last x p) x
       & fcard face (diskF (map h (x :: p))) <= (size (x :: p) == 5).
- case=> x [p xHRp lep5]; set xp := x :: p.
  have hp_ok: proper_ring (map h xp).
    rewrite {}/xp; case: p xHRp {lep5} => [|y [|y1 p1]] //= [] [].
      by rewrite /scycle /= /rlink cfaceC bridge'Gm.
    case/andP=> xRy _ /allP/=/and3P[ac_x ac_y _] _; apply: contraNneq => ehx.
    have ac_ex: edge x \in ac by rewrite (closed_connect acF xRy).
    rewrite -embed_functor // in ehx.
    by rewrite -(cface_inj_embed ac_ex xRy ehx) /rlink e2c.
  case: (IHf5); exists x, p => //.
  rewrite /= -(size_map h) eqSS leqNgt; apply/negP => nt_dF.
  have{xHRp} [[xRp p_ac URhp] Lp] := xHRp.
  have hxFehp: cface (h x) (edge (h (last x p))).
    by have[] := andP URhp; rewrite /= rcons_path last_map cfaceC => /andP[].
  have ac_x: x \in ac := p_ac x (mem_head x _).
  case/lastP Dp: p => [|p1 y]; first by rewrite Dp /= bridge'Gm in hxFehp.
  have Dy: y = last x p by rewrite Dp last_rcons.
  have ac_y: y \in ac by rewrite Dy p_ac ?mem_last.
  have [ry xFry hry] := cface_h_ac ac_x hxFehp.
  pose rp := rcons (rev (map edge (belast x p1))) ry.
  pose rx := edge (last x p1); pose rxp := rx :: rp.
  have Ehrp: map h rxp = rot 1 (rev_ring (map h xp)).
    rewrite /xp lastI /rev_ring !map_rcons rev_rcons rot1_cons -hry.
    rewrite Dp belast_rcons {}/rxp {}/rx {}/rp -rcons_cons.
    rewrite -rev_rcons -map_rcons -lastI map_rcons map_rev -!map_comp.
    congr (rcons (rev _) _); apply/eq_in_map => z pz.
    move/allP: p_ac xRp; rewrite {}Dp; case/splitPl: pz => p2 p3 Lp2.
    rewrite rcons_cat -cat_cons cat_path headI lastI Lp2 cat_rcons all_cat.
    set z1 := head y p3 => /and4P[_ ac_z ac_z1 _] /and3P[_ zRz1 _].
    by rewrite /= embed_functor // (closed_connect acF zRz1).
  case: IHf5; exists rx, rp.
    split; last first.
      move: xRp; rewrite Dp rcons_path => /andP[_ p1Ry].
      rewrite last_rcons (rlinkFr p1Ry); apply: contra Lp => ryRy.
      have ac_ry: ry \in ac by rewrite -(closed_connect acF xFry).
      have ac_ery: edge ry \in ac by rewrite (closed_connect acF ryRy).
      have:= canLR e2m hry; rewrite -Dy -embed_functor // => Dhy.
      by rewrite -(cface_inj_embed _ _ Dhy) // /rlink e2c cfaceC.
    split=> [|z|]; last 1 first.
    + by rewrite Ehrp rot_scycle; apply: scycle_rev_ring.
    + move: xFry xRp; rewrite cfaceC {rxp Ehrp}/rx {}/rp {hry}Dp.
      elim: p1 ry (x) => [|x3 p1 IHp] x1 x2 /= x1Fx2 /andP[x2Rx3 x3Rp].
        by rewrite /rlink e2c cfaceC x1Fx2.
      by rewrite rev_cons rcons_path last_rcons IHp // /rlink e2c cfaceC.
    rewrite -rcons_cons mem_rcons -rev_rcons inE /= mem_rev -map_rcons -lastI.
    rewrite -{2}[z]e2c (mem_map edgeI) => /predU1P[->|p1ez].
      by rewrite -(closed_connect acF xFry).
    move/allP: p_ac xRp; rewrite {}Dp; case/splitPl: p1ez => [p2 p3 Lp2].
    rewrite rcons_cat cat_path Lp2 headI /= all_cat /= /rlink e2c.
    by case/and4P=> _ _ ac_x3 _ /and3P[_ /(closed_connect acF)-> _].
  have EhrpF: diskF (map h rxp) =i diskF (rev_ring (map h xp)).
    by move=> z; rewrite Ehrp diskF_rot.
  have <-: size (map h xp) = size rxp.
    by rewrite size_map /= Dp !size_rcons size_rev size_map size_belast.
  rewrite (eq_n_comp_r EhrpF) (eq_n_comp_r (diskF_rev_ring cexGm URhp hp_ok)).
  apply: contraFT (Birkhoff cexGm _ URhp); last by rewrite size_map.
  by rewrite -ltnNge => nt_dFC; apply/andP.
case=> x [p [xHRp Lp] triv_dF]; have [] := negP Lp.
apply: trivial_hom_ring => //.
do [move Dxp: (x :: p) => xp; case: eqP => // sz_xp_5] in triv_dF *.
set hxp := map h xp; rewrite leqn0; apply/exists_inP=> [[u /= Du dFu]].
have{xHRp} [xRp p_ac URhxp] := xHRp; rewrite Dxp -/hxp in p_ac URhxp.
have{Du dFu triv_dF} DdF v: (v \in diskF hxp) = cface u v.
  have dFcF := closed_connect (diskF_face hxp).
  apply/idP/idP=> [dFv | /dFcF <- //]; apply/(rootP cfaceC)/esym/eqP.
  move: triv_dF; rewrite [fcard _ _](cardD1 u) inE /= Du dFu ltnS leqn0.
  move/pred0P/(_ (froot face v)); rewrite /= inE /= (roots_root cfaceC) /=.
  by rewrite -(dFcF _ _ (connect_root _ _)) (eqP Du) dFv andbT => /negbFE.
pose ru := spoke_ring u; pose frf := froots (@face Gm).
have{frf} DxpF: fband hxp =i fband ru.
  have ruF_xpF: [predI frf & fband ru] \subset [predI frf & fband hxp].
    apply/subsetP=> v1 /andP/=[Dv1 /hasP[v ru_v v1Fv]].
    rewrite inE /= (closed_connect (fbandF hxp) v1Fv) {v1 v1Fv}Dv1 /=.
    have{ru_v} uFnv: cface u (node v) by rewrite -mem_spoke_ring.
    have dNnv: node v \in diskN hxp by move: uFnv; rewrite -DdF => /andP[].
    have: v \notin diskF hxp.
      by rewrite DdF (same_cface uFnv) -{2}[v]nodeK -cface1r bridge'Gm.
    by rewrite inE /=; apply: contraR => ->; rewrite (fclosed1 (diskN_node _)).
  have EpFr: fcard face (fband ru) = fcard face (fband hxp).
    apply/eqP; rewrite eqn_leq subset_leq_card //.
    rewrite (scycle_fcard_fband URhxp) size_map sz_xp_5.
    rewrite (@scycle_fcard_fband Gm rlink); last exact: scycle_spoke_ring.
    by rewrite size_spoke_ring pentaGm.
  move=> v; have:= subset_cardP EpFr ruF_xpF (froot face v).
  rewrite !inE (roots_root cfaceC) /=.
  by rewrite -!(closed_connect (fbandF _) (connect_root _ v)).
have hxp_ru: {subset hxp <= ru}.
  move=> v hxp_v; have [cycRhxp _] := andP URhxp.
  have uAv: adj u v.
    by rewrite -fband_spoke_ring -DxpF (subsetP (ring_fband _)).
  have uAev: adj u (edge v).
    rewrite (adjFr (next_cycle cycRhxp hxp_v)) -fband_spoke_ring -DxpF.
    by rewrite (subsetP (ring_fband _)) ?mem_next.
  have /orP[//|] := adj11_edge cexGm uAv uAev.
  rewrite mem_spoke_ring -DdF => /andP[_] /=.
  rewrite -(fclosed1 (diskN_node _)) diskN_edge_ring //.
  by rewrite /hxp -(mkseq_nth x xp) sz_xp_5.
have: fcycle (face \o face \o edge) hxp.
  have [[cycRhxp UhxpF] URu] := (andP URhxp, scycle_spoke_ring cexGm u).
  apply cycle_from_next=> [|v hxp_v]; first exact: simple_uniq.
  apply/eqP/(scycle_cface URu); first 2 [by rewrite hxp_ru ?mem_next].
    by rewrite /= -(next_spoke_ring cexGm (hxp_ru v hxp_v)) mem_next hxp_ru.
  by rewrite -!cface1; apply: next_cycle cycRhxp hxp_v.
rewrite /hxp -Dxp /= rcons_path last_map => /andP/=[hxFFEhp /eqP Lhp].
have nxp_nxF: map node xp \subset cface (node x).
  rewrite subset_all -Dxp /= inE connect0 /=.
  move/allP: p_ac xRp hxFFEhp; rewrite -Dxp /=.
  elim: (p) (x) => //= x2 r IHr x1 => /andP[ac_x1 r_ac] /andP[x1Rx2 x2Rp].
  case/andP=> /eqP/esym Dhx2 hx2FFEhr; have [ac_x2 _] := andP r_ac.
  suffices{r IHr r_ac x2Rp hx2FFEhr} nx1Fnx2: cface (node x1) (node x2).
    by rewrite inE nx1Fnx2 (eq_all (same_cface nx1Fnx2)) IHr.
  have ac_ex1: edge x1 \in ac by rewrite (closed_connect acF x1Rx2).
  rewrite -embed_functor // -!hF -?(fclosed1 acF) // in Dhx2.
  have: cface x2 (face (face (edge x1))) by rewrite cfaceC -!cface1.
  move/cface_inj_embed->; rewrite // -(canRL edgeK (e2c _)) cface1r.
  by rewrite -{2}(n3c (ac_bc ac_x1)) !nodeK.
have ac'nx: (node x \notin ac).
  apply: contra Lp => ac_nx; set y := last x p in Lhp *; rewrite -Dxp in p_ac.
  have ac_x: x \in ac := p_ac x (mem_head x p).
  have ac_enx: edge (node x) \in ac by rewrite (fclosed1 acF) nodeK.
  have ac_y: y \in ac := p_ac y (mem_last x p).
  have ac_eny: edge (node y) \in ac by rewrite (fclosed1 acF) nodeK.
  have nxFny: cface (node x) (node y).
    by apply: (subsetP nxp_nxF); rewrite map_f // -Dxp mem_last.
  have ac_ny: node y \in ac by rewrite -(closed_connect acF nxFny).
  have hny: h (node y) = h (face (node x)).
    rewrite hF // -[h (node x)]edgeK -embed_functor // -hF // nodeK -Lhp.
    rewrite -[h y]n3m -(canRL edgeK (e2m _)) !nodeK.
    by rewrite -{2}[y]nodeK hF // embed_functor // edgeK.
  have nyFfnx: cface (node y) (face (node x)) by rewrite cfaceC -cface1.
  have bc_y: y \in bc := ac_bc ac_y.
  rewrite /rlink -(n3c bc_y) 2!cface1 nodeK -[node (node y)]e2c.
  by rewrite (cface_inj_embed ac_ny nyFfnx) // faceK nodeK.
have nxp_ace: map node xp \subset [predI cface (node x) & [preim edge of ac]].
  apply/subsetP=> y nxp_y; rewrite inE /= (subsetP nxp_nxF) //= inE /=.
  by have{y nxp_y} [z xp_z ->] := mapP nxp_y; rewrite (fclosed1 acF) nodeK p_ac.
have:= leq_trans (subset_leq_card nxp_ace) (adj_kernel_max ac'nx).
suffices /card_uniqP->: uniq (map node xp) by rewrite size_map sz_xp_5.
by rewrite (map_inj_uniq nodeI); have [_ /simple_uniq/map_uniq] := andP URhxp.
Qed.

Lemma pre_embed_inj : {in ac &, injective h}.
Proof.
move=> x y ac_x ac_y /= Dhx; have ac_eex: edge (edge x) \in ac by rewrite e2c.
have [[|z1 [|z2 p]] [//=/andP[xFz1 z1Rp] Lp _] [_ p_ac]] := h_spoke ac_eex ac_y.
  by apply: cface_inj_embed; rewrite // -[x]e2c (same_cface xFz1).
have [z1Rz2 _] := andP z1Rp; rewrite /rlink e2c in xFz1.
have [/andP[ac_z1 /eqP hez1] /andP[ac_z2 _] _] := and3P p_ac.
have hxFhz1 := cface_ac_h ac_x xFz1; rewrite Dhx in hxFhz1.
have [t yFt Dht] := cface_h_ac ac_y hxFhz1.
have ac_t: t \in ac by rewrite -(closed_connect acF yFt).
have ac_ez1: edge z1 \in ac by rewrite (closed_connect acF z1Rz2).
apply: cface_inj_embed; rewrite // (same_cface xFz1) cfaceC.
by rewrite -(edgeI (embed_full ac_t ac_ez1 _)) // Dht.
Qed.

Definition embed x :=
  if x \in ac then h x else
  if edge x \in ac then edge (h (edge x)) else
  if node x \in ac then face (edge (h (node x))) else
  edge (node (node (h (node (edge x))))).

Notation h1 := embed.

Lemma embed_cases x :
  (x \in ac \/ edge x \in ac) \/ node x \in ac \/ node (edge x) \in ac.
Proof.
suffices{x} in_bc x: bc x -> (x \in ac \/ edge x \in ac) \/ node x \in ac.
  by case/orP: (edge_perimeter x) => /in_bc; rewrite ?e2c; tauto.
move=> bc_x; have [rc_ex | bc_ex] := boolP (edge x \in rc); last first.
  by case: (orP (chordless_perimeter bc_x bc_ex)); tauto.
have [rc_enx | bc_enx] := boolP (edge (node x) \in rc); last first.
  rewrite inE /= (fclosed1 rcN) in bc_x.
  case: (orP (chordless_perimeter bc_x bc_enx)); first tauto.
  by rewrite (fclosed1 acF) nodeK; tauto.
have rc_fx: face x \in rc by rewrite (fclosed1 rcN) -(canRL edgeK (e2c x)).
have Dfx: face x = edge (node x).
  by rewrite (scycle_cface UNrc rc_fx rc_enx) // -cface1 cface1r nodeK.
have EfxF: cface (face x) =i [:: x; face x].
  by apply: fconnect_cycle; rewrite ?inE /= ?Dfx ?nodeK !eqxx ?orbT.
have:= allP (embeddable_ring embedGc) _ rc_fx.
rewrite -[good_ring_arity _]mem_seq4 (mem_iota 3 4).
by rewrite /order (eq_card EfxF) ltnNge card_size.
Qed.

Lemma embedE : {morph h1 : x / edge x}.
Proof.
move=> x; wlog bc_x: x / x \in bc.
  move=> IH; case: (orP (edge_perimeter x)) => /IH //.
  by rewrite e2c => ->; rewrite e2m.
rewrite /h1 e2c; do 2!case: ifPn; rewrite ?e2m //; first exact: embed_functor.
move=> ac'x ac'ex; have [/orP/norP[]//|/orP] := embed_cases x.
case: ifPn => [ac_nex _ | ac'nex]; last first.
  by rewrite orbF (canRL nodeK (n3m _)) => ->.
have bc_ex: edge x \in bc by rewrite inE /= (fclosed1 rcN); apply: ac_bc.
by have /norP[] := chordless_perimeter bc_x bc_ex.
Qed.

Lemma embedN : {in bc, {morph h1 : x / node x}}.
Proof.
move=> x bc_x; rewrite /h1 (fclosed1 acF (edge (node x))) nodeK.
rewrite (canRL nodeK (n3c bc_x)) -(fclosed1 acF).
have [ac_x | ac'x] := boolP (x \in ac).
  have ac_enx: edge (node x) \in ac by rewrite (fclosed1 acF) nodeK.
  apply: edgeI; rewrite -[x as x in h x]nodeK (hF ac_enx) faceK fun_if e2m.
  by case: ifP => // ac_nx; rewrite embed_functor.
have [ac_ex | ac'ex] := boolP (edge x \in ac).
  case: ifPn => [ac_nx | ac'nx]; last first.
    by rewrite -(canRL nodeK (n3m _)) hF // (canRL edgeK (e2m _)).
  rewrite (canRL edgeK (e2m _)) -hF // -(canRL nodeK (n3c bc_x)).
  have ac_ennx: edge (node (node x)) \in ac by rewrite (fclosed1 acF) nodeK.
  rewrite (canRL nodeK (n3m _)) -embed_functor -?hF ?nodeK //.
  by rewrite (canRL nodeK (n3c bc_x)) -fclosed1.
case: (embed_cases x) => /orP; first by case/norP.
rewrite (fun_if node) edgeK; case: ifP => //= _ ac_nex.
have bc_ex: edge x \in bc by rewrite inE /= (fclosed1 rcN); apply: ac_bc.
by have /norP[] := chordless_perimeter bc_x bc_ex.
Qed.

Lemma embed_inj : {in bc &, injective h1}.
Proof.
have bc_acN x: bc x -> x \notin ac -> edge x \notin ac -> node x \in ac.
  move=> bc_x ac'x ac'ex; case: (embed_cases x) => [/orP/norP|] [] // ac_enx.
  have bc_ex: edge x \in bc by rewrite inE /= (fclosed1 rcN) [~~ _]ac_bc.
  by have /norP[] := chordless_perimeter bc_x bc_ex.
move=> x y; without loss ac_x: x y / x \in ac.
  move=> IH bc_x bc_y eq_hxy.
  have [ac_x | ac'x] := boolP (x \in ac); first exact: IH.
  have [ac_y | ac'y] := boolP (y \in ac); first exact/esym/IH.
  have [ac_nx | ac'nx] := boolP (node x \in ac).
    by apply/nodeI/IH; rewrite ?embedN ?eq_hxy // inE /= -(fclosed1 rcN).
  have [ac_ny | ac'ny] := boolP (node y \in ac).
    by apply/nodeI/esym/IH; rewrite ?embedN ?eq_hxy // inE /= -(fclosed1 rcN).
  by apply/edgeI/IH; rewrite ?embedE ?eq_hxy ?ac_bc ?(contraR (bc_acN _ _ _)).
move=> bc_x bc_y; rewrite /h1 ac_x.
have [|ac'y] := ifPn; first exact: pre_embed_inj.
have [ac_ey | ac'ey] := ifPn; first by move/esym/embed_full <-; rewrite ?e2c.
have ac_ny: node y \in ac by apply: bc_acN.
have ac_enx: edge (node x) \in ac by rewrite (fclosed1 acF) nodeK.
rewrite bc_acN // -{1}[x]nodeK hF // => /faceI h_enx.
exact/esym/nodeI/edgeI/embed_full.
Qed. 

Local Notation ddart := {x | x \in bc}.

Definition embd_edge x :=
  if edge x \in bc then edge x else edge (node (edge x)).

Fact embd_edge_subproof (u : ddart) : embd_edge (sval u) \in bc.
Proof.
rewrite /embd_edge; case: ifPn => // bc'eu.
have:= edge_perimeter (node (edge (val u))).
by rewrite inE /= -(fclosed1 rcN) -implyNb bc'eu. 
Qed.

Fact embd_node_subproof (u : ddart): node (sval u) \in bc.
Proof. by rewrite inE /= -(fclosed1 rcN) [~~ _](valP u). Qed.

Definition embd_face x := if face x \in bc then face x else face (face x).

Fact embd_face_subproof (u : ddart) : embd_face (sval u) \in bc.
Proof.
rewrite /embd_face; case: ifP (edge_perimeter (face (val u))) => //= _.
by rewrite inE /= (canRL edgeK (e2c _)) -(fclosed1 rcN).
Qed.

Let dedge u : ddart := Sub (embd_edge (val u)) (embd_edge_subproof u).
Let dnode u : ddart := Sub (node (val u)) (embd_node_subproof u).
Let dface u : ddart := Sub (embd_face (val u)) (embd_face_subproof u).

Fact embed_disk_subproof : cancel3 dedge dnode dface.
Proof.
move=> u; apply: val_inj; rewrite /= /embd_edge.
case: ifP => [bc_ex | bc'ex]; last by rewrite /embd_face nodeK bc'ex edgeK.
by rewrite /embd_face inE /= (fclosed1 rcN) edgeK [~~ _](valP u) edgeK.
Qed.

Definition embed_disk := Hypermap embed_disk_subproof.
Local Notation Gd := embed_disk.
Definition embd (u : Gd) := sval u.

Lemma embd_inj : injective embd. Proof. exact: val_inj. Qed.

Lemma codom_embd : codom embd =i bc.
Proof.
move=> x; apply/imageP/idP => [[u _ ->] | bc_x]; first exact: (valP u).
by exists (Sub x bc_x).
Qed.

Definition embd_ring : seq Gd := preim_seq embd erc.

Lemma map_embd_ring : map embd embd_ring = erc.
Proof.
apply: map_preim => _ /mapP[x rc_x ->]; rewrite codom_embd.
by have:= edge_perimeter x; rewrite inE /= rc_x.
Qed.

Lemma cface_embd : {mono embd : u v / cface u v}.
Proof.
move=> u v; apply/idP/idP=> /connectP[p]; last first.
  move=> uFp -> {v}; elim: p u uFp => //= v p IHp u /andP[Dv /IHp].
  apply: connect_trans; rewrite -(eqP Dv) /embd /= /embd_face.
  by case: ifP => _; rewrite -!cface1r.
elim: {p}_.+1 u {-2}p (ltnSn (size p)) => // n IHn u [|y p] lepn.
  by move=> _ Dv; apply/eq_connect0/embd_inj.
rewrite cface1 /= => /andP[/eqP Dy yFp] Lp.
have{IHn}:= IHn (face u); rewrite /= /embd_face Dy.
have [bc_y | bc'y] := ifP; first by move/(_ p)->.
case: p => [|z p] /= in yFp Lp lepn *; first by rewrite -Lp (valP v) in bc'y.
by case/andP: yFp => /eqP-> zFp; move/(_ p) => -> //; apply: ltnW.
Qed.

Lemma scycle_embd_ring : sfcycle edge embd_ring.
Proof.
have UbGdF: simple embd_ring.
  move: (scycle_simple URerc); rewrite -map_embd_ring.
  elim: embd_ring => //= u q IHq; rewrite !simple_cons !unfold_in has_map.
  by rewrite (eq_has (cface_embd u)) => /andP[->].
rewrite /scycle UbGdF andbT; have [UbGd Iemb] := (simple_uniq UbGdF, embd_inj).
apply: cycle_from_next => //= u; rewrite -(mem_map Iemb) -(inj_eq Iemb).
rewrite -next_map // map_embd_ring /embd /= /embd_edge => /mapP[x rc_x ->{u}].
by rewrite e2c inE /= rc_x (next_map edgeI) //= (eqP (next_cycle cycNrc rc_x)).
Qed.

Let bGdE : fclosed edge embd_ring.
Proof.
apply: (intro_closed cedgeC) => u _ /(edge u =P _) <- bGd_u.
have [cycEbGd _] := andP scycle_embd_ring.
by rewrite -(fconnect_cycle cycEbGd bGd_u) fconnect1.
Qed.
Let bGd'E := predC_closed bGdE.

Definition embdd u := h1 (embd u).

Lemma embdd_inj : injective embdd.
Proof. by move=> u v /(embed_inj (valP u) (valP v))/embd_inj. Qed.

Lemma embddE : {in [predC embd_ring], {morph embdd: u / edge u}}.
Proof.
move=> u; rewrite inE /= -(mem_map embd_inj) map_embd_ring -embedE.

by rewrite -{1}[embd u]e2c (mem_map edgeI) /embdd /= /embd_edge inE /= => ->.
Qed.

Lemma embddN : {morph embdd: u / node u}.
Proof. by move=> u; rewrite /embdd /= (embedN (valP u)). Qed.

Let rdom' := image embdd [predC embd_ring].
Local Notation rdart := {x | x \notin rdom'}.

Fact embr_edge_subproof (w : rdart) : edge (sval w) \notin rdom'.
Proof.
apply: contra (valP w) => /= /imageP[u bGd'u /(canRL e2m)->{w}].
by rewrite -embddE // image_f // -(fclosed1 bGd'E).
Qed.

Let bGd_proj x := [pred u in embd_ring | x == embdd u].

Definition embr_node x :=
  oapp (embdd \o node \o face) (node x) (pick (bGd_proj x)).

Fact embr_node_subproof (w : rdart) : embr_node (val w) \notin rdom'.
Proof.
rewrite /embr_node; have [u /andP[bGd_u /eqP Dw] | bGd'w] := pickP.
  by rewrite Dw /= (mem_image embdd_inj) (fclosed1 bGd'E) faceK negbK.
apply/imageP=> [] [u /= bGd'u ndw]; have /andP[] := bGd'w (node (node u)).
have Dw: val w = embdd (node (node u)) by rewrite !embddN -ndw n3m.
by rewrite [_ \in _](contraR _ (valP w)) ?Dw // (mem_image embdd_inj).
Qed.

Definition embr_face x :=
  oapp (embdd \o edge) (face x) (pick (bGd_proj (edge x))).

Fact embr_face_subproof (w : rdart) : embr_face (val w) \notin rdom'.
Proof.
rewrite /embr_face; have [u /andP[bGd_u /eqP/(canRL e2m) Dw] | bGd'ew] := pickP.
  by rewrite Dw /= (mem_image embdd_inj) -(fclosed1 bGd'E) negbK.
apply/imageP=> [] [u /= bGd'u fdw]; have /andP[] := bGd'ew (node u).
have Dew: edge (val w) = embdd (node u).
  by rewrite (canRL edgeK (e2m _)) fdw embddN.
rewrite [_ \in _](contraR _ (embr_edge_subproof w)) ?Dew //.
by rewrite (mem_image embdd_inj).
Qed.

Let redge w : rdart := Sub (edge (val w)) (embr_edge_subproof w).
Let rnode w : rdart := Sub (embr_node (val w)) (embr_node_subproof w).
Let rface w : rdart := Sub (embr_face (val w)) (embr_face_subproof w).

Fact embed_rem_subproof : cancel3 redge rnode rface.
Proof.
move=> w; apply: val_inj; rewrite /= /embr_face e2m.
have [u /andP[bGd_u /eqP->] | bGd'w] := pickP; rewrite /embr_node.
  have [_ /andP[_ /eqP/embdd_inj <-] | /(_ (edge u))] /= := pickP.
    by rewrite [dnode _](edgeK u).
  by rewrite -(fclosed1 bGdE) bGd_u eqxx.
have [u /andP[bGd_u /eqP/= Dfew] | _] /= := pickP; last exact: edgeK.
have /negP[]:= valP w; rewrite -[val w]edgeK Dfew -embddN image_f //.
by apply: contraFN (bGd'w (node u)) => /= -> /=; rewrite embddN -Dfew edgeK.
Qed.

Definition embed_rem := Hypermap embed_rem_subproof.
Local Notation Gr := embed_rem.
Definition embr (u : Gr) := val u.

Lemma embr_inj : injective embr. Proof. exact: val_inj. Qed.

Lemma codom_embr : codom embr =i [predC rdom'].
Proof.
move=> x; apply/imageP/idP=> [[w _ ->] | bG'x]; first exact: (valP w).
by exists (Sub x bG'x).
Qed.

Definition embr_ring : seq Gr := preim_seq embr (rev (map embdd embd_ring)).

Lemma map_embr_ring : map embr embr_ring = rev (map embdd embd_ring).
Proof.
apply: map_preim => x; rewrite codom_embr mem_rev => /mapP[u bGd_u ->{x}].
by rewrite inE /= (mem_image embdd_inj) negbK.
Qed.

Lemma ucycle_embr_ring : ufcycle node embr_ring.
Proof.
have [[cycEbGd /simple_uniq UbGd] Iembr] := (andP scycle_embd_ring, embr_inj).
have UbGm: uniq (map embdd embd_ring) by rewrite (map_inj_uniq embdd_inj).
have UbGr: uniq embr_ring.
  by rewrite -(map_inj_uniq Iembr) map_embr_ring rev_uniq.
rewrite /ucycle UbGr andbT; apply: cycle_from_next => //= w.
rewrite -(inj_eq Iembr) -next_map // -(mem_map Iembr) map_embr_ring mem_rev.
rewrite next_rev /embr //= /embr_node => /mapP[u bGd_u ->].
rewrite (prev_map embdd_inj) // eq_sym.
have [_ /andP[_ /eqP/embdd_inj <-] | /(_ u)/andP[]//] := pickP.
by rewrite (inj_eq embdd_inj) -(canF_eq edgeK) [_ == _](prev_cycle cycEbGd).
Qed.

Lemma embed_patch : patch embdd embr embd_ring embr_ring.
Proof.
split.
- exact: embdd_inj.
- exact: embr_inj.
- exact: scycle_embd_ring.
- exact: ucycle_embr_ring.
- exact: map_embr_ring.
- move=> x; rewrite codom_embr !inE.
  apply/imageP/norP=> [[u bGd_u ->] | [/negbNE/imageP[u _ ->]]].
    by rewrite codom_f // (mem_map embdd_inj).
  by rewrite (mem_map embdd_inj); exists u.
- exact: embddE.
- exact: embddN.
- by [].
move=> w; rewrite inE /= -(mem_map embr_inj) map_embr_ring /embr /= /embr_node.
by case: pickP => //= u /andP[bGd_u /eqP->]; rewrite mem_rev map_f.
Qed.
Local Notation ppGm := embed_patch.

Lemma planar_embr : planar Gr.
Proof.
by have:= planarGm; rewrite /planar (genus_patch ppGm) addn_eq0 => /andP[].
Qed.

Lemma plain_embr : plain Gr.
Proof. by have:= plainGm; rewrite (plain_patch ppGm) => /andP[]. Qed.

Lemma cubic_embr : quasicubic embr_ring.
Proof. by have: cubic Gm := cexGm; rewrite (cubic_patch ppGm) => /andP[]. Qed.

Notation ccr := (map h1 cc).

Let mapEh1 p : insertE (map h1 p) = map h1 (insertE p).
Proof. by elim: p => //= x p ->; rewrite embedE. Qed.

Let ccE x : x \in insertE cc -> edge x \in insertE cc.
Proof. by rewrite !mem_insertE // (eq_has (cedge1 x)). Qed.

Lemma embed_sparse : sparse (insertE ccr).
Proof.
move: Cred_cc => [[rc'cc UccN _ _] _]; move: rc'cc UccN.
rewrite disjoint_has has_sym /sparse !simple_recI mapEh1 /=.
elim: (insertE cc) => //= x p IHp /norP[rc'x rc'p] /andP[pN'x /IHp-> {IHp}//].
rewrite unfold_in has_map {pN'x}(contra _ pN'x) // => /hasP[z p_z /= h1xNz].
apply/hasP; exists z => //; have{p_z} rc'z := hasPn rc'p z p_z.
case/connectP: h1xNz => q; elim: q => /= [|y q IHq] in x rc'x *.
  by move=> _ /embed_inj->.
case/andP=> /eqP <-; rewrite -(embedN rc'x) cnode1; apply: IHq.
by rewrite -(fclosed1 rcN).
Qed.

Let cface_ac_h1 : {in ac, {mono h1 : x y / cface x y}}.
Proof.
move=> x ac_x /= y; without loss bc_y: y / y \in bc.
  move=> IH; have /orP[] := edge_perimeter y; first exact: IH.
  rewrite -{1 2}[y]faceK e2c inE /= -(fclosed1 rcN) => rc'fy.
  by rewrite embedE embedN // cface1r nodeK IH // -cface1r.
have{y bc_y} /imageP[v _ ->]: y \in codom embd by rewrite codom_embd.
have /imageP[u _ Dx]: x \in codom embd by rewrite codom_embd ac_bc.
rewrite Dx cface_embd (patch_face_d ppGm) //; apply/exists_inP=> [[z]] /=.
rewrite inE codom_embr /embdd -Dx /h1 ac_x => /cface_h_ac[//|x1 xFx1 <-].
have ac_x1: x1 \in ac by rewrite -(closed_connect acF xFx1).
have /imageP[u1 _ Dx1]: x1 \in codom embd by rewrite codom_embd ac_bc.
case/imageP; exists u1; last by rewrite /embdd /h1 -Dx1 ac_x1.
rewrite inE /= -(mem_map embd_inj) -Dx1 map_embd_ring -[x1]faceK.
by rewrite (mem_map edgeI) -(fclosed1 rcN) [~~ _]ac_bc // -(fclosed1 acF).
Qed.

Let cface_h1 : {homo h1 : x y / cface x y}.
Proof.
move=> x y; without loss bc_y: y / y \in bc.
  move=> IH; have /orP[] := edge_perimeter y; first exact: IH.
  rewrite -{1 3}[y]faceK e2c inE /= -(fclosed1 rcN) => rc'fy xFy.
  by rewrite embedE embedN // cface1r nodeK IH // -cface1r.
without loss bc_x: x / x \in bc.
  move=> IH; have /orP[] := edge_perimeter x; first exact: IH.
  rewrite -{1 3}[x]faceK e2c inE /= -(fclosed1 rcN) => rc'fy xFy.
  by rewrite embedE embedN // cface1 nodeK IH // -cface1.
rewrite -!codom_embd in bc_x bc_y; rewrite -(f_iinv bc_x) -(f_iinv bc_y).
by rewrite cface_embd; apply: (patch_face_d' ppGm).
Qed.

Let adj_ac_h1 : {in ac &, {mono h1 : x y / adj x y}}.
Proof.
have cl_aF := closed_connect acF.
move=> x y ac_x ac_y; rewrite /h1 ac_x ac_y.
apply/adjP/adjP=> [[_ /(cface_h_ac ac_x)[z xFz <-] ] | [z xFz zRy]].
  rewrite /rlink cfaceC => /(cface_h_ac ac_y)[t yFt /esym/embed_full Dez].
  by exists z; rewrite // cfaceC Dez // -(cl_aF x z, cl_aF y t).
have ac_z: z \in ac by rewrite -(cl_aF x).
have ac_ez: edge z \in ac by rewrite (cl_aF _ y).
by exists (h z); rewrite /rlink -?embed_functor // cface_ac_h.
Qed.

Let orbitF_h1 (x : Gc) : x \in ac -> orbit face (h1 x) = map h1 (orbit face x).
Proof.
move=> ac_x; rewrite /orbit -!/(arity _) {2}/h1 ac_x hFn //.
move: (arity x) => n; elim: n => //= n IHn in x ac_x *.
have ac_fx: face x \in ac by rewrite -(fclosed1 acF).
rewrite -IHn //; congr (_ :: traject _ _ n).
by rewrite -{1}[x]faceK embedE embedN ?ac_bc ?nodeK.
Qed.

Lemma embed_valid_contract : valid_contract [::] ccr.
Proof.
split; try exact: embed_sparse; rewrite ?disjoint_has // size_map ?mapEh1.
  by have [[]] := Cred_cc.
have [[rc'cc _ _ triad_cc] _] := Cred_cc; rewrite disjoint_has has_sym in rc'cc.
move=> {triad_cc}/triad_cc/existsP[x /= /and3P[ac_x adj3x xA'cc]].
apply/existsP; exists (h1 x); apply/and3P; split=> // [{xA'cc} | {adj3x}].
  apply: leq_trans adj3x _; rewrite orbitF_h1 // /orbit.
  move: (arity x) => n; elim: n => //= n IHn in x ac_x *.
  apply: leq_add; last by rewrite IHn -?(fclosed1 acF).
  rewrite -embedE /fband has_map; case: hasP => // [[y cc_y yFex]].
  by case: hasP => // [[]]; exists y => //=; apply: cface_h1.
apply: contra xA'cc => /subsetP ccAx; apply/subsetP=> y cc_y.
have cc_ey: edge y \in insertE cc by apply: ccE.
have{ccAx} ccAx z: z \in insertE cc -> adj (h1 x) (h1 z).
  by move=> cc_z; apply/ccAx/map_f.
have bc_ey: edge y \in bc by apply: (hasPn rc'cc).
have: cface x (node y) || cface x (node (edge y)).
  rewrite -!(cface_ac_h1 ac_x) (embedN (hasPn rc'cc _ cc_y)) embedN //.
  by rewrite embedE -!mem_spoke_ring adj11_edge -?embedE ?ccAx.
case/orP=> [xFny | xFney].
  by apply/adjP; exists (node y); rewrite // /rlink cface1 nodeK.
apply/adjP; exists (edge (face y)); last by rewrite /rlink e2c -cface1.
by rewrite -{1}[y]e2c -(n3c bc_ey) cface1r !nodeK.
Qed.

Definition embed_cotrace := ring_trace (rotr 1 embr_ring).

Lemma embed_closure : Kempe_closed embed_cotrace.
Proof.
apply: Kempe_map; split; [ split | exact: planar_embr ].
  split; first exact: plain_embr.
  by apply/subsetP=> w; rewrite inE /= mem_rotr; apply: (subsetP cubic_embr w).
by rewrite rotr_ucycle; apply: ucycle_embr_ring.
Qed.

Lemma embed_contract : exists2 et, cc_ring_trace cc rrc et & embed_cotrace et.
Proof.
have [[rc'cc _ _ _] _] := Cred_cc; rewrite disjoint_has has_sym in rc'cc.
have [k [kE kF]] := contract_coloring cexGm embed_valid_contract.
pose k1 := k \o h1; exists (trace (map k1 rrc)).
  exists k1; split.
    have k1Ebc x: x \in bc -> invariant edge k1 x = (x \in insertE cc).
      move=> bc_x; rewrite /k1 /= embedE [_ == _]kE mapEh1.
      apply/mapP/idP=> [[y c_y /embed_inj-> //]|]; last by exists x.
      exact: (hasPn rc'cc).
    move=> x; have /orP[|bc_ex] := edge_perimeter x; first exact: k1Ebc.
    rewrite mem_insertE // (eq_has (cedge1 x)) -mem_insertE // -k1Ebc //= e2c.
    by rewrite eq_sym.
  move=> x; rewrite /k1 /=.
  by rewrite -(fconnect_invariant kF (cface_h1 (fconnect1 face x))) eqxx.
exists (k \o embr).
  split=> w /=.
    rewrite [_ == _]kE mapEh1; apply: contraNF (valP w) => /mapP[x cc_x /= ->].
    have xdP: x \in codom embd by rewrite codom_embd; apply: (hasPn rc'cc).
    apply/imageP; exists (iinv xdP); rewrite /embdd ?f_iinv // inE /=.
    rewrite -(mem_map embd_inj) map_embd_ring f_iinv -[x]e2c (mem_map edgeI).
    by apply: (hasPn rc'cc); apply: ccE.
  by apply/eqP/(fconnect_invariant kF); rewrite -(patch_face_r ppGm) -cface1.
rewrite !map_rotr 2!map_comp map_embr_ring (map_comp h1 embd) map_embd_ring.
rewrite !map_rev -rev_rot; congr (trace (rev _)).
case: rc cycNrc => //= x p; rewrite rot1_cons.
elim: p {1 3}x => [|_ p IHp] y /= /andP[/eqP <- nyNp].
  congr [:: _]; apply/(fconnect_invariant kF)/cface_h1.
  by rewrite cface1r nodeK.
congr (_ :: _); last exact: IHp.
by apply/(fconnect_invariant kF)/cface_h1; rewrite cface1r nodeK.
Qed.

Theorem not_embed_reducible : False.
Proof.
have [et etGc etGr] := embed_contract.
have{et etGc etGr}:= C_reducible_coclosure Cred_cc etGc embed_closure etGr.
case=> et [kc [kcE kcF] Detc] [kr col_kr Detr].
apply: minimal_counter_example_is_noncolorable (cexGm) _.
have [_] := colorable_patch ppGm; apply; exists (rev et); last first.
  by rewrite revK Detr -trace_rot -!map_rot rotrK; exists kr.
exists (kc \o embd).
  split=> u.
    rewrite /= /embd_edge; case: ifP => _; first exact: kcE.
    by rewrite -(eqcP (kcF _)) nodeK; apply: kcE.
  by apply/eqP/(fconnect_invariant kcF); rewrite cface_embd -cface1.
rewrite map_comp map_embd_ring Detc map_rev trace_rev rev_rot revK.
suffices Drc: rc = map face (rot 1 erc).
  rewrite [in LHS]Drc -map_comp map_rot trace_rot rotK.
  by congr (trace _); apply: eq_map => x; apply/eqP/kcF.
case: rc UNrc => // x p /andP[/=xNpx _]; rewrite rot1_cons.
by elim: p {1 3}x xNpx => /= [|y p IHp] z /andP[/eqP/(canRL nodeK)-> // /IHp->].
Qed.

End Embeddings.
