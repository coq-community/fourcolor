(* (c) Copyright 2006-2015 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype path fingraph.
From fourcolor Require Import hypermap jordan geometry color chromogram.
From fourcolor Require Import coloring patch snip sew revsnip kempe.
From fourcolor Require Import ctree initctree gtree initgtree ctreerestrict.
From fourcolor Require Import gtreerestrict cfmap cfcolor kempetree.

(******************************************************************************)
(* The Birkhoff theorem, stating that a minimal coloring counter-example must *)
(* be internally 5-connected, along with some of its consequences: the        *)
(* minimum face arity must be 5, and cartwheels (the radius-2 submap about a  *)
(* central hub face) must be well-formed (in particular, the radius-1 spoke   *)
(* ring about the hub must be chordless).                                     *)
(* Defined here:                                                              *)
(*        cpcard cp == number of darts in cpmap cp.                           *)
(*  ctree_pick_rev t' t == a (complete) trace coloring et such that the       *)
(*                     corresponding even partial trace is in t' : ctree, and *)
(*                     the partial trace corresonding to rev et is in t;      *)
(*                     returns [::] if there is no such trace.                *)
(*  Birkhoff_check h m <-> all configurations with ring size h+1 and kernel   *)
(*                     size greater than m are locally reducible (reducible   *)
(*                     in a map with more than m other faces). The evidence   *)
(*                     for this is a 'basis' of cprog's for cubic, but not    *)
(*                     necessarily connected configurations with at most m    *)
(*                     kernel faces (condition Birkhoff_check1), and an       *)
(*                     iteration count n such that, starting with two full    *)
(*                     ctree/gtree pairs, repeating n times the process of    *)
(*                     removing via Kempe_tree_closure a common trace         *)
(*                     returned by ctree_pick_rev in either of the ctrees,    *)
(*                     yields a ctree that is disjoint from one of the basis  *)
(*                     coloring trees computed by cpcolor (condition          *)
(*                     Birkhoff_check2).                                      *)
(*   --> The Birkhoff check condition implies there are no m-nontrivial rings *)
(* in a minimal counter-example because the two configurations consisting of  *)
(* the inside and the outside of the ring should have disjoint coloring sets, *)
(* (else we could glue two ring-compatible colourings), closed under Kempe    *)
(* flips, and meeting the coloring sets of each of the basis configurations.  *)
(*  --> In Birkhoff_check2 we could pick a trace in the intersection of the   *)
(* ctrees rather than in the intersection with reversal, but then the         *)
(* correctness proof would no longer be symmetrical as we would have to       *)
(* mirror one of the configurations. Similarly, we recheck dynamically that   *)
(* the trace is proper rather than prove it at an awkward time.               *)
(*          spoke y == the dart on the first ring of faces surrounding a      *)
(*                     central 'hub' face, that corresponds to a dart y in    *)
(*                     that hub (= face (edge y)).                            *)
(*     spoke_ring x == the (contour) ring obtained by mapping spoke on the    *)
(*                     reverse face (F-cycle) at x; spoke_ring x is simple    *)
(*                     (hence a ring, in our terminology) and indeed          *)
(*                     chordless in an internally 4-connected hypermap, hence *)
(*                     in a minimal counter-example by the Birkhoff theorem.  *)
(*        adj01 x y == x and y either belong to the same or to adjacent faces *)
(*                     of thier hypermap.                                     *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section BirkhoffCheck.

Variable h m : nat.

Fixpoint cpcard (cp : cprog) :=
  match cp with
  | (CpR _ | CpA | CpR') :: cp' => cpcard cp'
  | (CpU | CpK) :: cp' => (cpcard cp').+2
  | CpY :: cp' => (cpcard cp').+4
  | CpH :: cp' => (cpcard cp').+4.+2
  | [::] => 2
  end.

Lemma card_cpmap cp : #|cpmap cp| = cpcard cp.
Proof. by elim: cp => [|[] cp //=]; rewrite ?card_ecp ?card_bool // => ->. Qed.

Definition Birkhoff_check1 cp :=
  [&& cubic_prog cp, (cpcard cp).+1 < 6 * m + 4 * h & cprsize cp == h.+1].

Fixpoint ctree_pick_rev_rec (et : colseq) e t' t {struct t} : colseq :=
  match t with
  | CtreeLeaf _ =>
    if ctree_mem t' (etrace (belast e et)) then e :: et else [::]
  | CtreeNode t1 t2 t3 =>
    if ctree_pick_rev_rec (Color1 :: et) (e +c Color1) t' t1 is e' :: et' then
      e' :: et' else
    if ctree_pick_rev_rec (Color2 :: et) (e +c Color2) t' t2 is e' :: et' then
      e' :: et' else
    ctree_pick_rev_rec (Color3 :: et) (e +c Color3) t' t3
  | _ => [::]
  end.

Definition ctree_pick_rev := ctree_pick_rev_rec [::] Color0.

Lemma sumt_ctree_pick_rev t t' : sumt (ctree_pick_rev t t') = Color0.
Proof.
rewrite /ctree_pick_rev; set cs0 := [::].
have: Color0 +c sumt cs0 = Color0 by [].
elim: t' cs0 {1 3}Color0 => // [t1 IHt1 t2 IHt2 t3 IHt3|lf _] et e; last first.
  by move=> e_et_0 /=;  case : ifP.
move=> e_et_0 /=; set cprr := ctree_pick_rev_rec.
case Det1: (cprr _ _ _ t1) => [|e1 et1]; last first.
  by rewrite -Det1 IHt1 // [Color1]lock /= -addcA addKc.
case Det2: (cprr _ _ _ t2) => [|e2 et2]; last first.
  by rewrite -Det2 IHt2 // [Color2]lock /= -addcA addKc.
by rewrite IHt3 // [Color3]lock /= -addcA addKc.
Qed.

Lemma size_ctree_pick_rev t t' :
  ctree_proper h t' -> pred2 0 h.+1 (size (ctree_pick_rev t t')).
Proof.
rewrite /ctree_pick_rev; set cs0 := [::]; have: size cs0 + h = h by [].
elim: {1 3}h t' cs0 {1}Color0 => [|n IHn] [t1 t2 t3|lf|] et e //=.
  by rewrite addn0; case: ifP => //= _ ->.
rewrite -addSnnS => Het [_ t1ok t2ok t3ok]; set cprr := ctree_pick_rev_rec.
case Det1: (cprr _ _ _ t1) => [|e1 et1]; last by rewrite -Det1; apply: IHn.
by case Det2: (cprr _ _ _ t2) => [|e2 et2]; last rewrite -Det2; apply: IHn.
Qed.

Section BirkhoffTree.

Variable check_basis : ctree -> bool.

Definition do_Birkhoff_check2 et ctu gtu chk :=
  let ctr := ctree_of_ttail (etrace et) in
  if Color0 \in et then false else
  let: (ctu', GtreePair gtr gtu') := Kempe_tree_closure h.-1 h ctu ctr gtu in
  gtree_empty gtr && (check_basis ctu' || chk ctu' gtu').

Fixpoint Birkhoff_check2 ctu1 gtu1 n ctu2 gtu2 :=
  if n isn't n'.+1 then false else
  if ctree_pick_rev ctu1 ctu2 isn't e :: et then false else
      do_Birkhoff_check2 (belast e et) ctu1 gtu1 (Birkhoff_check2 ctu2 gtu2 n')
   && do_Birkhoff_check2 (rev et) ctu2 gtu2 (Birkhoff_check2 ctu1 gtu1 n').

End BirkhoffTree.

Inductive Birkhoff_check : Prop :=
   BirkhoffCheck niter cps (ctu := ctree_init_tree h) (gtu := gtree_init_tree h)
     (basis := map cpcolor cps) (chkb := fun t => has (ctree_disjoint t) basis)
   of all Birkhoff_check1 cps & Birkhoff_check2 chkb ctu gtu niter ctu gtu.

End BirkhoffCheck.

Module BirkhoffCheckLemmas.

Import ConfigSyntax.

Lemma Birkhoff2 : Birkhoff_check 1 0.
Proof. by exists 1 [:: Cprog]. Qed.

Lemma Birkhoff3 : Birkhoff_check 2 0.
Proof. by exists 1 [:: Cprog Y]. Qed.

Lemma Birkhoff4 : Birkhoff_check 3 0.
Proof. by exists 4 [:: Cprog U; Cprog 1 U]. Qed.

Lemma Birkhoff5 : Birkhoff_check 4 1.
Proof.
by exists 10 [:: Cprog U Y; Cprog 1 U Y; Cprog 2 U Y; Cprog 3 U Y;
                 Cprog 4 U Y; Cprog H 4 Y Y Y].
Qed.

End BirkhoffCheckLemmas.

Import BirkhoffCheckLemmas.

Section Birkhoff.

Variable G : hypermap.
Hypothesis geoG : minimal_counter_example G.

Let planarG : planar G := geoG.
Let bridge'G : bridgeless G := geoG.
Let plainG : plain G := geoG.
Let cubicG : cubic G := geoG.
Let ccG : connected G := geoG.
Let noncolG := minimal_counter_example_is_noncolorable geoG.
Let minG := minimal_counter_example_is_minimal geoG.
Let ee := plain_eq geoG.
Let e'id := plain_neq geoG.
Let nnn := cubic_eq geoG.

Section BirkhoffValid.

Variable n : nat.
Hypothesis leq_n_trivial : forall r : seq G,
  scycle rlink r -> size r <= n -> nontrivial_ring 0 r = false.

Lemma Birkhoff_valid m (r : seq G) :
   Birkhoff_check n m -> scycle rlink r -> size r = n.+1 ->
 nontrivial_ring m r = false.
Proof.
case=> nm cps ctu0 gtu0 basis chkb bk1ok bk2ok; move: r.
have chkbP (r : seq G) (Ur : scycle rlink r) (bGd := snipd_ring planarG Ur) :
    size r = n.+1 -> nontrivial_ring m r ->
    forall ctu, chkb ctu ->
  exists2 et, ring_trace bGd (ctrace et) &  ~~ ctree_mem ctu (etrace et).
- move=> sz_r nt_r ctu; move: bk1ok {bk2ok}; rewrite {}/chkb {}/basis.
  elim: cps => [|cp cps IHcp] //= /andP[/and3P[cpQ ltn_cp szr_cp] bk1ok].
  case/orP=> [{cps bk1ok IHcp}ctu'cp|]; last exact: IHcp.
  pose Gr := cpmap cp; pose bGr : seq Gr := rotr 1 (rev (cpring Gr)).
  have ntGr : proper_cpring Gr := cpmap_proper cpQ.
  have cycNbGr: ufcycle node bGr.
    by rewrite rot_ucycle /ucycle cycle_rev_cpring rev_uniq cpring_uniq.
  set Gd := snip_disk planarG Ur in bGd *.
  have cycEbGd: sfcycle edge bGd by apply: scycle_snipd_ring.
  have sz_bGdr: size bGd = size bGr.
    rewrite size_rot size_rev size_ring_cpmap (eqP szr_cp) -sz_r.
    by rewrite -(map_snipd_ring planarG Ur) size_map.
  pose G2 := sew_map cycEbGd cycNbGr sz_bGdr.
  have ppG2 := sew_map_patch cycEbGd cycNbGr sz_bGdr.
  have ppGd := snip_patch planarG Ur; rewrite -/bGd in ppGd.
  move: plainG; rewrite (plain_patch ppGd) => /andP[plainGd plainGrr].
  move: cubicG; rewrite (cubic_patch ppGd) => /andP[cubicGd cubicGrr].
  have planarG2: planar G2.
    by rewrite /planar (genus_patch ppG2) addn_eq0 cpmap_planar // planar_snipd.
  have plainG2: plain G2.
    by rewrite (plain_patch ppG2); apply/andP; split; last apply: cpmap_plain.
  have cubicG2: cubic G2.
    rewrite (cubic_patch ppG2); apply/andP; split => //.
    by apply/subsetP=> x; rewrite !inE mem_rot => /(subsetP (cpmap_cubic cpQ)).
  have bridge'G2: bridgeless G2.
    have [bridge'Gd _] := patch_bridgeless ppGd bridge'G.
    apply: bridgeless_patch ppG2 bridge'Gd (cpmap_bridgeless cpQ) _. 
    apply/idPn=> chord_bGd.
    have [r1 Ur1 [nt_r1 lt_r1r]] := ring_disk_chord geoG nt_r chord_bGd.
    by rewrite (leq_n_trivial Ur1) // -ltnS -sz_r in nt_r1.
  have colG2: four_colorable G2.
    apply: minG; try by do ![split | apply: cubic_precubic].
    rewrite ltnNge -(leq_add2l (size bGd)).
    move: (card_patch ppG2) (card_patch ppGd); rewrite !size_map -/G2 => <- <-.
    rewrite leq_add2l -ltnNge -ltnS card_cpmap (leq_trans ltn_cp) //.
    pose bGrr := snipr_ring planarG Ur.
    have sz_bGrr: size bGrr = n.+1.
      by rewrite -sz_r -(size_rev r) -(map_snipr_ring planarG Ur) size_map.
    case DbGrr: bGrr (sz_bGrr) => // [z0 bGrr1] _.
    have geoGrr: ucycle_plain_quasicubic_connected bGrr.
      split; first by split; [ split | apply: ucycle_snipr_ring].
      exact: (patch_connected_r ppGd ccG).
    move: (planar_snipr planarG Ur); rewrite (quasicubic_Euler geoGrr) /nilp.
    rewrite sz_bGrr add1n (patch_fcard_face_r ppGd) /outer -/Gr.
    move: #|_| => nGrr; pose arF := [predU diskFC r & fband r].
    have nbFarF: fcard face arF = n.+1 + fcard face (diskFC r).
      rewrite -sz_r -(scycle_fcard_fband Ur) -cardUI addnC eq_card0 => [|x].
        apply: eq_card => x; rewrite !inE.
        by case: (x \in fband r); rewrite andbF ?orbT ?orbF.
      by rewrite !inE; case: (x \in fband r); rewrite !andbF.
    rewrite mulnSr addnA (addnA _ 6 6) eqn_add2r.
    rewrite -(@eq_n_comp_r _ _ arF) => [|x].
      rewrite nbFarF addSn mulnSr eqn_add2r mulnDr (mulnDl 4 2) addnC.
      rewrite mul2n addnA doubleS -2!addSnnS eqn_add2r -ltnS => /eqP <-.
      by rewrite ltn_add2r ltn_pmul2l //; case/andP: nt_r.
    have imGr := codom_snipr planarG Ur.
    apply/idP/exists_inP=> [|[y]].
      rewrite !inE orbC unfold_in; case: hasP => [[y ry xFy] | _ dN'x].
        by exists y; rewrite // !inE imGr !inE ry.
      by exists x; rewrite !inE // imGr !inE (negPf dN'x) andbF.
    rewrite !(inE, imGr) orbC => xFy; apply: contraR.
    case/norP=> rF'x; rewrite rF'x negbK => dNx.
    have /andP[/= rF'y ->]: y \in diskF r.
      by rewrite -(closed_connect (diskF_face r) xFy) !inE rF'x.
    by rewrite (contra (subsetP (ring_fband r) _)).
  have [/(_ colG2)[et Det_d Det_r] _] := colorable_patch ppG2.
  case/lastP: et => [|et e] in Det_d Det_r.
    have [k _ /esym/nilP/negP[]] := Det_r.
    by rewrite /nilp size_trace size_map size_rot size_rev head_cpring.
  have De: sumt et = e.
    apply/eqP; have [k _ /(congr1 (sumt \o rotr 1))/eqP] := Det_d.
    by rewrite /= rotr1_rcons -[rotr 1 _]trace_rot sumt_trace /= addcC addc_eq0.
  exists et => [|{Det_d}]; first by rewrite /ctrace De.
  rewrite (ctree_mem_disjoint ctu'cp) //; apply/ctree_mem_cpcolor.
  split; first exact: even_etrace; rewrite /etrace sumt_permt De.
  have [k col_k Det] := Det_r; exists (etrace_perm et \o k).
    by apply: coloring_inj col_k; apply: permc_inj.
  rewrite -/Gr map_comp trace_permt -(revK (cpring Gr)) map_rev trace_rev.
  rewrite -rev_rotr -[rotr 1 _]trace_rot size_trace -[rot _ _]map_rotr -Det.
  by rewrite !(rev_rcons, rot1_cons) revK.
case Dn: {1}n => [|n'] => [[|x[]] // /andP[/andP[]] | r Ur sz_r].
  by rewrite /rlink cfaceC bridgeless_cface.
apply: contraTF bk2ok => nt_r; have Ur2 := scycle_rev_ring geoG Ur.
pose P Ur1 et := ~ ring_trace (snipd_ring planarG Ur1) et.
pose kv r1 Ur1 := Kempe_valid n' (P r1 Ur1) ctu0 CtreeEmpty GtreeEmpty gtu0.
have: kv _ Ur2 by rewrite /kv /ctu0 /gtu0 Dn; apply: Kempe_valid_init.
have: kv r Ur by rewrite /kv /ctu0 /gtu0 Dn; apply: Kempe_valid_init.
move: sz_r nt_r Ur Ur2; rewrite {}/kv -Dn.
elim: nm r ctu0 gtu0 {2 4}ctu0 {2 4}gtu0 => // nm IHnm r1 ctu1 gtu1 ctu2 gtu2.
set r2 := rev_ring r1 => sz_r1 nt_r1 Ur1 Ur2 r1valid r2valid /=.
have sz_r2: size r2 = n.+1 by rewrite size_rev size_map.
have nt_r2: nontrivial_ring m r2 by apply: (nontrivial_rev_ring geoG).
have r1closed := @ring_disk_closed _ geoG planarG _ Ur1 _ nt_r1 cubicG.
have r2closed := @ring_disk_closed _ geoG planarG _ Ur2 _ nt_r2 cubicG.
case Det: (ctree_pick_rev ctu1 ctu2) => //= [e et].
have Dct0 (ct0 := untrace Color0 (e :: et)): trace ct0 = e :: et.
  by rewrite trace_untrace // -Det sumt_ctree_pick_rev.
have sz_et: size et = n.
  have [[ctu2ok _] _] := r2valid; have:= size_ctree_pick_rev ctu1 ctu2ok.
  by rewrite Det !inE /= -Dn => /eqP[].
apply/andP=> [[r1check r2check]]; case: noncolG.
apply: (@colorable_from_ring _ geoG planarG _ Ur1 _ nt_r1 (e :: et)).
  have [// | tr1'et] := decide_ring_trace (snipd_ring planarG Ur1) (e :: et).
  move: r1check {r2check}; rewrite /do_Birkhoff_check2 {1}Dn.
  set ctr := ctree_of_ttail _; case: ifPn => // et'0.
  have []:= @Kempe_tree_closure_correct n' (P _ Ur1) n ctu1 ctr gtu1.
    apply: Kempe_valid_restrict r1valid => et1 /ctree_of_ttail_mem Det1.
    rewrite Det1 ?memc0_permt // ctrace_permt.
    split; last by rewrite size_map size_belast sz_et.
    move: (etrace_perm _) => g /r1closed[tr1_et _]; case: tr1'et.
    suffices ->: e :: et = ctrace (belast e et).
      by rewrite -[ctrace _](mapK (inv_permc g)); apply: tr1_et.
    by rewrite -Dct0 /= (scanlK addKc).
  case: Kempe_tree_closure => ctu3 [[] // gtu3] {tr1'et r1valid}r1valid _.
  case/orP=> [/(chkbP r1)[]// et1 tr_et1 ct3'et1 | {r1closed}/idPn[]].
    suffices sz_et1: size et1 = n'.+1.
      by have[] := Kempe_validP r1valid sz_et1 ct3'et1 r1closed tr_et1.
    have [k _ /(congr1 size)] := tr_et1; rewrite size_rcons size_trace size_map.
    by rewrite -(size_map snipd) (map_snipd_ring planarG Ur1) sz_r1 Dn => [][].
  by rewrite -(rev_rev_ring geoG r1) in Ur1 r1valid; apply: (IHnm r2).
have [| tr2'et] := decide_ring_trace (snipd_ring planarG Ur2) (rev (e :: et)).
  by congr (ring_trace (snipd_ring _ _) _); apply: bool_irrelevance.
move: r2check {r1check}; rewrite /do_Birkhoff_check2 {1}Dn.
set ctr := ctree_of_ttail _; case: ifPn => // et'0.
have []:= @Kempe_tree_closure_correct n' (P r2 Ur2) n ctu2 ctr gtu2.
  apply: Kempe_valid_restrict r2valid => et2 /ctree_of_ttail_mem-Det2.
  rewrite {}Det2 ?memc0_permt {et'0}// ctrace_permt.
  split; last by rewrite size_map size_rev -Dn.
  move: (etrace_perm _) => g /r2closed[tr2_et _]; case: tr2'et.
  suffices ->: rev (e :: et) = ctrace (rev et).
    by rewrite -[ctrace _](mapK (inv_permc g)); apply: tr2_et.
  suffices /eqP: sumt (rev (rcons et e)) = Color0.
    by rewrite rev_cons rev_rcons /= addc_eq0 => /eqP->.
  rewrite -rot1_cons -Dct0 -[rev _](rotrK 1) -rev_rot -!trace_rot -trace_rev.
  exact: sumt_trace.
case: Kempe_tree_closure => ctu3 [[] // gtu3] {r2valid tr2'et}r2valid _.
case/orP=> [/(chkbP r2)[]// et3 tr_et3 ct'et3 | /idPn[]]; last exact: (IHnm r1).
suffices sz_et3: size et3 = n'.+1.
  by have [] := Kempe_validP r2valid sz_et3 ct'et3 r2closed tr_et3.
have [k _ /(congr1 size)] := tr_et3; rewrite size_rcons size_trace size_map.
by rewrite -(size_map snipd) map_snipd_ring sz_r2 Dn => [][].
Qed.

End BirkhoffValid.

Theorem Birkhoff (r : seq G) :
  size r <= 5 -> scycle rlink r -> nontrivial_ring (size r == 5) r = false.
Proof.
elim: {1 3}5 (leqnn 5) => [|n IHn] n_lt5 in r *.
  case: r => // _ _; rewrite /nontrivial_ring [fcard _ _]eq_card0 // => x.
  by rewrite !inE andbF.
move/(_ (ltnW n_lt5)) in IHn; rewrite leq_eqVlt => /predU1P[]; last exact: IHn.
move=> sz_r Ur; apply: (Birkhoff_valid _ _ Ur sz_r).
  move {r Ur sz_r} => r Ur r_le_n; rewrite -(IHn r r_le_n) //.
  by rewrite eqn_leq andbC leqNgt (leq_trans _ n_lt5).
have [*] := And4 Birkhoff2 Birkhoff3 Birkhoff4 Birkhoff5.
rewrite sz_r; case: n sz_r n_lt5 {IHn}; last by do 4![case=> //].
by case: r Ur => [|x []]; rewrite /scycle //= /rlink cfaceC bridgeless_cface.
Qed.

Lemma nontrivial_cycle2 (x y : G) (r := [:: x; y]) :
  scycle rlink r -> edge x != y -> nontrivial_ring 0 r.
Proof.
move=> Ur y'ex; apply/nontrivial0P; split.
  exists (node x); rewrite !inE -(fclosed1 (diskN_node r)).
  rewrite diskN_E mem_head unfold_in /= -{2}[x]nodeK -cface1r.
  rewrite bridgeless_cface //= orbF andbT; apply: contraL Ur => nxFy /=.
  rewrite /rlink -(same_connect_r cfaceC nxFy) -[node x]nodeK -cface1r.
  by rewrite cface1 -(canRL nodeK (nnn x)) bridgeless_cface.
pose nex := node (edge x); have rF'nex: nex \notin fband r.
  rewrite unfold_in /= orbF -{1}[nex]nodeK -cface1 (canRL nodeK (nnn _)) ee.
  rewrite cfaceC cface1 bridgeless_cface //; apply: contraL Ur => /= nexFy.
  rewrite {1}/rlink -(same_connect_r cfaceC nexFy) -[edge x]nodeK -cface1.
  by rewrite cfaceC bridgeless_cface.
exists nex; rewrite !inE rF'nex -(fclosed1 (diskN_node r)) diskN_E inE /=.
by rewrite -(fclosed1 (diskE_edge planarG Ur)) !inE e'id eqxx (negPf y'ex).
Qed.

Lemma double_dart (x y : G) : cface x y -> cface (edge x) (edge y) -> x = y.
Proof.
move=> xFy exFey; apply: contraTeq isT => y'x /=.
have Ur: scycle rlink [:: x; edge y] by rewrite srcycleI //= exFey ee cfaceC.
by rewrite -(Birkhoff _ Ur) // nontrivial_cycle2 // (inj_eq edgeI).
Qed.

Section SpokeRing.

Variable x : G.

Let p : seq G := orbit face x.

Let p_x : x \in p. Proof. by rewrite -fconnect_orbit. Qed.

Let ucycFp : ufcycle face p.
Proof. by rewrite /ucycle orbit_uniq (cycle_orbit faceI). Qed.

Let Ep y : cface x y = (y \in p). Proof. exact: fconnect_orbit. Qed.

Definition spoke (y : G) : G := face (edge y).

Lemma inj_spoke : injective spoke.
Proof. by apply: can_inj node _; apply: edgeK. Qed.

Definition spoke_ring : seq G := map spoke (rev p).

Lemma mem_spoke_ring y : (y \in spoke_ring) = cface x (node y).
Proof. by rewrite -{1}[y]nodeK (mem_map inj_spoke) mem_rev Ep. Qed.

Local Notation r := spoke_ring.
Local Notation Er := mem_spoke_ring.

Lemma next_spoke_ring (y : G) : y \in r -> next r y = face (spoke y).
Proof.
move=> ry; have [cycFp Up] := andP ucycFp.
rewrite -{1}[y]nodeK (next_map inj_spoke) ?rev_uniq // (next_rev Up).
rewrite -[prev p _]faceK /spoke ee -(canRL nodeK (nnn y)).
by rewrite (eqP (prev_cycle cycFp _)) // -Ep -Er.
Qed.

Lemma scycle_spoke_ring : scycle rlink r.
Proof.
have [cycFp Up] := andP ucycFp; apply/andP; split.
  apply: cycle_from_next; first by rewrite (map_inj_uniq inj_spoke) ?rev_uniq.
  by move=> y ry; rewrite (next_spoke_ring ry) /rlink -!cface1r.
rewrite /simple /r !map_rev rev_uniq -map_comp map_inj_in_uniq // => y z py pz.
move/(rootP cfaceC); rewrite -cface1 -cface1r; apply: double_dart.
by rewrite -!Ep in py pz; rewrite -(same_cface py).
Qed.
Let scycRr := scycle_spoke_ring.

Lemma diskF_spoke_ring y : (y \in diskF r) = cface x y.
Proof.
apply/andP/idP=> [[/= rF'y /hasP[z rz n'zDy]] | xFy]; last first.
  split; last first.
     rewrite /= -{1}[y]edgeK -(fclosed1 (diskN_node r)) diskN_E inE /= Er.
     by rewrite edgeK xFy.
  apply/hasP=> -[z]; rewrite Er => xFnz.
  rewrite -[z]nodeK -cface1r -(same_cface xFy) (same_cface xFnz).
  by rewrite bridgeless_cface.
case/connectP: n'zDy rF'y; set z0 := finv node z.
have rfz0: face z0 \in r.
  by rewrite -(ee z0) Er edgeK -(nnn z0) (f_finv nodeI) cface1r nodeK -Er.
case=> [|z1 q] /= z0Dq ->{y}.
  by case/hasP; exists (face z0); last exact: fconnect1.
case/andP: z0Dq => /andP[_ /clinkP[z0nz1 | fz0z1]] z1Dq; last first.
  case: q z1Dq => [|z2 q]; last by rewrite /dlink /= -fz0z1 rfz0.
  by rewrite (subsetP (ring_fband r)) // -fz0z1.
move: rz z1Dq; rewrite Er {z z0 z0nz1 rfz0}(canRL (f_finv nodeI) z0nz1) nnn.
elim: q z1 => //= z q IHq y xFy /andP[/andP[_ /clinkP[ynz | fyz]]].
  have rz: z \in r by rewrite Er -ynz.
  case: q {IHq} => [|z1 q]; last by rewrite /dlink /= rz.
  by rewrite (subsetP (ring_fband r)).
by apply: IHq; rewrite -fyz -cface1r.
Qed.

Lemma chordless_spoke_ring : chordless r.
Proof.
apply/subsetP=> y1 ry1; apply: contraLR isT => /exists_inP[y2] /= /adjP[z y1Fz].
rewrite /rlink => ezFy2 /and3P[ry1'y2 r'y1'y2 /= ry2].
pose q := [:: node y2; edge z; edge (node y1)].
have scycRq: scycle rlink q.
  rewrite srcycleI //= !ee cface1 nodeK cfaceC ezFy2 /= andbC.
  rewrite cface1r nodeK cfaceC y1Fz /= cfaceC; rewrite !Er in ry1 ry2.
  by rewrite -!(same_cface ry2) !(same_cface ry1) connect0 bridgeless_cface.
rewrite -(Birkhoff _ scycRq) //; apply/(nontrivial0P _); split.
  pose t := node (edge (node y1)); exists t; rewrite !inE.
  have Dt: t = prev r y1.
    have [_ Ur] := andP scycRr; rewrite /t -{1}[y1](next_prev (simple_uniq Ur)).
    by rewrite next_spoke_ring ?mem_prev // faceK edgeK.
  rewrite Er in ry2; rewrite unfold_in /= cfaceC -(same_cface ry2).
  have xFnt: cface x (node t) by rewrite -Er Dt mem_prev.
  rewrite (same_cface xFnt) -{2}[t]nodeK -cface1r bridgeless_cface //= orbF.
  rewrite cfaceC (same_cface ezFy2) cfaceC /= orbC.
  rewrite -[edge _]nodeK -cface1r bridgeless_cface //=.
  rewrite -(fclosed1 (diskN_node q)) diskN_E inE /= !inE eqxx !orbT andbT.
  apply: contra r'y1'y2 => tFy2; rewrite -Dt eq_sym.
  by apply/eqP/(scycle_cface scycRr); rewrite ?Er.
exists (node (node y1)); rewrite !inE andbC -(fclosed1 (diskN_node q)).
rewrite -{1}[node y1]ee (diskN_edge_ring geoG) ?inE ?eqxx ?orbT ?unfold_in //=.
rewrite !Er in ry1 ry2; rewrite cfaceC -(same_cface ry2) (same_cface ry1).
rewrite -{1}[node _]nodeK -cface1 cfaceC bridgeless_cface //= orbF orbC.
rewrite (canRL nodeK (nnn _)) -cface1 cfaceC cface1 nodeK bridgeless_cface //=.
rewrite cface1 cfaceC (same_cface ezFy2) -next_spoke_ring; last by rewrite Er.
by apply: contra ry1'y2 => /(scycle_cface scycRr)->; rewrite ?mem_next ?Er.
Qed.

Lemma size_spoke_ring : size r = arity x.
Proof. by rewrite /r size_map size_rev /p /orbit size_traject. Qed.

(* Proof note: the Birkhoff theorem only tells us the spoke ring must have an *)
(* empty exterior -- we must reuse the non-colorability condition to rule out *)
(* the tetrahedral map! It then turns out to be easier to use colorability    *)
(* as well to rule out the square map, rather than prove it is not cubic.     *)
Lemma min_arity : 4 < arity x.
Proof.
rewrite /= -size_spoke_ring ltnNge; apply: contraL isT => r_le4 /=.
have [y dFCy | dCF_0] := pickP [pred y | y \in diskFC r].
  rewrite -(Birkhoff _ scycRr) 1?ltnW // eqn_leq andbC ltnNge r_le4 /=.
  apply/(nontrivial0P _); split; last by exists y.
  by exists x; rewrite diskF_spoke_ring.
case: noncolG; exists (fun y =>
  if cface x y then Color0 else
  let i := find (cface y) r in
  if (i == 2) && (size r == 3) then Color3 else
  if pred2 0 2 i then Color1 else Color2).
split=> y /=; last by rewrite -cface1r -(eq_find (cface1 y)) eqxx.
set i1 := find (cface y) r; set i2 := find (cface (edge y)) r.
case xFy: (cface x y).
  by rewrite (same_cface xFy) bridgeless_cface //; do 2?case: ifP.
case xFey: (cface x (edge y)); first by do 2?case: ifP.
have rFy: y \in fband r.
  apply: contraFT (dCF_0 y) => rF'y; rewrite !inE rF'y.
  by rewrite -diskF_spoke_ring !inE rF'y /= in xFy; rewrite xFy.
have rFey: edge y \in fband r.
  apply: contraFT (dCF_0 (edge y)) => rF'ey; rewrite !inE rF'ey.
  by rewrite -diskF_spoke_ring !inE rF'ey /= in xFey; rewrite xFey.
pose z1 := nth x r i1; pose z2 := nth x r i2.
have z1Az2: adj z1 z2.
  by apply/adjP; exists y; first rewrite cfaceC; apply: nth_find.
have [lti1r lti2r]: i1 < size r /\ i2 < size r by rewrite -!has_find.
have [rz1 rz2]: z1 \in r /\ z2 \in r by rewrite !mem_nth.
have [cycRr /simple_uniq Ur] := andP scycRr.
have{rz1}:= pred0P (subsetP chordless_spoke_ring _ rz1) z2.
rewrite !inE {}z1Az2 {}rz2 andbT (eq_sym z2) (canF_eq (prev_next Ur)) /=.
have eq_nth_prev i j (lti : i < size r) (ltj : j < size r):
  (nth x r j == prev r (nth x r i)) = (j == (if i == 0 then size r else i).-1).
- suff <-: index (prev r (nth x r i)) r = (if i == 0 then size r else i).-1.
    by rewrite -(nth_uniq x _ _ Ur) ?nth_index ?index_mem // mem_prev ?mem_nth.
  rewrite prev_nth mem_nth //; case Dr: r => // [x0 r1] in Ur lti *.
  rewrite index_uniq ?ltnS ?index_size //; have /=/andP[r1'x0 Ur1] := Ur. 
  case: i => [|i] /= in lti *; last by rewrite index_uniq.
  by apply/eqP; rewrite eqn_leq index_size leqNgt index_mem.
rewrite !{}eq_nth_prev {z1 z2}//.
case Dn: (size r) r_le4 lti1r lti2r => [|[|n]] //.
  by case: r cycRr Dn => [|x0 []] //=; rewrite /rlink cfaceC bridgeless_cface.
by case: i1 i2 n {Dn} => [|[|[|[|i1]]]] [|[|[|[|i2]]]] [|[|[|n]]].
Qed.

Lemma fband_spoke_ring y : (y \in fband r) = adj x y.
Proof.
apply/hasP/adjP => [[z rz zFy] | [z xFz zRy]].
  by exists (node z); [rewrite -Er | rewrite /rlink cface1 nodeK cfaceC].
by exists (face (edge z)); [rewrite Er edgeK | rewrite -cface1r cfaceC].
Qed.

Lemma adj11_edge y : adj x y -> adj x (edge y) -> (y \in r) || (edge y \in r).
Proof.
rewrite -!fband_spoke_ring => /hasP[z rz yFz] /hasP[t rt eyFt].
apply: contraFT (pred0P (subsetP chordless_spoke_ring _ rz) t).
case/norP=> r'y r'ey; rewrite !inE -(adjF yFz) -(adjFr eyFt) adjE rt andbT.
have [cycRr /simple_uniq Ur] := andP scycRr.
rewrite /= andbC eq_sym (canF_eq (next_prev Ur)) !next_spoke_ring //.
apply/andP; split; apply/eqP=> Dz.
  rewrite Dz -!cface1r -[y]ee in yFz.
  by rewrite (double_dart eyFt) ?rt in r'ey.
by rewrite Dz -!cface1r in eyFt; rewrite (double_dart yFz) ?rz in r'y.
Qed.

Lemma fcard_adj_adj y : adj x y -> fcard face (predI (adj y) (adj x)) = 2.
Proof.
move=> xAy; have /hasP[y1 ry1 yFy1]: y \in fband r by rewrite fband_spoke_ring.
rewrite [fcard _ _](cardD1 (froot face (next r y1))).
rewrite (cardD1 (froot face (prev r y1))) !inE !(roots_root cfaceC).
have r_xA z: z \in r -> adj x z by rewrite Er => /adjF->; apply: adjN.
set z1 := prev r y1; have rz1: z1 \in r by rewrite mem_prev.
set z2 := next r y1; have rz2: z2 \in r by rewrite mem_next.
rewrite -!(adjFr (connect_root _ _)) !r_xA //=.
have [cycRr /simple_uniq Ur] := andP scycRr.
rewrite !(adjF yFy1) (rlink_adj (next_cycle cycRr ry1)) adjC //.
rewrite (rlink_adj (prev_cycle cycRr ry1)) /= (sameP eqP (rootP cfaceC)).
case z1Fz2: (cface z1 z2).
  case: (rot_to rz1) min_arity (cycle_next Ur) (Ur) => [i r1 Dr].
  rewrite -size_spoke_ring -(size_rot i) -(rot_cycle i) -(rot_uniq i) Dr.
  case: r1 {Dr} => [|y3 [|z3 r3]] // _ /and3P[/= /eqP Dy3 /eqP Dz3 _].
  case/andP=> /= /norP[_ /norP[/eqP[]]]; rewrite -Dz3 -Dy3.
  by rewrite (next_prev Ur); apply: (scycle_cface scycRr).
rewrite eq_card0 // => t; apply/and5P=> [] [z1F't z2F't /eqP Dt yAt xAt].
rewrite -Dt !(sameP eqP (rootP cfaceC)) in z1F't z2F't.
move: xAt; rewrite -fband_spoke_ring => /hasP[t1 rt1 tFt1].
case/andP: (pred0P (subsetP chordless_spoke_ring _ ry1) t1); split.
  by rewrite !inE -(adjF yFy1) -(adjFr tFt1).
rewrite !inE rt1 andbT; apply/andP; split; apply/eqP => [Dt1].
  by rewrite (same_cface tFt1) Dt1 connect0 in z2F't.
by rewrite (same_cface tFt1) Dt1 connect0 in z1F't.
Qed.

Definition adj01 (y z : G) := cface y z || adj y z.

Lemma adj12_edge y z :
  adj x y -> adj x z -> adj z (edge y) -> adj01 z y || adj01 x (edge y).
Proof.
rewrite -2!fband_spoke_ring => /hasP[y1 ry1 yFy1] /hasP[z1 rz1 zFz1].
case/adjP=> x1 zFx1; rewrite /rlink cfaceC => eyFex1.
apply/norP=> [] [/norP[zF'y zA'y] /norP[xF'ey xA'ey]].
rewrite !(same_cface zFz1) in zF'y zFx1; rewrite {z zFz1}(adjF zFz1) in zA'y.
pose q := [:: y; edge x1; edge (node z1); node y1].
have scycRq: scycle rlink q.
  rewrite srcycleI //= eyFex1 cface1r nodeK cfaceC zF'y !ee /= andbT.
  rewrite (same_cface yFy1) cfaceC (adj_no_cface geoG (adjN y1)) /=.
  rewrite cface1r nodeK cfaceC zFx1 -(same_cface eyFex1) cfaceC.
  rewrite !Er in ry1 rz1; rewrite -(same_cface ry1) xF'ey.
  by rewrite -(same_cface rz1) ry1 cface1 nodeK cfaceC yFy1.
apply: (elimF (nontrivial0P _) (Birkhoff _ scycRq) _) => //; split.
  exists (node (node y1)); rewrite !inE -(fclosed1 (diskN_node q)).
  rewrite diskN_E !inE eqxx /= !orbT andbT // unfold_in /= orbF.
  rewrite cfaceC (same_cface yFy1) -{2 4}[y1]edgeK nnn -cface1r.
  rewrite bridgeless_cface // cfaceC -(same_cface eyFex1) (no_adj_adj xA'ey).
    rewrite -cface1 cfaceC cface1 nodeK; rewrite adjC // in zA'y.
    rewrite (no_adj_adj zA'y); first by rewrite adj_no_cface ?adjN.
    by rewrite (adjF yFy1) adjE.
  by rewrite Er in ry1; rewrite (adjF ry1) adjC ?adjN.
exists (node (node z1)); rewrite !inE -(fclosed1 (diskN_node q)).
rewrite -{2}[node z1]ee (diskN_edge_ring geoG) //= ?inE ?eqxx ?orbT //.
rewrite unfold_in /= andbT orbF -{1 3}[z1]edgeK nnn -cface1 cfaceC.
rewrite (no_adj_adj zA'y (adjE z1)); rewrite !Er in ry1 rz1.
rewrite cfaceC -(same_cface eyFex1) (no_adj_adj xA'ey) /=.
  rewrite -cface1 cfaceC cface1 nodeK bridgeless_cface //.
  rewrite cfaceC -(same_cface ry1) (same_cface rz1) -{1}[node z1]nodeK -cface1.
  by rewrite cfaceC bridgeless_cface.
by rewrite (adjF rz1) adjC ?adjN.
Qed.

Lemma fcard_adj_max y : ~~ cface x y -> fcard face (predI (adj y) (adj x)) <= 2.
Proof.
move=> xA'y; case xAy: (adj01 x y).
  by rewrite /adj01 (negPf xA'y) in xAy; rewrite (fcard_adj_adj xAy).
rewrite {xA'y}leqNgt /(fcard _ _); set axy := predI _ _; apply/negP => axy_gt2.
have{axy_gt2} []: {e | 2 < size e & all axy e /\ uniq e}.
  exists (enum axy); [by rewrite -cardE | split; last exact: enum_uniq].
  by apply/allP=> z; rewrite mem_enum.
case=> [|z1 [|z2 [|z3 e]]] //= _ [/and4P]; rewrite !inE !negb_or.
case=> /and3P[Dz1 yAz1 xAz1] /and3P[Dz2 yAz2 xAz2] /and3P[Dz3 yAz3 xAz3] _.
case/and3P=> /and3P[z2'1 z3'1 _] /andP[z3'2 _] _ {axy e}.
have{xAy} cross_adj z t: z != t -> froots face z -> froots face t ->
    adj x z -> adj x t -> adj y z -> adj y t -> adj z t.
- move=> /negPf t'z /eqP Dz /eqP Dt xAz xAt yAz /adjP[u yFu uRt].
  rewrite -(adjFr uRt) in xAt; rewrite (adjF yFu) adjC // -[u]ee in yAz.
  move: (adj12_edge xAt xAz yAz).
  rewrite ee orbC /adj01 -(adjFr yFu) cfaceC -(same_cface yFu) cfaceC.
  rewrite -/(adj01 x y) xAy cfaceC (same_cface uRt) cfaceC.
  by rewrite (sameP (rootP cfaceC) eqP) Dz Dt t'z (adjFr uRt).
have []: [/\ adj z1 z2, adj z1 z3 & adj z2 z3] by split; apply: cross_adj.
move: {y Dz1 Dz2 Dz3 yAz1 yAz2 yAz3 z2'1 z3'1 z3'2 cross_adj} xAz1 xAz2 xAz3.
rewrite -!fband_spoke_ring => /hasP[t1 rt1 zFt1] /hasP[t2 rt2 zFt2].
move=> /hasP[t3 rt3 zFt3].
rewrite !(adjF zFt1) (adjF zFt2) (adjFr zFt2) !(adjFr zFt3).
move {z1 z2 z3 zFt1 zFt2 zFt3} => t1At2 t1At3 t2At3.
have [cycRr /simple_uniq Ur] := andP scycRr.
have Ar_xor u v: adj u v -> u \in r -> v \in r ->
    next r u <> next r v /\ (next r u = v \/ next r v = u).
- move=> uAv ru rv; split=> [eq_ruv | ].
    have /idP[] := adj_no_cface bridge'G uAv.
    by rewrite (can_inj (prev_next Ur) eq_ruv).
  apply/pred2P; apply: contraFT (pred0P (subsetP chordless_spoke_ring _ ru) v).
  by rewrite !inE uAv rv -(canF_eq (prev_next Ur)) eq_sym negb_or andbT.
have{t1At2} [rt2'1 rt1V2] := Ar_xor t1 t2 t1At2 rt1 rt2.
have{t1At3} [rt3'1 rt1V3] := Ar_xor t1 t3 t1At3 rt1 rt3.
have{Ar_xor t2At3} [rt3'2 rt2V3] := Ar_xor t2 t3 t2At3 rt2 rt3.
have [i r1 Dr1] := rot_to rt1.
move: min_arity (cycle_next Ur) (Ur).
rewrite -size_spoke_ring -(size_rot i) -(rot_cycle i) -(rot_uniq i) {i}Dr1.
case: r1 => [|u2 [|u3 [|u4 r1]]] //= _ /and4P[/eqP <- /eqP <- /eqP <- _].
rewrite !negb_or => /andP[/and4P[_ _ /eqP[]]] {u2 u3 u4 r1}.
case: rt1V2 rt2V3 rt1V3 rt2'1 rt3'1 rt3'2; first by move=> -> [] -> // [] ->.
by move=> Dt1; rewrite Dt1 => [] [-> | Dt2] // [] -> //; rewrite Dt2.
Qed.

End SpokeRing.

Definition minimal_counter_example_is_plain_cubic_pentagonal :=
  PlainCubicPentagonal geoG min_arity.

End Birkhoff.

Prenex Implicits spoke spoke_ring.

Coercion minimal_counter_example_is_plain_cubic_pentagonal :
  minimal_counter_example >-> plain_cubic_pentagonal.
