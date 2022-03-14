(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype path fingraph.
From fourcolor Require Import hypermap geometry color coloring cfmap ctree.
From fourcolor Require Import cfcolor.

(******************************************************************************)
(*   Compute the contract of a configuration construction: a cprog whose ring *)
(* colorings coincides with the contract colorings of the initial cprog.      *)
(*   The computation also checks the validity of the contract (sparseness,    *)
(* and if required the existence of a triad).                                 *)
(*   Recall that in library coloring we chose to represent contracts as a     *)
(* of darts that forms a transversal of the edges deleted by the contract.    *)
(* The contract annotation represents this list by a list of the indices of   *)
(* the darts in a transversal of all the kernel edges of the map constructed  *)
(* by the configuration program. Out-of-bounds indices are ignored, so        *)
(* contracts are alway off-ring by construction.                              *)
(*   The kernel edge transversal list edges in the reverse order they become  *)
(* kernel edges during the construction. Each Y step adds a single edge, the  *)
(* 'foot' of the Y, except the initial Y step, as after this step all edges   *)
(* are still ring edges; note that this initial Y is actually at the end of   *)
(* the construction program, which is interpreted right-to-left). Each H step *)
(* adds three edges: the right and left `feet' of the H, and the horizontal   *)
(* crossbar, in that order, by convention; thus in the (reverse order)        *)
(* they appear in the "crossbar, left, right" order.                          *)
(*    Definitions:                                                            *)
(*  cfcontract cf == a transversal of the contract edges of cfmap cf.         *)
(* contract_ctree cf == Some ctree of the contract colorings of cfmap cf, if  *)
(*                   cfprog cf is well-formed (satisfies config_prog) and     *)
(*                   cfcontract cf is valid (sparse, with a triad if size 4). *)
(*    ctrmsize cp == the number of 'kernel' (non-ring) edges in cfmap cp.     *)
(*     ctrenum cp == a transversal sequence of the kernel edges of cfmap cp.  *)
(* ctrmask cp cci == mask for the contract index list cci and cfprog cp.      *)
(* cfcontract_mask cf == contract mask for cf : config.                       *)
(* valid_ctrm cm cp <=> the contract represented by mask cm : bitseq is valid *)
(*                   for cpmap cp (size in [1,4], with a triad for size 4).   *)
(*  ctrband cm cp == the cpmask selecting the faces of cp incident to one of  *)
(*                   the edges selected by contract mask cm; this may include *)
(*                   both kernel and ring faces (see the cfmap documentation).*)
(* cptriad ccm cp i == the kernel of cpmap cp has a triad with index < i, for *)
(*                   a contract with ctrband ccm -- that is, there is a face  *)
(*                   with index < i that is adjacent to at least 3 of the     *)
(*                   faces selected by ccm, as well as to a face NOT in ccm.  *)
(* cfctr mr mk cp == Some cfprog for the application of the contract erasing  *)
(*                   the edges selected by masks mk (for kernel edges) and mr *)
(*                   (for ring edges, in recursive calls), provided cp is a   *)
(*                   config_prog and the contract is sparse.                  *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section ConfigContract.

Fixpoint ctrmsize (cp : cprog) : nat :=
  match cp with
  | CpR _ :: cp' => ctrmsize cp'
  | [:: CpY] => 0
  | CpY :: cp' => (ctrmsize cp').+1
  | CpH :: cp' => (ctrmsize cp').+3
  | _ => 0
  end.

Fixpoint ctrmask_rec (cci : seq nat) i n {struct n} : bitseq :=
  if n is n'.+1 then (i \in cci) :: ctrmask_rec cci i.+1 n' else [::].

Definition ctrmask cp cci := ctrmask_rec cci 0 (ctrmsize cp).

Lemma size_ctrmask cp cci : size (ctrmask cp cci) = ctrmsize cp.
Proof. by rewrite /ctrmask; elim: (ctrmsize cp) 0 => //= *; congr _.+1. Qed.

Fixpoint ctrenum (cp : cprog) : seq (cpmap cp) :=
  match cp with
  | CpR _ :: cp' => ctrenum cp'
  | CpY :: cp' => let G := cpmap cp' in
    if cp' is [::] then [::] else map (icpY G) (node G :: ctrenum cp')
  | CpH :: cp' => let G := cpmap cp' in
    face (ecpH G) :: map (icpH G) [:: node G, G : G & ctrenum cp']
  | _ => [::]
  end.

Lemma size_ctrenum cp : size (ctrenum cp) = ctrmsize cp.
Proof.
elim: cp => [|[n||||||] cp IHcp] //=; rewrite -{}IHcp ?size_map //.
by case: cp => //= *; rewrite size_map.
Qed.

Lemma insertE_icpY (G : hypermap) (x : G) p :
  insertE (map (icpY x) p) = map (icpY x) (insertE p).
Proof. by elim: p => // *; do ?congr (_ :: _). Qed.

Lemma insertE_icpH (G : hypermap) (x : G) p :
  insertE (map (icpH x) p) = map (icpH x) (insertE p).
Proof. by elim: p => // *; do ?congr (_ :: _). Qed.

Lemma uniq_ctrenum cp :
  config_prog cp -> uniq (insertE (cat (cpring (cpmap cp)) (ctrenum cp))).
Proof.
elim: cp => //=; case=> // [n||] cp IHcp.
- move/IHcp=> {IHcp}; apply: etrans; set G := cpmap cp.
  rewrite cpring_ecpR /rot !insertE_cat -catA uniq_catCA catA /=.
  by rewrite -insertE_cat cat_take_drop.
- rewrite cpring_ecpY; case Dcp: cp => [|s cp']; first by rewrite cpring0.
  rewrite -{s cp'}Dcp; set G := cpmap cp => /IHcp{IHcp} IHcp.
  rewrite 2!cat_cons (insertE_cat [:: _; _]) -map_cons -map_cat.
  rewrite insertE_icpY cat_uniq has_map has_pred0 !andTb.
  rewrite (map_inj_uniq (@icpY_inj G G)) -cat1s !insertE_cat uniq_catCA.
  by rewrite -!insertE_cat catA -[h in h ++ _]head_cpring.
move=> cp_ok; move/(_ cp_ok): IHcp.
have:= cpmap_proper (config_prog_cubic cp_ok); set G := cpmap cp => Ggt1 IHcp.
rewrite (cpring_ecpH Ggt1) insertE_cat [p in _ ++ p](insertE_cat [:: _]).
rewrite uniq_catCA (insertE_cat [:: _; _]) -catA -insertE_cat catA.
rewrite -!map_cons -map_cat insertE_icpH [node _]/= if_neg [_ == _]/= nodeK.
rewrite (negPf Ggt1) cat_uniq has_map has_pred0 (map_inj_uniq (@icpH_inj G G)).
rewrite andTb insertE_cat (insertE_cat [:: _; _]) uniq_catCA -!insertE_cat.
by rewrite catA -[h in h ++ _]head_proper_cpring.
Qed.

Let nsp (b : bool) := if b then orb else andb.

Fixpoint cfctr (mr mc : bitseq) (cp : cprog) {struct cp} : option cprog :=
  match cp, mr, mc with
  | CpR i :: cp', _, _ =>
    let mr' := rotr i mr in
    if cfctr mr' mc cp' is Some cpc then
      Some (CpR (count negb (take i mr')) :: cpc)
    else None
  | [:: CpY], [:: b1, b2, b3 & _], _ =>
    if nsp b1 b2 b3 then None else
    Some (if b1 || (b2 || b3) then [::] else [:: CpY])
  | CpY :: cp', [:: b1, b2 & mr'], b3 :: mc' =>
    if nsp b1 b2 b3 then None else
    if cfctr (b3 :: mr') mc' cp' is Some cpc then
      Some (if b1 || b2 then cpc else (if b3 then CpU else CpY) :: cpc)
    else None
  | CpH :: cp', [:: b1, b2 & mr'], [:: b3, b4, b5 & mc'] =>
    if nsp b3 b1 b4 || nsp b3 b2 b5 then None else
    if [&& b1, b2 & all id mr'] then None else
    if cfctr [:: b4, b5 & mr'] mc' cp' is Some cpc then
      Some (if b3 then cpc else
            if b1 then
               if b2 then CpA :: cpc else
               if b5 then cpc else CpK :: cpc
             else
               if b2 then (if b4 then cpc else CpK :: cpc) else
               if b4 then (if b5 then CpU :: cpc else CpY :: cpc) else
               if b5 then CpY :: cpc else CpH :: cpc)
     else None
  | _, _, _ => None
  end.

Lemma cfctr_config_prog mr mc cp : cfctr mr mc cp ==> config_prog cp.
Proof.
elim: cp mr mc => //=; case=> // [n||] cp IHcp mr mc.
- by case: (cfctr _ mc cp) (IHcp (rotr n mr) mc).
- case Dcp: cp mr => [|s cp'] [|b1 [|b2 mr]] //.
    case: mr => [|b3 mr]; last by case: ifP.
    by case: mc => [|b3 mc] //; case: ifP.
  rewrite -{}Dcp; case: mc => [|b3 mc] //; case: ifP => // _.
  by case: (cfctr _ mc cp) (IHcp (b3 :: mr) mc).
case: mr mc => [|b1 [|b2 mr]] [|b3 [|b4 [|b5 mc]]] //=.
by do 2!case: ifP => // _; case: (cfctr _ mc cp) (IHcp [:: b4, b5 & mr] mc).
Qed.

Lemma cfctr_correct mr mc cp (G := cpmap cp) (r := cpring G) :
    size mr = cprsize cp -> size mc = ctrmsize cp ->
    let cc := mask mr r ++ mask mc (ctrenum cp) in
    forall k : G -> color, cc_coloring cc k ->
  if cfctr mr mc cp is Some cpc then
    let r' := cpring (cpmap cpc) in
    exists2 k', coloring k' & map k' r' = map k (mask (map negb mr) r)
  else True.
Proof.
have has_mask2_F T (a : pred T) p1 p2 m1 m2 :
  ~~ has a (p1 ++ p2) -> has a (mask m1 p1 ++ mask m2 p2) = false.
- by apply: contraNF; rewrite !has_cat => /orP[]/has_mask->; rewrite ?orbT.
rewrite {}/r {}/G; elim: cp => // s cp IHcp in mr mc *.
case Dcpc: (cfctr mr mc _) (cfctr_config_prog mr mc (s :: cp)) => // [cpc].
case: s => // [n||] in Dcpc *; rewrite implyTb => cp_ok Emr Emc;
  have cpQ := config_prog_cubic cp_ok; rewrite /= in cpQ Dcpc Emr Emc;
  move: IHcp (cpmap_plain cpQ) (cpmap_proper cpQ);
  rewrite [cpmap (_ :: _)]/=; set G := cpmap cp => IHcp plainG ntG.
- rewrite cpring_ecpR; rewrite -(size_rotr n) in Emr.
  move=> k [kE kF]; have{IHcp} := IHcp _ _ Emr Emc k.
  case: (cfctr _ mc cp) cpc Dcpc => // [cpc] _ [<-].
  rewrite [cpmap (_ :: _)]/=; set Gc := cpmap cpc.
  case=> [|k' k'col Ek']; first split=> // x.
    rewrite kE !(mem_insertE plainG); apply: {x}eq_has_r => x.
    rewrite !mem_cat; congr (_ || _); rewrite -{1}(rotrK n mr).
    by apply: mem_mask_rot; rewrite Emr -size_ring_cpmap.
  exists k'; rewrite // cpring_ecpR -{3}(rotrK n mr) 2!map_rot {}Ek' mask_rot.
    by rewrite map_rot -map_take count_map.
  by rewrite size_map size_ring_cpmap.
- rewrite /G.
  case Dcp: cp mc mr Emc Emr Dcpc => [|s cp'] [|b3 mc] [|b1 [|b2 mr]] //.
    case: mr {cp Dcp G cp_ok cpQ IHcp plainG ntG} => [|b3 [|b4 mr]] // _ _.
    set G := cpmap [::]; case: ifP => // b123 [<-] {cpc}; rewrite cpring_ecpY.
    case: b1 b2 b3 b123 => [] [] // [] // _; rewrite cpring0 -/G => k [kE kF].
    - exists (k \o icpY G).
        by split=> y; [case: y (kE (icpY G y)) | case: y; apply/eqP].
      congr (_ :: _); have:= kE (node (ecpY G)).
      by rewrite !inE /= -(eqcP (kF _)) => /eqP->; rewrite -(eqcP (kF _)).
    - exists (k \o icpY G).
        by split=> y; [case: y (kE (icpY G y)) | case: y; apply/eqP].
      by congr (_ :: _); rewrite /= -(eqcP (kF _)).
    - exists (fun y => k (if y then ecpY G : ecpY G else node (ecpY G))) => //.
      split=> y /=; last by case: y; apply/eqP.
      have:= kE (node (ecpY G)); rewrite inE -(eqcP (kF _)) nodeK.
      by case: y => //; rewrite eq_sym.
    by rewrite cpring_ecpY cpring0; exists k.
  rewrite -Dcp cpring_ecpY ![size _ = _]/= -/G => [] [Emc] [Emr].
  have Ecp: ctrenum (CpY :: cp) = map (icpY G) (node G :: ctrenum cp).
    by rewrite /= /G Dcp.
  case: ifP =>  // b123; have plainGX: plain (ecpY G) := plain_ecpY G plainG.
  case: (cfctr _ mc cp) {IHcp Emr}(IHcp (b3 :: mr) mc Emr Emc) => //.
  move: cpc => _ cpc IHcp [<-] k [kE kF]; pose h := k \o icpY G.
  have hF: invariant face h =1 G.
    move=> x; apply/eqP; apply: (fconnect_invariant kF).
    by rewrite cface_icpY cfaceC fconnect1.
  have hE: invariant edge h
             =i insertE (mask (b3 :: mr) (cpring G) ++ mask mc (ctrenum cp)).
  - move=> x; rewrite inE /h /= icpY_edge; apply: (etrans (kE _)).
    rewrite !mem_insertE // {2}head_cpring Ecp.
    rewrite (eq_has (plain_orbit plainG x)) (eq_has (plain_orbit plainGX _)).
    rewrite !has_cat -icpY_edge map_cons !has_mask_cons !andbF !orFb.
    by rewrite orbCA -!orbA; congr (_ || _); rewrite -!map_mask !has_map.
  case: {IHcp}(IHcp h) {Emc}; first by split.
  set Gc := cpmap cpc => h' h'col Eh.
  have{h'col} [[h'E h'F] ntGc] := (h'col, coloring_proper_cpring Gc h'col).
  case: ifP => b12; rewrite -/Gc.
    exists h' => //; rewrite {h' hE h'E h'F}Eh /behead head_cpring /h.
    rewrite !map_mask map_comp !map_cons -/G.
    rewrite -(fconnect_invariant kF (cface_node_ecpY G)).
    case: b1 b2 b3 b12 b123 kE => [] [] [] // _ _ kE; congr (_ :: _).
    have:= etrans (kE _) (mem_head _ _).
    by rewrite inE -(eqcP (kF _)) nodeK => /eqP.
  have hEr: all (invariant edge h) (mask (b3 :: mr) (cpring G)).
    apply/allP=> x rGx; rewrite [invariant _ _ _]hE mem_insertE //.
    by apply/hasP; exists x; rewrite ?connect0 // mem_cat rGx.
  have nGN'r: fpath (finv node) (node G) (behead (cpring G)).
    move: (cycle_rev_cpring G); rewrite head_cpring lastI rev_rcons -lastI.
    by rewrite (cycle_path (G : G)) /= -(fpath_finv nodeI); case/andP.
  have h'nGc: h' (node Gc) = h (node G).
    move: hEr Eh {hE kE}; rewrite head_cpring (head_cpring Gc).
    elim: {mr}(b3 :: mr) (node G) (behead _) nGN'r => // [b mr IHcp].
    case: b => [x [|y p] | x p _ _ [Dx]] //=; first by case mr.
    case/andP=> /eqP Dy yN'p /andP[/eqcP <-].
    by rewrite -(eqcP (hF _)) -(f_finv nodeI x) nodeK Dy; apply: IHcp.
  case: b1 b2 b3 b12 {b123} => [] [] [] // _ in Eh kE hE hEr *.
    pose k' u := oapp h' (k (ecpY G)) [pick x | cface u (icpU Gc x)].
    have k'F: invariant face k' =1 ecpU Gc.
      by move=> u; apply/eqP; congr oapp; apply: eq_pick => x; rewrite -cface1.
     have Ek' x: k' (icpU Gc x) = h' x.
      rewrite /k'; case: pickP => [y | /(_ x)/idP[]//].
      by rewrite cface_icpU cfaceC => /(fconnect_invariant h'F).
    have k'X: k' (ecpU Gc) = k (ecpY G).
      by rewrite /k'; case: pickP => // y; rewrite cface_ecpU.
    have k'nX: k' (node (ecpU Gc)) = k (node (ecpY G)).
      rewrite (fconnect_invariant kF (cface_node_ecpY _)).
      by rewrite -(eqcP (k'F _)) /= Ek' h'nGc.
    exists k'; last first.
      rewrite [cpmap _]/= -/Gc cpring_ecpU 4!map_cons {1 2}/negb k'nX.
      rewrite !mask_cons !map_cat !map_nseq k'X; congr [::_, _ & _].
      by rewrite -map_mask -!map_comp -/h (eq_map Ek') Eh head_cpring.
    suffices k'EX: invariant edge k' (ecpU Gc) = false.
      split=> // -[||x] //; first by rewrite inE eq_sym.
      rewrite -/cpmap -/Gc in x *; rewrite -/(icpU Gc x) inE -(icpU_edge Gc).
      by rewrite !Ek'; apply: h'E.
    apply/eqP => k'eX; have/esym/eqP/idPn[] := kE (node (ecpY G)).
    rewrite inE -k'nX -(eqcP (kF _)) nodeK -k'X -k'eX eqxx eqb_id.
    rewrite mem_insertE // mask_cons has_mask2_F // -mem_insertE //.
    have:= uniq_ctrenum cp_ok; rewrite [cpmap _]/= -/G cpring_ecpY.
    by rewrite -cat1s -catA insertE_cat cons_uniq inE => /andP[/norP[]].
  pose k' u := oapp h' (k (ecpY G)) [pick x | cface u (icpY Gc x)].
  have k'F: invariant face k' =1 ecpY Gc.
    by move=> u; apply/eqP; congr oapp; apply: eq_pick => x; rewrite -cface1.
  have Ek' x: k' (icpY Gc x) = h' x.
    rewrite /k' -/Gc; case: pickP => [y | /(_ x)/idP[]//].
    by rewrite cface_icpY cfaceC => /(fconnect_invariant h'F).
  have k'X: k' (ecpY Gc) = k (ecpY G).
    by rewrite /k' -/Gc; case: pickP => // y; rewrite cface_ecpY.
  have k'nX: k' (node (ecpY Gc)) = k (node (ecpY G)).
    rewrite (fconnect_invariant k'F (cface_node_ecpY _)) Ek' h'nGc.
    by rewrite (fconnect_invariant kF (cface_node_ecpY _)).
  have h'Gc: h' Gc = h G.
    rewrite head_proper_cpring // in Eh.
    move: nGN'r Eh hEr {hE kE}; rewrite head_proper_cpring //=.
    case/andP=> [_ GN'r] [_ Eh]; move: GN'r Eh.
    elim: mr (G : G) (drop 2 _) => // [b mr IHmr].
    case: b => [x [|y p] | x p _ [Dx]] //=; first by case mr.
    case/andP=> /eqP Dy yN'r Eh /andP[/eqcP <-]; move: Eh.
    by rewrite -(eqcP (hF _)) -(f_finv nodeI x) nodeK Dy; apply: IHmr.
  exists k'; last first.
    rewrite [cpmap _]/= -/Gc !cpring_ecpY 4!map_cons {1 2}/negb.
    rewrite k'nX !mask_cons !map_cat !map_nseq k'X; congr [:: _, _ & _].
    rewrite -map_mask -!map_comp -/h (eq_map Ek').
    by move: Eh; rewrite head_cpring (head_cpring G); case.
  suffices k'EX u: cface u (ecpY Gc) -> invariant edge k' u = false.
    split; rewrite // [cpmap _]/= -/Gc => u.
    have [[x uFx] | XFu] := fband_icpY u; last first.
      by apply: k'EX; rewrite cfaceC.
    have [[y euFy] | XFeu] := fband_icpY (edge u); last first.
      have eeu: edge (edge u) = u.
        by move: XFeu {uFx}; rewrite cface_ecpY; case: u => [||[||z]].
      by rewrite inE eq_sym -{1}eeu [_ == _]k'EX // cfaceC.
    rewrite inE (fconnect_invariant k'F uFx) (fconnect_invariant k'F euFy).
    have: adj x y by rewrite -(adj_icpY Gc) -(adjF uFx) -(adjFr euFy) adjE.
    case/adjP=> z xFz zRy; rewrite !Ek' (fconnect_invariant h'F xFz).
    by rewrite -(fconnect_invariant h'F zRy); apply: h'E.
  move=> uFX; rewrite inE (fconnect_invariant k'F uFX) k'X.
  have{uFX}: adj (ecpY Gc) (edge u) by rewrite -(adjF uFX) adjE.
  rewrite (adj_ecpY ntGc) unfold_in => /hasP[_ /mapP[y GcNy ->] euFy].
  rewrite {u euFy}(fconnect_invariant k'F euFy) Ek'.
  move: (uniq_ctrenum cp_ok) kE GcNy; rewrite [cpmap _]/= -/G cpring_ecpY.
  move Dx: (ecpY G : ecpY G) {mc hE}(_ :: mc) (ctrenum _) => x mc p.
  move Dnx: (node x) => nx /= /and4P[nxE'p _ xE'p _]; move: nxE'p xE'p.
  rewrite !inE !negb_or !andbA => /andP[_].
  rewrite !(mem_insertE plainGX) => nxE'p /andP[_ xE'p] kE /pred2P[]->{y}.
    rewrite -[x]nodeK Dnx h'nGc /h eq_sym.
    rewrite (eqcP (kF _)) /= -(fconnect_invariant kF (cface_node_ecpY _)).
    by rewrite Dx Dnx [_ == _](kE nx) (mem_insertE plainGX) has_mask2_F.
  have <-: k (edge x) = h' Gc.
    by rewrite -(eqcP (kF _)) h'Gc -Dx /= nodeK (negPf ntG).
  by rewrite [_ == _](kE x) (mem_insertE plainGX) has_mask2_F.
case: mr mc Emc Emr Dcpc => [|b1 [|b2 mr]] // [|b3 [|b4 [|b5 mc]]] //.
case: ifP => // b314_325; case: ifP => // b12mr [Emc] Emr.
rewrite /= in Emc Emr.
have{IHcp}:= IHcp [:: b4, b5 & mr] mc Emr Emc.
case: (cfctr _ mc cp) cpc => // [cpc] _ IHcp [<-] k [kE kF].
pose h := k \o icpH G.
have hF: invariant face h =1 G.
  by move=> x; apply/eqP/(fconnect_invariant kF); rewrite cface_icpH -cface1.
have plainGX : plain (ecpH G) := plain_ecpH G plainG.
have hE: invariant edge h
          =i insertE (mask [:: b4, b5 & mr] (cpring G) ++ mask mc (ctrenum cp)).
- move=> x; rewrite inE /h /comp icpH_edge [_ == _]kE !mem_insertE //.
  rewrite cpring_ecpH // {2}head_proper_cpring //.
  rewrite (eq_has (plain_orbit plainG x)) (eq_has (plain_orbit plainGX _)).
  rewrite !has_cat -icpH_edge [ctrenum _]/= !has_mask_cons.
  rewrite !andbF !orFb orbCA -!orbA; congr 1 (_ || _).
  rewrite [node _]/= /long_cpring [~~ _]/= nodeK (negPf ntG) andbF orFb orbCA.
  by congr [|| _, _ | _]; rewrite -map_mask has_map.
have{IHcp} [//|h' h'col Eh'] := IHcp h; set Gc := cpmap cpc in h' h'col Eh' *.
have{h'col} [[h'E h'F] ntGc] := (h'col, coloring_proper_cpring Gc h'col).
have kefX: k (edge (face (ecpH G))) = h G.
  apply: (fconnect_invariant kF); apply connect1; apply/eqP.
  by rewrite /= nodeK (negPf ntG).
have hEr: all (invariant edge h) (mask [:: b4, b5 & mr] (cpring G)).
  apply/allP=> x rGx; rewrite [invariant _ _ _]hE mem_insertE //.
  by apply/hasP; exists x; rewrite ?connect0 // mem_cat rGx.
have nGN'r: fpath (finv node) (node G) (rcons (behead (cpring G)) (node G)).
  rewrite (fpath_finv nodeI) last_rcons belast_rcons -head_cpring.
  have:= cycle_rev_cpring G.
  by rewrite head_cpring (cycle_path (G : G)) rev_cons last_rcons.
case: b3 b314_325 hE hEr kE Eh'.
  case: b1 b2 b4 b5 {b12mr} => [] // [] // [] [] // _ _ _ kE Eh'.
  exists h'; rewrite // -/Gc Eh' head_proper_cpring // cpring_ecpH //.
  rewrite !map_mask !map_cons -map_comp.
  rewrite (fconnect_invariant kF (cface_node_ecpH ntG)) -/(h (node G)).
  congr [:: _, _ & _]; apply: eqP; rewrite -(eqcP (kF _)) -kefX [_ == _]kE.
  by rewrite insertE_cat mem_cat mem_head orbT.
case b12: (b1 && b2).
  case: b1 b2 b12 b12mr b4 b5 => [] [] //  _ b_mr [] // [] // _ hE hEr kE Eh'.
  have longGc: long_cpring Gc.
    rewrite size_long_cpring -(size_map h') Eh'; move/eqP: Emr b_mr.
    rewrite -size_ring_cpmap; case: (cpring G) => [|x0 [|x1 p]] //= {x0 x1}.
    rewrite !eqSS => /eqP eq_sz; rewrite !(size_mask, size_map) //.
    by rewrite !ltnS count_map -has_count has_predC => ->.
  rewrite (head_proper_cpring ntG) head_proper_cpring //= in Eh'.
  have{Eh'} [h'nGc h'Gc Eh'] := Eh'.
  have h'feGc: h' (face (edge Gc)) = h (face (edge G)).
    rewrite head_long_cpring //= in Eh'; move: nGN'r Eh' hEr.
    rewrite head_proper_cpring //= drop0 => /andP[_].
    elim: (mr) {-2}(G : G) (drop 2 _) => [|b m IHm] // x [|y p] //=.
    case/andP=> /eqP Dy yN'p; rewrite -(finv_eq_can nodeK x) Dy.
    case: b => [/= Eh' | []//] /andP[/eqcP <-] hEp.
    by rewrite -(eqcP (hF _)) (IHm _ _ yN'p).
  have Eh'A: h' (node Gc) = h' (face (edge Gc)).
    rewrite h'nGc h'feGc (eqcP (hF (edge G))).
    rewrite /h /= -(fconnect_invariant kF (cface_node_ecpH ntG)).
    transitivity (k (face (edge (node (ecpH G))))); apply: eqP.
      by rewrite eq_sym (eqcP (kF _)) [_ == _]kE head_cpring mem_head.
    rewrite nodeK eq_sym -(eqcP (kF _)) /= nodeK (negPf ntG) eqxx.
    by rewrite [_ == _](kE (ecpH G)) cpring_ecpH // 2?mem_behead ?mem_head.
  have h'FA: invariant (@face (ecpA Gc)) h' =1 Gc.
    rewrite /invariant /= /ecpA_face => x; rewrite inE.
    case: ifP => _; first exact: h'F; case: (x =P _) => [Dx|_].
      by rewrite -(eqcP (h'F x)) Dx -Eh'A eqxx.
    case: (face x =P _) => [Dfx | _]; last exact: h'F.
    by rewrite -(eqcP (h'F x)) Dfx -Eh'A eqxx.
  exists h'; last first.
    rewrite [cpmap _]/= -/Gc cpring_ecpA longGc cpring_ecpH //=.
    by rewrite -map_mask -map_comp; rewrite drop_behead in Eh'.
  split; rewrite //= /ecpA_edge /= -/Gc => x /=.
  case: ifP => _; first exact: h'E.
  case: (x =P _) => [Dx | _].
    by rewrite -(eqcP (h'F _)) nodeK Eh'A (eqcP (h'F _)) Dx; apply: h'E.
  case: (x =P _) => [Dx | _]; last exact: h'E.
  by rewrite -(eqcP (h'F _)) -Eh'A -(canLR nodeK Dx) (eqcP (h'F _)); apply: h'E.
case: b1 b2 {b12mr}b12 b4 b5 => [] [] // _ [] [] // _;
  rewrite [cpmap _]/= -/Gc => hE hEr kE Eh'.
- exists h'; rewrite // Eh' (head_proper_cpring ntG) cpring_ecpH //.
  rewrite !map_mask !map_cons -map_comp; congr (_ :: _).
  apply/esym/eqP; rewrite /h /= -(fconnect_invariant kF (cface_node_ecpH ntG)).
  rewrite -[y in k y](nodeK (ecpH G)) (eqcP (kF _)) [_ == _]kE.
  by rewrite head_cpring mem_head.
- pose k' u := oapp h' Color0 [pick x | cface u (icpK Gc x)].
  have k'F: invariant face k' =1 ecpK Gc.
    by move=> u; apply/eqP; congr oapp; apply: eq_pick => x; rewrite -cface1.
  have Ek' x: k' (icpK _ x) = h' x.
    rewrite /k' -/Gc; case: pickP => [y | /(_ x)/idP[]//].
    by rewrite cface_icpK cfaceC => /(fconnect_invariant h'F).
  rewrite (head_proper_cpring ntG) (head_proper_cpring ntGc) /= in Eh'.
  have{Eh'} [hnGc hGc Eh'] := Eh'.
  have kX: k (ecpH G) = h' (node Gc).
    apply: eqP; rewrite hnGc -(nodeK (ecpH G)) (eqcP (kF _)).
    rewrite /h /= -(fconnect_invariant kF (cface_node_ecpH ntG)) [_ == _]kE.
    by rewrite head_cpring mem_head.
  exists k'; last first.
    rewrite cpring_ecpK cpring_ecpH // map_mask !map_cons -!map_comp.
    rewrite (eq_map Ek') Eh' map_mask kX; congr (_ :: _).
    by rewrite (fconnect_invariant k'F (cface_node_ecpK _)) Ek'.
  set x0 : ecpK Gc := ecpN (ecpR' Gc).
  suffices k'EX: invariant edge k' x0 = false.
    split=> // [] [||x] //; first by rewrite inE eq_sym.
    by rewrite -[Icp x]/(icpK Gc x) inE -icpK_edge !Ek'; apply: h'E.
  rewrite inE; have <-: h' (face (edge Gc)) = k' (edge x0).
    rewrite (eqcP (h'F _)) -Ek'; apply/(fconnect_invariant k'F)/connect1/eqP.
    by rewrite /ecpK /x0 ecpR'_eq /= nodeK eqxx.
  have <-: k (ecpH G) = k' x0.
    rewrite kX -Ek'; apply/esym/(fconnect_invariant k'F)/connect1/eqP.
    by rewrite /ecpK /x0 ecpR'_eq.
  have <-: (h (face (edge G)) = h' (face (edge Gc))).
    move/eqP: Emr; move: nGN'r hEr; rewrite -size_ring_cpmap -/G.
    rewrite (head_proper_cpring ntG) /= !eqSS => /andP[_].
    move: (mr) {-2}(G : G) (drop 2 (cpring G)) Eh'.
    elim=> [|b m IHm] x [|y p] //= Eh' /andP[/eqP/(canRL (f_finv nodeI))->].
      suffices /eqP->: long_cpring Gc = false by rewrite nodeK.
      by rewrite size_long_cpring -(size_map h') head_proper_cpring //= Eh'.
    case: b Eh' => /= Eh' yN'Hp.
      by rewrite nodeK => /andP[/eqP<-]; rewrite -(eqcP (hF _)); apply: IHm.
    have longGc: long_cpring Gc.
      by rewrite size_long_cpring -(size_map h') head_proper_cpring //= Eh'.
    by rewrite head_long_cpring // in Eh'; rewrite nodeK; case: Eh'.
  have <-: k (edge (ecpH G)) = h (face (edge G)).
    rewrite (eqcP (hF _)); apply/esym/(fconnect_invariant kF)/connect1/eqP.
    by rewrite /= nodeK (negPf ntG) eqxx.
  have:= uniq_ctrenum cp_ok; rewrite [_ == _]kE [cpmap _]/= -/G cpring_ecpH //.
  rewrite 2!cat_cons (insertE_cat [:: _; _]) (insertE_cat [:: _]) -catA.
  rewrite uniq_catCA -insertE_cat catA cat1s cons_uniq inE orFb !mem_insertE //.
  by rewrite 2!mask_cons cat0s -mask_cons => /andP[/has_mask2_F->].
- exists h'; rewrite // Eh' (head_proper_cpring ntG) cpring_ecpH //.
  rewrite !map_mask !map_cons -map_comp; congr (_ :: _).
  apply/eqP; rewrite (fconnect_invariant kF (cface_node_ecpH ntG)).
  by rewrite -{1}(nodeK G) (eqcP (hF _)) [_ == _]hE head_cpring mem_head.
- pose k' u := oapp h' Color0 [pick x | cface u (icpK Gc x)].
  have k'F: invariant face k' =1 ecpK Gc.
    by move=> u; apply/eqP; congr oapp; apply/eq_pick=> x; rewrite -cface1.
  have Ek' x: k' (icpK _ x) = h' x.
    rewrite /k' -/Gc; case: pickP => [y | /(_ x)/idP[]//].
    by rewrite cface_icpK cfaceC => /(fconnect_invariant h'F).
  rewrite (head_proper_cpring ntG) (head_proper_cpring ntGc) /= in Eh'.
  have{Eh'} [h'nGc h'Gc Eh'] := Eh'.
  exists k'; last first.
    rewrite cpring_ecpK cpring_ecpH // map_mask !map_cons -!map_comp.
    rewrite (eq_map Ek') Eh' map_mask; congr (_ :: _).
    rewrite (fconnect_invariant k'F (cface_node_ecpK _)) Ek'.
    by rewrite (fconnect_invariant kF (cface_node_ecpH ntG)).
  set x0 : ecpK Gc := ecpN (ecpR' Gc).
  suffices k'EX: invariant edge k' x0 = false.
    split=> // -[||x] //; first by rewrite inE eq_sym.
    by rewrite -[Icp x]/(icpK Gc x) inE -icpK_edge !Ek' [_ == _]h'E.
  rewrite inE; have <-: h' (face (edge Gc)) = k' (edge x0).
    rewrite (eqcP (h'F _)) -Ek'; apply/(fconnect_invariant k'F)/connect1/eqP.
    by rewrite /ecpK /x0 ecpR'_eq /= nodeK eqxx.
  have <-: h (face (edge G)) = h' (face (edge Gc)).
    move/eqP: Emr; move: nGN'r hEr; rewrite -size_ring_cpmap -/G.
    rewrite (head_proper_cpring ntG) /= !eqSS => /andP[_].
    move: (mr) {-2}(G : G) (drop 2 (cpring G)) Eh'.
    elim=> [|b m IHm] x [|y p] //= Eh' /andP[/eqP/(canRL (f_finv nodeI))->].
      suffices /eqP->: long_cpring Gc = false by rewrite nodeK.
      by rewrite size_long_cpring -(size_map h') head_proper_cpring //= Eh'.
    case: b Eh' => /= Eh' yN'p.
      by rewrite nodeK -(eqcP (hF _)) => /andP[/eqP<-]; apply: IHm.
    have longGc: (long_cpring Gc).
      by rewrite size_long_cpring -(size_map h') head_proper_cpring //= Eh'.
    by rewrite nodeK head_long_cpring // in Eh' *; case: Eh'.
  have <-: k (edge (ecpH G)) = h (face (edge G)).
    rewrite (eqcP (hF _)); apply/esym/(fconnect_invariant kF)/connect1/eqP.
    by rewrite /= nodeK (negPf ntG) eqxx.
  have <-: k (node (ecpH G)) = k' x0.
    rewrite (fconnect_invariant kF (cface_node_ecpH ntG)) -[k _]/(h (node G)).
    rewrite -h'nGc -Ek'; apply/esym/(fconnect_invariant k'F)/connect1/eqP.
    by rewrite /ecpK /x0 ecpR'_eq.
  have <-: k (edge (node (ecpH G))) = k (edge (ecpH G)).
    rewrite -(eqcP (kF _)) nodeK; apply/esym/eqP.
    by rewrite [_ == _]kE cpring_ecpH ?mem_head.
  have:= uniq_ctrenum cp_ok; rewrite [_ == _]kE [cpmap _]/= -/G cpring_ecpH //.
  rewrite mask_cons cat0s cat_cons (insertE_cat [:: _]) cons_uniq inE andbC.
  rewrite !mem_insertE // => /andP[_] /norP[_]; apply: contraNF.
  case/hasP=> [z p_z nXEz]; apply/hasP; exists z => {nXEz}//.
  by move: p_z; rewrite !mem_cat => /orP[]/mem_mask->; rewrite ?orbT.
- pose k' u := oapp h' (k (ecpH G)) [pick x | cface u (icpU Gc x)].
  have k'F: invariant face k' =1 ecpU Gc.
    by move=> u; apply/eqP; congr oapp; apply/eq_pick=> x; rewrite -cface1.
  have Ek' x: k' (icpU Gc x) = h' x.
    rewrite /k' -/Gc; case: pickP => [y | /(_ x)/idP[]//].
    by rewrite cface_icpU cfaceC => /(fconnect_invariant h'F).
  have k'X: k' (ecpU Gc) = k (ecpH G).
    by rewrite /k'; case: pickP => // y; rewrite cface_ecpU.
  rewrite (head_proper_cpring ntG) head_cpring /= in Eh'.
  have k'eX: h (face (edge G)) = k' (edge (ecpU Gc)).
    have <-: h' (node Gc) = k' (edge (ecpU Gc)) by rewrite -(eqcP (k'F _)) -Ek'.
    move: nGN'r hEr; rewrite (head_proper_cpring ntG) /= => /andP[_ GN'r].
    case/and3P=> _ _; move: (mr) {-2}(G : G) (drop 2 (cpring G)) Eh' GN'r.
    elim=> [|b m IHm] x [|y p] //= Eh' /andP[/eqP/(canRL (f_finv nodeI))->].
    rewrite nodeK; case: b Eh' => [|] /= Eh' yN'p; last by case: Eh'.
    by case/andP=> /eqcP<-; rewrite -(eqcP (hF _)); apply: IHm.
  exists k'; last first.
    rewrite cpring_ecpU cpring_ecpH // map_mask !map_cons -!map_comp -/cpmap.
    rewrite (eq_map Ek') head_cpring map_cons Eh' k'X map_mask; congr (_ :: _).
    rewrite (fconnect_invariant kF (cface_node_ecpH ntG)) -[k _]/(h (node G)).
    apply: (etrans (esym k'eX)); transitivity (h G); apply: eqP.
      by rewrite (eqcP (hF _)) [_ == _]hE head_proper_cpring // !inE eqxx !orbT.
    by rewrite -{1}(nodeK G) (eqcP (hF _)) [_ == _]hE head_cpring mem_head.
  suffices k'EX: invariant edge k' (ecpU Gc) = false.
    split=> // [] [||x] //; first by rewrite inE eq_sym.
    by rewrite -[Icp x]/(icpU Gc x) inE -icpU_edge !Ek' [_ == _]h'E.
  rewrite inE k'X -k'eX.
  have <-: k (edge (ecpH G)) = h (face (edge G)).
    rewrite (eqcP (hF _)); apply/esym/(fconnect_invariant kF)/connect1/eqP.
    by rewrite /= nodeK (negPf ntG) eqxx.
  have:= uniq_ctrenum cp_ok; rewrite [_ == _]kE [cpmap _]/= -/G cpring_ecpH //.
  rewrite 2!mask_cons !cat0s 2!cat_cons (insertE_cat [:: _; _]) 3!cons_uniq.
  by case/and4P=> _ _; rewrite inE !mem_insertE // => /has_mask2_F->.
- pose k' u := oapp h' (k (ecpH G)) [pick x | cface u (icpY Gc x)].
  have k'F: invariant face k' =1 ecpY Gc.
    by move=> u; apply/eqP; congr oapp; apply/eq_pick=> x; rewrite -cface1.
  have Ek' x: k' (icpY Gc x) = h' x.
    rewrite /k' -/Gc; case: pickP => [y | /(_ x)/idP[]//].
    by rewrite cface_icpY cfaceC => /(fconnect_invariant h'F).
  have k'X: k' (ecpY Gc) = k (ecpH G).
    by rewrite /k'; case: pickP => // y; rewrite cface_ecpY.
  rewrite (head_proper_cpring ntG) head_cpring /= in Eh'.
  have{Eh'} [h'nGc Eh'] := Eh'.
  have hnG: h (node G) = h G.
    rewrite -{2}(nodeK G) (eqcP (hF _)); apply/esym/eqP.
    by rewrite [_ == _]hE head_cpring mem_head.
  have k'nX: k' (node (ecpY Gc)) = k (node (ecpH G)).
    rewrite (fconnect_invariant k'F (cface_node_ecpY _)) Ek' h'nGc -hnG.
    by rewrite (fconnect_invariant kF (cface_node_ecpH ntG)).
  have h'Gc: h' Gc = h (face (edge G)).
    rewrite head_proper_cpring //= in Eh'; move: nGN'r hEr {hE kE}.
    rewrite head_proper_cpring //= => /andP[_ GN'r] /andP[_]; move: Eh' GN'r.
    elim: (mr) {-2}(G : G) (drop 2 (cpring G)) => [|b m IHm] x [|y p] //= Eh'.
    case/andP=> /eqP/(canRL (f_finv nodeI))-> yN'p; rewrite nodeK.
    case: b => /= [|[]//] in Eh' * => /andP[/eqP <- /(IHm y)-> //].
    exact/eqP/hF.
  exists k'; last first.
    rewrite [cpmap _]/= cpring_ecpY cpring_ecpH // !map_mask !map_cons.
    by rewrite k'nX k'X -!map_comp (eq_map Ek') Eh' map_mask.
  suffices k'EX u: cface u (ecpY Gc) -> invariant edge k' u = false.
    rewrite [cpmap _]/= -/Gc; split=> // u.
    have [[x uFx] | XFu] := fband_icpY u; last by rewrite k'EX // cfaceC.
    have [[y euFy] | XFeu] := fband_icpY (edge u); last first.
      have eeu: edge (edge u) = u.
        by move: XFeu {uFx}; rewrite cface_ecpY; case: u => [||[||z]].
      by rewrite inE eq_sym -{1}eeu [_ == _]k'EX // cfaceC.
    rewrite inE (fconnect_invariant k'F uFx) (fconnect_invariant k'F euFy) !Ek'.
    have: adj x y by rewrite -(adj_icpY Gc) -(adjF uFx) -(adjFr euFy) adjE.
    case/adjP=> z xFz zRy; rewrite (fconnect_invariant h'F xFz).
    by rewrite -(fconnect_invariant h'F zRy) [_ == _]h'E.
  move=> uFX; rewrite inE (fconnect_invariant k'F uFX) k'X.
  have{uFX}: adj (ecpY Gc) (edge u) by rewrite -(adjF uFX) adjE.
  rewrite (adj_ecpY ntGc) unfold_in => /hasP[_ /mapP[y GcNy ->] euFX].
  rewrite {u euFX}(fconnect_invariant k'F euFX) Ek'.
  move: kE (uniq_ctrenum cp_ok); rewrite [cpmap _]/= -/G cpring_ecpH // => kE.
  rewrite 2!cat_cons (insertE_cat [:: _; _]) cat_uniq has_sym andbCA andbC.
  rewrite -all_predC => /andP[_ /and4P[]]; rewrite 9?(mem_insertE, inE) //.
  move=> rE'nX _ rE'X _; move: GcNy; rewrite !inE => /pred2P[]->.
    rewrite h'nGc -hnG -[h _](fconnect_invariant kF (cface_node_ecpH ntG)).
    rewrite eq_sym -[z in k z]nodeK (eqcP (kF _)) [_ == _]kE 2!mask_cons !cat0s.
    by rewrite mem_insertE // has_mask2_F.
  rewrite h'Gc; have <-: k (edge (ecpH G)) = h (face (edge G)).
    rewrite (eqcP (hF _)); apply/esym/(fconnect_invariant kF)/connect1/eqP.
    by rewrite /= nodeK (negPf ntG) /= eqxx.
  by rewrite [_ == _]kE 2!mask_cons !cat0s mem_insertE // has_mask2_F.
- pose k' u := oapp h' (k (ecpH G)) [pick x | cface u (icpY Gc x)].
  have k'F: invariant face k' =1 ecpY Gc.
    by move=> u; apply/eqP; congr oapp; apply/eq_pick=> x; rewrite -cface1.
  have Ek' x: k' (icpY Gc x) = h' x.
    rewrite /k' -/Gc; case: pickP => [y | /(_ x)/idP[]//].
    by rewrite cface_icpY cfaceC => /(fconnect_invariant h'F).
  have k'X: k' (ecpY Gc) = k (ecpH G).
    by rewrite /k'; case: pickP => // y; rewrite cface_ecpY.
  rewrite (head_proper_cpring ntG) head_cpring /= in Eh'.
  have{Eh'} [h'nGc Eh'] := Eh'.
  have hfeG: h (face (edge G)) = h G.
    by apply/eqP; rewrite (eqcP (hF _)) [_ == _]hE head_proper_cpring ?mem_head.
  have k'nX: k' (node (ecpY Gc)) = k (node (ecpH G)).
    rewrite (fconnect_invariant k'F (cface_node_ecpY _)) Ek' h'nGc.
    by rewrite (fconnect_invariant kF (cface_node_ecpH ntG)).
  have h'Gc: h' Gc = h (face (edge G)).
    rewrite head_proper_cpring //= in Eh'; move: nGN'r hEr {hE kE}.
    rewrite head_proper_cpring //= => /andP[_ GN'r] /andP[_]; move: GN'r Eh'.
    elim: (mr) {-2}(G : G) (drop 2 (cpring G)) => [|b m IHm] x [|y p] //=.
    case/andP=> /eqP/(canRL (f_finv nodeI))-> yN'p; rewrite nodeK.
    by case: b => [? /andP[/eqcP<-]|[]//]; rewrite -(eqcP (hF _)); apply: IHm. 
  exists k'; last first.
    rewrite /cpmap -/cpmap cpring_ecpY cpring_ecpH // !map_mask !map_cons k'nX.
    by rewrite k'X -!map_comp (eq_map Ek') Eh' map_mask.
  suffices k'EX u: cface u (ecpY Gc) -> invariant edge k' u = false.
    rewrite [cpmap _]/= -/Gc; split=> // u.
    have [[x uFx] | XFu] := fband_icpY u; last by apply: k'EX; rewrite cfaceC.
    have [[y euFy] | XFeu] := fband_icpY (edge u); last first.
      have eeu: edge (edge u) = u.
        by move: XFeu {uFx}; rewrite cface_ecpY; case: u => [||[||z]].
      by rewrite inE eq_sym -{1}eeu; apply: k'EX; rewrite cfaceC.
    rewrite inE (fconnect_invariant k'F uFx) (fconnect_invariant k'F euFy) !Ek'.
    have: adj x y by rewrite -(adj_icpY Gc) -(adjF uFx) -(adjFr euFy) adjE.
    case/adjP=> z xFz zRy; rewrite (fconnect_invariant h'F xFz).
    by rewrite -(fconnect_invariant h'F zRy) [_ == _]h'E.
  move=> uFX; rewrite inE (fconnect_invariant k'F uFX) k'X.
  have{uFX}: adj (ecpY Gc) (edge u) by rewrite -(adjF uFX) adjE.
  rewrite (adj_ecpY ntGc) unfold_in => /hasP[ _ /mapP[y GcNy ->] euFX].
  rewrite {u euFX}(fconnect_invariant k'F euFX) Ek'.
  move: kE (uniq_ctrenum cp_ok); rewrite [cpmap _]/= -/G cpring_ecpH //.
  rewrite 2!mask_cons !cat0s 2!cat_cons (insertE_cat [:: _; _]) cat_uniq => kE.
  rewrite has_sym -all_predC andbA andbAC => /andP[_ /and4P[]].
  rewrite 9?(mem_insertE, inE) // => rE'nX _ rE'X _.
  move: GcNy; rewrite !inE => /pred2P[]->.
    rewrite h'nGc -[h _](fconnect_invariant kF (cface_node_ecpH ntG)) eq_sym.
    rewrite -{1}(nodeK (ecpH G)) (eqcP (kF _)) [_ == _]kE mem_insertE //.
    exact: has_mask2_F.
  rewrite h'Gc; have <-: k (edge (ecpH G)) = h (face (edge G)).
    rewrite (eqcP (hF _)); apply/esym/(fconnect_invariant kF)/connect1/eqP.
    by rewrite /= nodeK (negPf ntG) /= eqxx.
  by rewrite [_ == _]kE mem_insertE // has_mask2_F.
pose k' u := oapp h' (k (ecpH G)) [pick x | cface u (icpH Gc x)].
have k'F: invariant face k' =1 ecpH Gc.
  by move=> u; apply/eqP; congr oapp; apply/eq_pick=> x; rewrite -cface1.
have Ek' x: k' (icpH Gc x) = h' x.
  rewrite /k' -/Gc; case: pickP => [y | /(_ x)/idP[]//].
  by rewrite cface_icpH cfaceC => /(fconnect_invariant h'F).
have k'X: k' (ecpH Gc) = k (ecpH G).
  by rewrite /k'; case: pickP => // y; rewrite cface_ecpH.
rewrite (head_proper_cpring ntG) head_proper_cpring //= in Eh'.
have{Eh'} [h'nGc h'Gc Eh'] := Eh'.
have k'nX: k' (node (ecpH Gc)) = k (node (ecpH G)).
  rewrite (fconnect_invariant k'F (cface_node_ecpH ntGc)) Ek' h'nGc.
  by rewrite (fconnect_invariant kF (cface_node_ecpH ntG)).
have h'feGc: h' (face (edge Gc)) = h (face (edge G)).
  move/eqP: Emr; move: nGN'r hEr {hE kE}; rewrite -size_ring_cpmap -/G.
  rewrite head_proper_cpring //= !eqSS => /andP[_].
  elim: (mr) {-2}(G : G) (drop 2 (cpring G)) Eh' => [|b m IHm] x [|y p] //= Eh';
    case/andP=> /eqP/(canRL (f_finv nodeI))-> yN'p; rewrite nodeK.
  - suffices /eqP->: long_cpring Gc = false by rewrite -h'nGc.
    by rewrite size_long_cpring -(size_map h') head_proper_cpring //= Eh'.
  case: b Eh' => /= Eh'.
    by case/andP=> /eqcP=> <-; rewrite -(eqcP (hF _)); apply: IHm.
  have longGc: long_cpring Gc.
    by rewrite size_long_cpring -(size_map h') head_proper_cpring //= Eh'.
  by rewrite (head_long_cpring longGc) in Eh'; case: Eh'.
exists k'; last first.
  rewrite [cpmap _]/= !cpring_ecpH // !map_mask !map_cons.
  by rewrite k'nX k'X -!map_comp (eq_map Ek') Eh' map_mask.
suffices k'EX u: cface u (ecpH Gc) -> invariant edge k' u = false .
  split=> //; rewrite [cpmap _]/= -/Gc => u.
  have [[x uFx] | XFu] := fband_icpH u; last first.
    by apply: k'EX; rewrite cfaceC.
  have [[y euFy] | XFeu] := fband_icpH (edge u); last first.
    have eeu: edge (edge u) = u.
      by move: XFeu {uFx}; rewrite cface_ecpH; case: u => [||[||[||z]]].
    by rewrite inE eq_sym -{1}eeu; apply: k'EX; rewrite cfaceC.
  rewrite inE (fconnect_invariant k'F uFx) (fconnect_invariant k'F euFy) !Ek'.
  have: adj x y by rewrite -(adj_icpH Gc) -(adjF uFx) -(adjFr euFy) adjE.
  case/adjP=> z xFz zRy; rewrite (fconnect_invariant h'F xFz).
  by rewrite -(fconnect_invariant h'F zRy) [_ == _]h'E.
move=> uFX; rewrite inE (fconnect_invariant k'F uFX) k'X.
have{uFX}: adj (ecpH Gc) (edge u) by rewrite -(adjF uFX) adjE.
rewrite (adj_ecpH ntGc) unfold_in => /hasP[ _ /mapP[y GcNy ->] euFy].
rewrite {u euFy}(fconnect_invariant k'F euFy) Ek'.
move: kE (uniq_ctrenum cp_ok); rewrite [cpmap _]/= -/G cpring_ecpH //.
rewrite /ctrenum -/ctrenum -/G 3!mask_cons !cat0s => kE.
rewrite -[p in _ ++ p]cat1s 2!insertE_cat uniq_catCA -!insertE_cat.
rewrite 3!cat_cons -2!cat_rcons -cat_cons insertE_cat cat_uniq has_sym andbCA.
rewrite /rcons {2}/insertE -all_predC /all 15?(mem_insertE, inE) //.
case/andP=> /and3P[rE'fX _] /and3P[rE'nX _] /andP[rE'X _] _. 
move: GcNy; rewrite !inE => /predU1P[|/pred2P[]] ->{y}.
- rewrite h'nGc -[h _](fconnect_invariant kF (cface_node_ecpH ntG)).
  rewrite eq_sym -{1}(nodeK (ecpH G)) (eqcP (kF _)) [_ == _]kE.
  by rewrite mem_insertE // has_mask2_F.
- rewrite h'Gc -(eqcP (kF _)); have <-: k (edge (face (ecpH G))) = h G.
    by apply/(fconnect_invariant kF)/connect1/eqP; rewrite /= nodeK (negPf ntG).
  by rewrite [_ == _]kE mem_insertE // has_mask2_F.
rewrite h'feGc; have <-: k (edge (ecpH G)) = h (face (edge G)).
  rewrite (eqcP (hF _)); apply/esym/(fconnect_invariant kF)/connect1/eqP.
  by rewrite /= nodeK (negPf ntG) /= eqxx.
by rewrite [_ == _]kE  mem_insertE // has_mask2_F.
Qed.

Lemma sparse_cfctr mr mc cp :
  size mr = cprsize cp -> size mc = ctrmsize cp ->
  let G := cpmap cp in
  let cc := map edge (mask mr (cpring G)) ++ insertE (mask mc (ctrenum cp)) in
  cfctr mr mc cp ==> sparse ((G : G) :: cc).
Proof.
lazy zeta; elim: cp => [|s cp IHcp] // in mr mc *.
case Dcpc: (cfctr _ _) (cfctr_config_prog mr mc (s :: cp)) => // [cpc].
case: s Dcpc => // [n||] Dcpc; rewrite !implyTb => cp_ok Emr Emc;
  have cpQ := config_prog_cubic cp_ok; rewrite /= in Dcpc cpQ Emr Emc;
  move: IHcp {cpQ} (cpmap_plain cpQ) (cpmap_cubic cpQ) (cpmap_proper cpQ);
  rewrite [cpmap (_ :: _)]/=; set G := cpmap cp => IHcp plainG cubicG ntG.
- rewrite cpring_ecpR /= -(rotrK n mr).
  rewrite -(size_rotr n mr) in Emr; move: Dcpc (IHcp _ _ Emr Emc).
  case: (cfctr _ mc cp) => //= _ _ {cpc}; apply: etrans; apply: eq_simple.
    move=> y; congr (_ || _).
      by rewrite !(cfaceC y); apply/esym/(@same_cnode G)/fconnect_iter.
    apply: eq_has_r => x {y}; rewrite !mem_cat; congr (_ || _).
    by rewrite !map_mask map_rot mem_mask_rot // size_map size_ring_cpmap.
  rewrite /= !size_cat !size_map; congr (_ + _).+1; rewrite /rot mask_cat.
    rewrite -rot_size_cat size_rot -mask_cat ?cat_take_drop //.
    by rewrite !size_take Emr -size_ring_cpmap.
  by rewrite !size_drop Emr -size_ring_cpmap.
- rewrite /G.
  case Dcp: cp mc mr Emc Emr Dcpc => [|s cp'] [|b3 mc] // [|b1 [|b2 mr]] //.
    case: mr {cp Dcp G IHcp cp_ok plainG cubicG ntG} => [|b3 [|b4 mr]] // _ _.
    rewrite sparse_cons -(eq_has (mem_cpring (ecpY _))) cpring_ecpY cpring0 /=.
    by case: b1 b2 b3 => [] [] [].
  rewrite -Dcp -/G; have plainGX: plain (ecpY G) := plain_ecpY G plainG.
  case: ifP => // b123; rewrite [size _]/= [size _ = _]/= => [] [Emc] [Emr].
  case: (cfctr _ _)  {IHcp}(IHcp (b3 :: mr) mc Emr Emc) => // {cpc} cpc IHcp _.
  have <-: map (icpY G) (node G :: ctrenum cp) = ctrenum (CpY :: cp).
    by rewrite /G Dcp.
  move: IHcp; set p := _ ++ _; rewrite sparse_cons -(eq_has (mem_cpring G)).
  case/andP=> {cpc}rG'p IHp.
  have{rG'p IHp}: sparse ((ecpY G : ecpY G) :: map (icpY G) (node G :: p)).
    rewrite map_cons !sparse_cons; apply/and3P; split.
    - rewrite -(eq_has (mem_cpring (ecpY G))) cpring_ecpY -map_cons.
      apply: contra rG'p => /hasP[_ /mapP[y py ->] r_y]; apply/hasP.
      rewrite !inE (mem_map (@icpY_inj _ G)) !orFb  in r_y.
      exists y; last exact: mem_behead; case/predU1P: py => // y_nG.
      by have:= cpring_uniq G; rewrite head_cpring /= -y_nG r_y.
    - apply: contra rG'p => /hasP[_ /mapP[y py ->]]; rewrite cnodeC => yNnG.
      apply/hasP; exists y => //; apply: wlog_neg => r'y.
      by rewrite mem_cpring cnode1 cnodeC -(@cnode_injcp [:: CpY]).
    elim: p rG'p IHp => //= x p IHp /norP[r'x r'p].
    rewrite !sparse_cons => /andP[pN'x /IHp->] {r'p}//; rewrite andbT has_map.
    by rewrite (eq_has (@cnode_injcp [:: CpY] _ _ _ r'x)).
  rewrite -cat1s sparse_catC cats1 -(cat1s (pointer _)) sparse_catC cats1.
  rewrite -map_mask /p head_cpring cpring_ecpY !mask_cons map_cons !map_cat.
  rewrite insertE_cat -insertE_icpY !map_mask -!map_comp rcons_cons !rcons_cat.
  move: (rcons _ _) => rk; rewrite insertE_icpY insertE_seqb map_cat !map_nseq.
  move: {p}(mask mr _) (nseq b3 _) => rr r3; set x3 := icpY G (node G).
  rewrite sparse_catCA -!(catA _ _ rk) -catA sparse_catCA.
  rewrite [cat r3]lock 2!catA -lock sparse_catCA; move: {rr rk}(r3 ++ _) => rk.
  case: b1 b2 b3 b123 => [] [] [] // _;
    rewrite !sparse_cons => /andP[// /contra->//]; apply: sub_has => u.
  - by rewrite 2!cnode1.
  by rewrite cnode1.
case: mc mr Emc Emr Dcpc => [|b3 [|b4 [|b5 mc]]] [|b1 [|b2 mr]] // [Emc] Emr.
rewrite /= in Emc Emr; case: ifP => // b314_325; case: ifP => // _.
have{IHcp}:= IHcp [:: b4, b5 & mr] mc Emr Emc; set p := _ ++ _.
case: (cfctr _ _ _) => // []{cpc} cpc IHcp _; rewrite {cpc}implyTb in IHcp.
have plainGX := plain_ecpH G plainG.
have <-: face (ecpH G) :: map (icpH G) [:: node G, G : G & ctrenum cp] =
          ctrenum (CpH :: cp) by [].
move: IHcp; rewrite sparse_cons -(eq_has (mem_cpring G)) => /andP[r'p IHp].
have nX: node (ecpH G) = icpN _ (icpN _ (edge (ecpU G))).
  by rewrite /= /long_cpring /= nodeK (negPf ntG).
have n1G: node (icpH G G) = icpN _ (ecpY G) by rewrite /= (negPf ntG) /= !eqxx.
have in_rH x: (icpH G x \in cpring (ecpH G)) = (x \in drop 2 (cpring G)).
  by rewrite cpring_ecpH // nX !inE (mem_map (@icpH_inj _ G)).
have{IHp r'p}: sparse (pointer (ecpH G) :: map (icpH G) [:: node G, G : G & p]).
  rewrite !map_cons !sparse_cons; apply/and4P; split.
  - rewrite -!map_cons -(eq_has (mem_cpring (ecpH G))) has_map (eq_has in_rH).
    apply: contra r'p => /hasP[x]; rewrite !inE orbA => /orP[Gx | p_x] r_x.
      have:= cpring_uniq G; rewrite head_proper_cpring // (cat_uniq [:: _; _]).
      by case/and3P=> _ /hasP[]; exists x; rewrite ?inE.
    by apply/hasP; exists x; last apply: mem_drop r_x.
  - rewrite -map_cons has_map; apply/hasPn=> y; rewrite !inE => p_y.
    set n0nG := icpH G _; pose n1nG : ecpH G := icpN _ (icpN _ (ecpU G)).
    pose n2nG : ecpH G := icpN _ (edge (ecpY G)).
    have cycNnG : fcycle node [:: n0nG; n1nG; n2nG] by rewrite /= !eqxx.
    rewrite (fconnect_cycle cycNnG) ?mem_head // !inE !orbF.
    case/predU1P: p_y => [-> | p_y].
      by have:= cpring_uniq G; rewrite head_proper_cpring.
    apply: contraNneq r'p => /icpH_inj y_nG; apply/hasP; exists y => //.
    by rewrite head_cpring -y_nG mem_head.
  - rewrite has_map; apply/hasPn=> y p_y; rewrite inE.
    have r'y := hasPn r'p _ p_y.
    by rewrite cnodeC (@cnode_injcp [:: CpH]) // cnodeC -mem_cpring.
  elim: p r'p IHp => [|x p IHp] //= /norP[r'x r'p].
  rewrite !sparse_cons has_map => /andP[/contra->]; first exact: IHp.
  by apply: etrans; apply: eq_has => y; rewrite inE (@cnode_injcp [:: CpH]).
rewrite {}/p head_proper_cpring // cpring_ecpH //.
rewrite -cat1s sparse_catC cats1 -(cat1s (ecpH G : ecpH G)) sparse_catC cats1.
rewrite 4!map_cons !mask_cons !insertE_cat map_cat -insertE_icpH map_mask.
rewrite !rcons_cons !rcons_cat -map_comp !map_cat; move: (rcons _ _) => rk.
rewrite !map_mask -map_comp !map_nseq /comp; move: (mask mr _) => rr IHcp.
rewrite 4!(catA (insertE _), =^~ insertE_cat) sparse_catCA.
rewrite (catA _ _ rr) -2!catA sparse_catCA !insertE_cat !insertE_seqb !catA.
rewrite -3!catA sparse_catCA; do[rewrite -!catA; move: (_ ++ _) => r] in IHcp *.
rewrite (catA (nseq b2 _)) (catA (nseq b5 _)) sparse_catCA -!catA.
pose xG b := nseq b (icpH G G); pose yG b := nseq b (icpH G (node G)).
transitivity (sparse (xG b2 ++ xG b3 ++ xG b5 ++ yG b1 ++ yG b3 ++ yG b4 ++ r)).
  congr uniq; rewrite !map_cat !map_nseq.
  do !congr cat; congr nseq; apply/(rootP (@cnodeC (ecpH G))).
  - by rewrite 2!cnode1r n1G.
  - by rewrite cnode1r n1G.
  - by rewrite nX 2!cnode1 /= eqxx.
  by rewrite cnode1 /= eqxx.
move: IHcp; rewrite (sparse_catCA [::_] [::_]) {}/xG {}/yG.
move: (ecpY G) (icpH G G) (icpH G (node G)) r => G' x y r.
case: b3 b1 b2 b4 b5 b314_325 => [] [] [] [] [] // _.
- by case/andP.
- by rewrite sparse_catCA => /andP[].
- by case/andP.
- by rewrite sparse_catCA => /andP[].
by case/and3P.
Qed.

Fixpoint ctrband (cm : bitseq) (cp : cprog) {struct cp} : cfmask :=
  match cp, cm with
  | CpR n :: cp', _ =>
    let: Cfmask mr mk := ctrband cm cp' in Cfmask (rot n mr) mk
  | [:: CpY], _ =>
    Cfmask (nseq 3 false) [::]
  | CpY :: cp', b1 :: cm' =>
    if ctrband cm' cp' is Cfmask [:: a0, a1 & mr] mk then
      Cfmask [:: b1 || a0, false, b1 || a1 & mr] mk
    else Cfmask [::] [::]
  | CpH :: cp', [:: b1, b0, b2 & cm'] =>
    if ctrband cm' cp' is Cfmask [:: a0, a1, a2 & mr] mk then
      Cfmask [:: b0 || a0, b1, b2 || a2 & mr] ([|| b0, b1, b2 | a1] :: mk)
    else Cfmask [::] [::]
  | _, _ => Cfmask [::] [::]
  end.


Lemma ctrband_correct cm cp :
    size cm = ctrmsize cp -> config_prog cp ->
 [/\ proper_cpmask cp (ctrband cm cp)
   & fband (insertE (mask cm (ctrenum cp)))
       =i fband (cpmask (ctrband cm cp) cp)].
Proof.
move=> Ecm cp_ok; elim: cp cp_ok cm Ecm => // s cp IHcp cp_ok.
move: cp_ok (config_prog_cubic cp_ok) IHcp => /=.
case: s => // [n||] cp_ok cpQ; move: (cpmap_plain cpQ) (cpmap_proper cpQ);
  rewrite [cpmap _]/=; set G := cpmap cp => plainG ntG IHcp cm Ecm.
- case: (ctrband cm cp) {IHcp Ecm cp_ok}(IHcp cp_ok _ Ecm) => mr mk.
  case=> /andP[Emr Emc] IHcp; split; first by rewrite /= size_rot Emr.
  rewrite /cpmask /= -/G cpring_ecpR /= => x.
  rewrite IHcp /= !fband_cat /=; congr (_ || _).
  by rewrite mask_rot ?fband_rot // (eqP Emr) -size_ring_cpmap.
- rewrite /G; case Dcp: cp cm cp_ok Ecm => [|s cp'] // [|b1 cm] //.
    by rewrite /cpmask /= cpring_ecpY cpring0.
  rewrite -Dcp -/G [size _]/= => cp_ok [Ecm].
  case: (ctrband cm cp) {IHcp}(IHcp cp_ok _ Ecm) => mr mk [/andP[/eqP Emr Emk]].
  have: 1 < size mr by rewrite Emr -size_ring_cpmap -size_proper_cpring.
  case: mr Emr => [|a0 [|a1 mr]] // Emr _ IHcp.
  split=> [|u]; first by rewrite /= -Emr /= eqxx.
  rewrite -map_cons /cpmask [cpmap _]/= [cpker _]/= -/G.
  rewrite cpring_ecpY /behead (head_proper_cpring ntG).
  rewrite -!map_mask insertE_icpY map_cons !mask_cons cat0s insertE_cat.
  rewrite insertE_seqb -!catA !unfold_in !has_cat !has_seqb -map_mask.
  have [[x uFx] | XFu] := fband_icpY u; last first.
    have DuF := etrans (esym (same_cface XFu _)) (cface_ecpY _).
    by rewrite !DuF !andbF !(eq_has DuF) !has_map !has_pred0. 
  rewrite !(same_cface uFx) !(eq_has (same_cface uFx)) !cface_icpY.
  rewrite !has_map !(eq_has (cface_icpY G x)) !has_cat !has_seqb.
  rewrite [has _ _]IHcp [in rhs in _ = rhs]cface1r cface_icpY.
  rewrite /cpmask {1}(head_proper_cpring ntG) unfold_in has_cat !has_mask_cons.
  by rewrite orbCA cface1r nodeK !andb_orl -!orbA; do !bool_congr.
case: cm Ecm => [|b1 [|b0 [|b2 cm]]] //; rewrite [size _]/= => [] [Ecm].
case: (ctrband cm cp) {IHcp}(IHcp cp_ok _ Ecm) => mr mk [/andP[/eqP Emr Emk]].
have longG: long_cpring G by apply: cfmap_long.
have: 2 < size mr by rewrite Emr -size_ring_cpmap -size_long_cpring.
case: mr Emr => [|a0 [|a1 [|a2 mr]]] // Emr _ IHcp; rewrite /= in Emr.
split=> [|u]; first by rewrite /= -Emr /= eqxx.
rewrite /cpmask [cpmap _]/= [cpker _]/= -/G (head_long_cpring longG).
rewrite cpring_ecpH // !mask_cons !insertE_cat -!map_mask !insertE_seqb. 
rewrite insertE_icpH !unfold_in !has_cat !has_seqb.
have fnX: face (node (ecpH G)) = icpH G (node G).
  by rewrite /= /long_cpring /= nodeK (negPf ntG) /= nodeK (negPf ntG).
have <-: face (icpH G (edge (node G))) = edge (face (ecpH G)).
  rewrite /= nodeK (negPf ntG) /= [_ == _](inj_eq edgeI) eq_sym (negPf ntG).
  by rewrite eqxx.
rewrite (cface1r (node _)) fnX -(cface1r (ecpH G)) -cface1r.
case uFX: (cface u (ecpH G)).
  have DuF := etrans (same_cface uFX _) (cface_ecpH ntG _).
  by rewrite !andbT !DuF !andbF !(eq_has DuF) !has_map !has_pred0.
have [[x uFx]|] := fband_icpH u; last by rewrite cfaceC uFX.
have DuF := etrans (same_cface uFx _) (cface_icpH _ _ _).
rewrite !DuF !andbF !has_map !(eq_has DuF) [has _ _]IHcp unfold_in.
rewrite /cpmask (head_long_cpring longG) has_cat !has_mask_cons.
by rewrite cface1r nodeK -cface1r /= !andb_orl -!orbA; do !bool_congr.
Qed.

Definition cfcontract_mask cf := ctrmask (cfprog cf) (cfcontract_ref cf).

Definition cfcontract cf := mask (cfcontract_mask cf) (ctrenum (cfprog cf)).

Fixpoint cptriad ccm cp i :=
  if i is i'.+1 then
    let: Cfmask mrt mkt := cpadj (cfmask1 cp i') cp in
    let: Cfmask mrc mkc := ccm in
    let mct := mask mrc mrt ++ mask mkc mkt in
    if has negb mct && (2 < count id mct) then true else cptriad ccm cp i'
  else false.

Definition valid_ctrm (cm : bitseq) cp :=
  let n := count id cm in
  if n == 4 then cptriad (ctrband cm cp) cp (cpksize cp) else 0 < n <= 3.

Definition contract_ctree cf :=
  let cp := cfprog cf in let cm := cfcontract_mask cf in
  if cfctr (nseq (cprsize cp) false) cm cp is Some cpc then
    if valid_ctrm cm cp then Some (cpcolor cpc) else None
  else None.

Lemma contract_ctreeP cf :
 if contract_ctree cf is Some ct then
   let r := cfring cf in
   [/\ valid_contract r (cfcontract cf)
     & forall et, cc_ring_trace (cfcontract cf) (rev r) et ->
        ctree_mem ct (etrace (behead et))]
 else True.
Proof.
case: cf => sym ccr cp; rewrite /contract_ctree /cfcontract /cfcontract_mask /=.
rewrite /cfring revK /cfmap {sym}/= -size_ring_cpmap.
set G := cpmap cp; set r := cpring G.
set cm := ctrmask cp ccr; set mr0 := nseq (size r) false.
have Emr0: size mr0 = cprsize cp by rewrite -size_ring_cpmap /mr0 size_nseq.
have Ecm: size cm = ctrmsize cp by apply: size_ctrmask.
move: (sparse_cfctr Emr0 Ecm) (cfctr_correct Emr0 Ecm).
case: (cfctr mr0 cm cp) (cfctr_config_prog mr0 cm cp) => //= [cpc] cp_ok.
have plainG := cpmap_plain (config_prog_cubic cp_ok).
set cc := mask cm (ctrenum cp); rewrite -/G -/r in cc *.
rewrite {1}mask_false cat0s => cc_sparse cc_col.
case: ifP => // cm_valid; split=> [|_ [k col_k ->]]; last first.
  have{cc_col} := cc_col k; rewrite mask_false map_nseq mask_true //.
  case=> {k col_k}// k col_k <-.
  apply/ctree_mem_cpcolor; split; first exact: even_etrace.
  set et := trace _; rewrite /etrace; set h := etrace_perm _.
  exists (h \o k); first by apply: coloring_inj col_k; apply: permc_inj.
  rewrite sumt_permt map_comp trace_permt -/et -map_cons; congr (map h _).
  have tr_et: sumt et = Color0 by apply: sumt_trace.
  by rewrite -[sumt _]add0c -{}tr_et /et head_cpring /= [ctrace _]headI addcK.
have size_cc: size cc = count id cm by rewrite size_mask // size_ctrenum.
rewrite /valid_ctrm -{}size_cc -(mem_iota 1 3) !inE in cm_valid.
split=> [|||cc4]; first 2 [by case/andP: cc_sparse].
- have:= uniq_ctrenum cp_ok; rewrite -/G -/r insertE_cat cat_uniq disjoint_has.
  rewrite andbA andbAC => /andP[_]; apply: contra => /hasP[x] /=.
  rewrite mem_rev mem_insertE // => r_x /has_mask KEx.
  by apply/hasP; exists x; rewrite /= mem_insertE //; apply/hasP; exists x.
- by rewrite /= !orbA orbC -!orbA; case: ifP cm_valid.
move: cm_valid; rewrite {}cc4 /=; apply: contraL => /pred0P no_triad.
elim: {-2}(_ cp) (leqnn (cpksize cp)) => //= i IHi lt_i_cp.
move: (cfmask1 cp i) (cpmask1 lt_i_cp cp_ok) (proper_cpmask1 cp i) => cmx.
set x := nth _ _ i => Dcpx cmx_valid.
move: (cpadj_proper cmx_valid) (cpmask_adj cp_ok cmx_valid).
case: (cpadj cmx cp) => mrt mkt.
case: {-4}(ctrband cm cp) (ctrband_correct Ecm cp_ok) => mrc mkc.
rewrite -/cc /= -/G -/r => [] [/andP[Emrc Emkc] DccF] /andP[Emrt Emkt] DmtF.
case: andP => [{IHi}[mtc_max mtc_min]|_]; last by apply: IHi; last apply: ltnW.
rewrite -size_ring_cpmap -/G -/r in Emrc Emrt.
pose mt := mrt ++ mkt; pose mc := mrc ++ mkc; pose q := r ++ cpker cp.
have Emtq: size mt == size q.
  by rewrite !size_cat (eqP Emrt) (eqP Emkt) (size_cpker cp_ok) eqxx.
have Emcq: size mc == size q.
  by rewrite !size_cat (eqP Emrc) (eqP Emkc) (size_cpker cp_ok) eqxx.
have Uq: simple q by apply: cpmap_simple.
rewrite -!mask_cat -/mt -/mc -/q ?(eqP Emrt) ?(eqP Emrc) // {}Dcpx in DccF DmtF.
rewrite -mask_cat -/mt -/mc ?(eqP Emrt) ?(eqP Emrc) // in mtc_max mtc_min.
case/andP: {no_triad}(no_triad x); split=> /=.
  move: Uq; rewrite simple_cat => /and3P[_ Urk _]; apply: contra Urk.
  case/hasP=> y; rewrite mem_rev => r_y xFx.
  apply/hasP; exists x; first by rewrite mem_nth ?size_cpker.
  by apply/hasP; exists y.
apply/andP; split=> [{mtc_max} | {mtc_min}]; last first.
  apply: contraL mtc_max => /subsetP ccAx.
  have{ccAx DccF DmtF}: {subset fband (mask mc q) <= fband (mask mt q)}.
    move=> y; rewrite -DccF DmtF /= orbF adjC //.
    by case/hasP=> z /ccAx xAz /adjFr->.
  move: mc mt Emcq Emtq Uq; rewrite simple_recI.
  elim: q => [|y q IHq] [|b1 m1] // [|b2 m2] //= Em1 Em2 /andP[qF'y Uq].
  have{qF'y} qF'y m: (y \in fband (mask m q)) = false.
    by apply: contraNF qF'y; apply: has_mask.
  case: b1 b2 => [] [] //= q12F; try apply: (IHq m1 m2) => //.
  - move=> z q1Fz; have:= q12F z; rewrite !unfold_in /=.
    case zFy: (cface z y); last exact.
    by rewrite (closed_connect (fbandF _) zFy) qF'y in q1Fz.
  - by rewrite -(qF'y m2) q12F // fband_cons connect0.
  move=> z q1Fz; case/orP: (q12F z q1Fz) => // zFy.
  by rewrite (closed_connect (fbandF _) zFy) qF'y in q1Fz.
pose n_Ax_cc := fcard face (predI (adj x) (fband (insertE cc))).
apply: leq_trans mtc_min _; apply: (@leq_trans n_Ax_cc); last first.
  rewrite -size_filter -(size_map (froot face \o edge)).
  apply: leq_trans (card_size _); apply: subset_leq_card.
  apply/subsetP=> y /and3P[/eqP Dy /adjP[z xFz zRy] cc_y].
  apply/mapP; exists z; last by rewrite /= (rootP cfaceC zRy).
  rewrite mem_filter -fconnect_orbit xFz andbT.
  by rewrite /fband (eq_has (same_cface zRy)).
pose nF_qtc := fcard face (fband (filter (fband (mask mt q)) (mask mc q))).
apply: eq_leq; transitivity nF_qtc; last first.
  apply: eq_n_comp_r => y; rewrite unfold_in has_filter inE [fband _ _]DccF.
  rewrite (eq_filter DmtF) -filter_predI -has_filter adjC //.
  apply/hasP/andP=> [[z qc_z /andP[yFz zAx]] | [yAx /hasP[z qc_z zFy]]].
    by rewrite /= orbF -(adjF yFz) in zAx; split; last by apply/hasP; exists z. 
  by exists z => //=; rewrite zFy -(adjF zFy) yAx.
rewrite {n_Ax_cc DccF DmtF}/nF_qtc simple_fcard_fband; last first.
  by rewrite /simple filter_mask !map_mask !mask_uniq.
move: mc mt Emcq Emtq Uq; rewrite simple_recI.
elim: q => [|y q IHq] [|b1 m1] // [|b2 m2] //= Em1 Em2 /andP[qF'y Uq].
set q1 := mask m1 q; set q2 := mask m2 q.
have{qF'y} qF'y m: (y \in fband (mask m q)) = false.
  by apply: contraNF qF'y; apply: has_mask.
have Eq21: filter (fband (y :: q2)) q1 = filter (fband q2) q1.
  apply: eq_in_filter => z q1z; apply: orb_idl; rewrite cfaceC => yFz.
  by case/hasP: (qF'y m1); exists z.
by case: b1 b2 => [] []; rewrite /= IHq ?Eq21 ?connect0 ?[fband _ y]qF'y.
Qed.

End ConfigContract.

