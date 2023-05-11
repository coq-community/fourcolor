(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype path fingraph.
From fourcolor Require Import hypermap walkup geometry color chromogram.

(******************************************************************************)
(* Hypermap, graph and contract colorings, colorable maps, ring traces, valid *)
(* contracts, and the definition of the special maps used in the proof:       *)
(* minimal counter example, C-reducible, and embeddable.                      *)
(*   For G : hypermap, k : G -> color, and cc, r : seq G, we have             *)
(*  coloring k <-> k is a map coloring: k assigns the same color to each dart *)
(*                 in a face cycle of G, but a different color to the ends of *)
(*                 each edge link, hence to adjacent faces.                   *)
(*  four_colorable G <-> G has a map coloring; we prove this is decidable.    *)
(* minimal_counter_example G <-> G is a minimal counter-example to the finite *)
(*                 hypermap four color theorem: a non-four_colorable planar   *)
(*                 bridgeless plain and precubic hypermap, such that all such *)
(*                 hypermaps with fewer darts are four_colorable. We show     *)
(*                 immediately that such a G must be cubic, and later that it *)
(*                 must be connected (patch.v) and pentagonal (birkhoff.v).   *)
(*  cc_coloring cc k <-> assuming G is a plain map, k is a contract map       *)
(*                 coloring for the contract cc: k assigns the same color to  *)
(*                 faces adjacent via an E-link (x, edge x), for x \in cc,    *)
(*                 but different colors to other adjacent faces.              *)
(*  cc_colorable cc <-> there is a contract map coloring for cc.              *)
(*  ring_trace r et <-> there is a map coloring k such that et is the edge    *)
(*                 coloring trace of map k r.                                 *)
(* cc_ring_trace cc r et <-> there is a contract coloring for cc with trace   *)
(*                 et on r.                                                   *)
(* good_ring_arity x <=> the arity (face size) for x is between 3 and 6; it   *)
(*                 is easier to check the embedding of a configuration whose  *)
(*                 perimeter satisfies this condition in an internally        *)
(*                 6-connected map.                                           *)
(* at_radius2 A x y <=> x and y are both adjacent to some common z \in A;     *)
(*                 when A is face-closed and contains both x and y, this      *)
(*                 implies the face at y is at distance at most 2 from the    *)
(*                 the face at x, in A.                                       *)
(*   radius2 A <=> A has radius 2, i.e., there is an x in A such that         *)
(*                 at_radius2 A x y holds for all y in A.                     *)
(* embeddable r <-> G is an embeddable configuration with perimeter r: G is   *)
(*                 planar, bridgeless, connected, plain, and r-quasicubic for *)
(*                 the simple N-cycle r, while good_ring_arity holds on r and *)
(*                 kernel r has radius 2.                                     *)
(*    sparse p <=> p is node-simple: no two darts in p belong to the same     *)
(*                 node.                                                      *)
(*   triad p x <=> x is a triad for p: at least three of the faces around the *)
(*                 face of x contain a dart y in p (so x and y are adjacent), *)
(*                 but not all y in p are adjacent to x.                      *)
(* valid_contract r cc <-> cc is a valid contract for ring r: cc has size at  *)
(*                 most 4, and the edge completion of cc is disjoint from r,  *)
(*                 sparse and has a triad if cc has size 4.                   *)
(* C_reducible r cc <-> assuming G is a configuration with ring r, G is       *)
(*                 C-reducible with contract cc: cc is valid, and any         *)
(*                 contract ring trace et for cc is in the Kempe (co)closure  *)
(*                 of the set of ring traces of colorings of G. This means    *)
(*                 that G cannot be embedded in a minimal counter-example, as *)
(*                 then applying cc to G would yield a four_colorable smaller *)
(*                 map whose coloring could be adjusted by a series of Kempe  *)
(*                 flips to match a coloring of G.                            *)
(* edge_central h x <=> h : G -> G' commutes with edge at x : G.              *)
(*                  := h (edge x) == edge (h x)                               *)
(* preembedding A h <-> h : G -> G' is an embedding for a subset A of G: in A *)
(*                h commutes with face and preserves arity, A is included in  *)
(*                the face-closure of its h-edge_central subset, which is     *)
(*                rlink-connected.                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Coloring.

Variable G : hypermap.

Definition coloring (k : G -> color) :=
  invariant edge k =1 pred0 /\ invariant face k =1 G.

Lemma coloring_inj h k : injective h -> coloring k -> coloring (h \o k).
Proof.
move=> injh [kE kF]; split=> x; rewrite /invariant.
  by move: (kE x); rewrite -(invariant_inj edge k injh).
by move: (kF x); rewrite -(invariant_inj face k injh).
Qed.

Definition ring_trace r et := exists2 k, coloring k & et = trace (map k r).

Definition four_colorable := exists k, coloring k.

Lemma colorable_bridgeless : four_colorable -> bridgeless G.
Proof.
case=> k [kE kF]; apply/existsP => [[x eFex]]; case/negP: (kE x); apply/eqP.
by rewrite -(fconnect_invariant kF eFex).
Qed.

Definition graph_coloring (k : G -> color) :=
  invariant edge k =1 pred0 /\ invariant node k =1 G.

Definition graph_four_colorable : Prop := exists k, graph_coloring k.

Definition cc_coloring cc (k : G -> color) :=
  invariant edge k =i insertE cc /\ invariant face k =1 G.

Definition cc_colorable cc := exists k, cc_coloring cc k.

Definition cc_ring_trace cc r et :=
  exists2 k, cc_coloring cc k & et = trace (map k r).

End Coloring.

Arguments coloring {G} k.
Arguments ring_trace {G} r et.
Arguments cc_coloring {G} cc k.
Arguments cc_colorable {G} cc.
Arguments cc_ring_trace {G} cc r et.

Section ColoringDual.

Variable G : hypermap.

Lemma coloring_dual (k : G -> color) :
  @coloring (dual G) k <-> graph_coloring k.
Proof.
split=> [[kE' kF'] | [kE kN]].
  split=> x; rewrite /= eq_sym.
    by rewrite -{1}(finv_f edgeI x) [_ == _]kE'.
  by rewrite -{1}(finv_f nodeI x) [_ == _]kF'.
split; move=> /= x; rewrite eq_sym.
  by rewrite -{1}(f_finv edgeI x) [_ == _]kE.
by rewrite -{1}(f_finv nodeI x) [_ == _]kN.
Qed.

Lemma four_colorable_dual :
  four_colorable (dual G) <-> graph_four_colorable G.
Proof. by split=> [] [k colk]; exists k; case (coloring_dual k); auto. Qed.

Lemma coloring_mirror (k : G -> color) : @coloring (mirror G) k -> coloring k.
Proof.
case=> kE' kF'; have kF x: k (face x) = k x.
  by apply/esym/eqP; rewrite -{1}(finv_f faceI x) [_ == _]kF'.
split=> x //=; rewrite eq_sym -kF ?eqxx // -(kF (edge x)) -{1}[x]edgeK.
exact: kE'.
Qed.

Lemma colorable_mirror : four_colorable (mirror G) -> four_colorable G.
Proof. by case=> k /coloring_mirror; exists k. Qed.

End ColoringDual.

Section EqmColorable.

Variable G G' : hypermap.
Hypothesis eqG : eqm G G'.

Lemma eqm_colorable : four_colorable G -> four_colorable G'.
Proof.
case: G eqG => [d e n f GeK] [e' n' f' G'eK De _ Df] [k [kE kF]]; exists k.
by split=> x; rewrite /= -?De -?Df; [apply: kE | apply: kF].
Qed.

Lemma eqm_graph_colorable : graph_four_colorable G -> graph_four_colorable G'.
Proof.
case: G eqG => [d e n f GeK] [e' n' f' G'eK De Dn _] [k [kE kN]]; exists k.
by split; move=> x; rewrite /= -?De -?Dn; [apply: kE | apply: kN ].
Qed.

End EqmColorable.

Section DecideColorable.

Variable G : hypermap.

(* We need decidability of ring traces in birkhoff.                           *)
Lemma decide_ring_trace (r : seq G) et :
  {ring_trace r et} + {~ ring_trace r et}.
Proof.
pose kpr k p := [pred lc : colseq | (map k p == lc) && (trace (map k r) == et)].
pose ekpr := exists2 k, coloring k & kpr k _ _; pose lc : colseq := [::].
suff: {ekpr [::] lc} + {~ ekpr [::] lc}.
  case=> [col | no_col]; [left | right].
    by have [k colk /eqseqP Det] := col; exists k.
  by case=> k colk /esym/eqP Det; case: no_col; exists k.
move Dn: #|[predC (Nil G)]| => n.
elim: n [::] lc Dn => [|n IHn] p lc Dn.
  have allp x: x \in p := negbFE (card0_eq Dn x).
  pose kp := nth Color0 lc (index _ p).
  pose kkp := [pred x | (kp (edge x) == kp x) || (kp (face x) != kp x)].
  case kp_ok: (pred0b kkp && kpr kp p lc).
    case/andP: kp_ok => col_kp Det; left; exists kp => //.
    by split=> x; [apply negbTE | apply negbNE]; case/norP: (pred0P col_kp x).
  right=> [[k [kE kF] /andP[/eqP Dlc Det]]].
  have Dkp: kp =1 k.
    by move=> x; rewrite /kp -Dlc (nth_map x) ?nth_index ?index_mem.
  rewrite /= !(eq_map Dkp) Dlc Det eqxx /= andbT in kp_ok.
  by case/pred0Pn: kp_ok => x /=; rewrite !Dkp [_ == _]kE [_ == _]kF.
have [x p'x | p0] := pickP [predC p]; last by rewrite (eq_card0 p0) in Dn.
pose ekprx c := ekpr (x :: p) (c :: lc).
have ekprxP c : {ekprx c} + {~ ekprx c}.
  apply: IHn; rewrite (cardD1 x) [x \in _]p'x in Dn; case: Dn => <-.
  by apply: eq_card => y; rewrite !inE negb_or.
have [cb /= cb_ok | no_cb] := pickP [pred cb | ekprxP (ccons cb.1 cb.2)].
  left; move: (ccons _ _) (ekprxP _) cb_ok => c [] // [k col_k] /=.
  by rewrite eqseq_cons -andbA => /andP[]; exists k.
right=> [[k colk kpr_k]]; pose cb := (cbit1 (k x), cbit0 (k x)).
case/idP: (no_cb cb) => /=; case: (ekprxP _) => // [[]]; exists k => //=.
by rewrite ccons_cbits eqseq_cons eqxx.
Qed.

Lemma decide_colorable : {four_colorable G} + {~ four_colorable G}.
Proof.
case: (decide_ring_trace [::] [::]) => [colG | col'G]; [left | right].
  by have [k colk _] := colG; exists k.
by case=> k colk; case: col'G; exists k.
Qed.

End DecideColorable.

Section MinimalCounterExample.

Variable G : hypermap.

Record minimal_counter_example : Prop := MinimalCounterExample {
  minimal_counter_example_is_planar_bridgeless_plain_precubic :>
    planar_bridgeless_plain_precubic G;
  minimal_counter_example_is_noncolorable :
    ~ four_colorable G;
  minimal_counter_example_is_minimal : forall G',
    planar_bridgeless_plain_precubic G' -> #|G'| < #|G| -> four_colorable G'
}.

Lemma minimal_counter_example_is_cubic : minimal_counter_example -> cubic G.
Proof.
move=> cexG; have F'eG := bridgeless_cface cexG.
have plainG : plain G := cexG; have nGle3 := precubic_leq cexG.
apply/subsetP => /= x _; apply/idPn=> n3'x.
have x'nx: node x != x.
  by apply: contraFneq (F'eG x) => {2}<-; rewrite cface1r nodeK.
have nnx: node (node x) = x.
  apply: contraNeq n3'x => x'n2x; rewrite [x \in _]eqn_leq nGle3 /order.
  rewrite (cardD1 x) (cardD1 (node x)) (cardD1 (node (node x))) !inE.
  by rewrite (inj_eq nodeI) x'nx x'n2x -!cnode1r connect0.
pose G' := WalkupE x; pose h' (u : G') := val u.
pose unx : G' := sub (node x) x'nx; pose G'' := WalkupE unx.
pose h'' (w : G'') := val w; pose h := h' (h'' _).
have Ih': injective h' := val_inj; have Ih'': injective h'' := val_inj.
have Ih: injective h := inj_comp Ih' Ih''.
have hF w1 w2: cface w1 w2 = cface (h w1) (h w2).
  by apply: etrans (fconnect_skip faceI _ _); apply: (fconnect_skip faceI).
have hN w1 w2: cnode w1 w2 = cnode (h w1) (h w2).
  by apply: etrans (fconnect_skip nodeI _ _); apply: (fconnect_skip nodeI).
have hN1 w: h (node w) = node (h w).
  pose nw' := WalkupI unx (node (h w)); pose nw := WalkupI w nw'.
  have Dnw': h' nw' = node (h w).
    by rewrite [h' _]WalkupI_eq -{1}nnx (inj_eq nodeI) eq_sym -if_neg (valP w).
  have Dnw: h nw = node (h w).
    rewrite {1}/h [h'' _]WalkupI_eq -(inj_eq Ih') Dnw' (inj_eq nodeI).
    by rewrite eq_sym -if_neg (valP (h'' w)).
  by rewrite -Dnw; congr h; symmetry; do 2!apply: (valE_skip nodeI).
have ltG''G: #|G''| < #|G| by rewrite ltnW // -!card_S_Walkup.
have oE_G'' w: order edge w = #|predD1 (cedge (h'' w)) unx|.
  rewrite /order -(card_image Ih''); apply: eq_card => u; rewrite inE /=.
  have [u_nx | nx'u] := altP eqP.
    by apply/imageP => [[wu _ u_wu]]; case/eqP: (valP wu); rewrite -[RHS]u_nx.
  set wu : G'' := sub u nx'u; rewrite (mem_image Ih'' _ wu) /=.
  apply: etrans (eq_fconnect (glink_fp_skip_edge _) w wu) _.
    by rewrite /glink /= -!val_eqE /= nnx !eqxx /= orbT.
  exact: (fconnect_skip edgeI w wu).
have [|k [kE kF]] := minimal_counter_example_is_minimal cexG _ ltG''G.
  do ?split; last 1 first.
  - apply/subsetP => [w _]; rewrite !inE; apply: leq_trans (nGle3 (h w)).
    rewrite /order -(card_image Ih) subset_leq_card //.
    by apply/subsetP=> _ /imageP[w' cww' ->]; rewrite -[_ \in _]hN.
  - by do 2!apply: planar_WalkupE; apply: cexG.
  - apply/existsP=> [[w]]; rewrite -{1}[w]edgeK cface1r hF hN1.
    by move: (h _) => y; rewrite -{2}[y]nodeK -cface1r F'eG.
  apply/subsetP => [w _]; rewrite /order_set /in_mem /= oE_G''; set u := h'' w.
  have [EuNx | Eu'Nx] := boolP (has (cedge (h' u)) [:: x; node x]); last first.
    rewrite -(eqnP (predT_subset plainG (h w))) -(card_image Ih').
    have [/negPf Eu'x Eu'nx] := norP Eu'Nx; rewrite /= orbF in Eu'nx.
    apply/eqP; apply: eq_card => y.
    have [-> {y} | x'y] := eqVneq y x; last first.
      pose v : G' := sub y x'y; rewrite (mem_image Ih' _ v) !inE.
      case: eqP => [[ynx] | _]; last exact (same_cskip_edge Eu'Nx).
      by apply/esym/(contraNF _ Eu'nx) => wEy; rewrite /= -ynx.
    rewrite [x \in cedge _]Eu'x; apply/imageP=> [[[z x'z] _ /= zx]].
    by case/eqP: (x'z). 
  have x'Enx: ~~ (cross_edge x).
    move: EuNx; rewrite /= orbF /cross_edge !(cedgeC (h' u)).
    rewrite ![cedge _ _]plain_orbit // !inE (negPf x'nx).
    apply: contraTneq => nx_ex; rewrite nx_ex plain_eq // (negPf (valP u)).
    by rewrite orbF orbb -nx_ex (valP w).
  have:= cardD1 unx (cedge u); rewrite [_ \in _](cskip_edge_merge x'Enx EuNx).
  rewrite /= connect0 orbT -eqSS -add1n => <-.
  have:= cardUI (cedge x) (cedge (node x)); rewrite -!/(order _ _) -eqSS.
  rewrite !(eqnP (predT_subset plainG _)) addn2 eq_sym addnC => <-.
  rewrite eq_card0 ?add0n => [|y]; last first.
    apply: contraNF x'Enx => /andP[/same_cedge xEy /= neEy].
    by rewrite /cross_edge xEy cedgeC.
  rewrite (cardD1 x) !inE connect0 eqSS /order -(card_image Ih').
  apply/eqP/esym/eq_card => y; rewrite !inE; have [-> | x'y] /= := altP eqP.
    by apply/imageP=> [[[z x'z] _ /esym/eqP/idPn]].
  set v : G' := sub y x'y; rewrite (mem_image Ih' _ v).
  by apply: (etrans (cskip_edge_merge x'Enx EuNx)); rewrite /= orbF !(cedgeC y).
case: (minimal_counter_example_is_noncolorable cexG).
pose a' x w := cface x (h w).
have a'0P y: a' y =1 pred0 -> pred2 x (node x) y.
  move=> a'y0; apply/norP => [[x'y nx'y]]; pose uy : G' := sub y x'y.
  by case/idP: (a'y0 ((sub uy : _ -> G'') nx'y)); apply: connect0.
have a'F y z: a' y =1 pred0 -> cface y z -> y = z.
  move=> a'y0 yFz; suffices: pred2 y (node y) z.
    by case/pred2P=> // zny; rewrite -[y]nodeK -zny -cface1 cfaceC F'eG in yFz.
  have: pred2 x (node x) z.
    by apply a'0P => w; rewrite /a' -(same_cface yFz) -a'y0.
  by case/pred2P: (a'0P _ a'y0) => -> /pred2P[]-> /=; rewrite ?nnx ?eqxx ?orbT.
pose k' y := oapp k (ccons false (y == x)) (pick (a' y)).
have kFF w w': cface w w' -> k w = k w'.
  case/connectP=> p wFp ->{w'}; elim: p w wFp => //= _ p IHp w /andP[/eqP <-].
  by move/IHp <-; rewrite (eqcP (kF w)). 
have k'F y z: cface y z -> k' y = k' z.
  rewrite /k' => yFz; case: pickP => [w yFw | a'y0]; last first.
    by rewrite -(a'F y z) //; case: pickP => // w yFw; case/idP: (a'y0 w).
  rewrite /a' (same_cface yFz) in yFw; case: pickP => [w' zFw' | /(_ w)/idP//].
  by apply: kFF; rewrite hF -(same_cface yFw).
have k'E y: ~~ (pred2 x (node x) y) -> k' y != k' (edge y).
  case/norP=> [x'y nx'y]; pose w := (sub (sub y x'y : G') : _ -> G'') nx'y.
  have Dfey: (face (edge y) = h (face (edge w))).
    by apply: nodeI; rewrite -hN1 !edgeK.
  rewrite (k'F (edge y) _ (fconnect1 _ _)) /k'.
  case: pickP => [w' yFw' | /(_ w)]; last by rewrite /a' connect0.
  case: pickP => [w'' feyFw'' /= | /(_ (face (edge w)))]; last first.
    by rewrite /a' Dfey connect0.
  apply: contraFneq (kE w) => eq_kw; rewrite /= -(eqcP (kF _)); apply/eqP/esym.
  by apply: (etrans (etrans _ eq_kw)); apply: kFF; rewrite hF // -Dfey cfaceC.
exists k'; split=> y; last by apply/eqP/k'F; rewrite cfaceC fconnect1.
have [Dy | /k'E/negPf] := boolP (pred2 x (node x) y); last by rewrite eq_sym.
have eey := plain_eq cexG y.
have [Dey|/k'E/negPf] := boolP (pred2 x (node x) (edge y)); last by rewrite eey.
rewrite /k' /= eq_sym; case: pickP => [w yFw /= | a'y0].
  suffices cycFy: fcycle face [:: y].
    rewrite /a' [cface y _](fconnect_cycle cycFy) ?mem_head // inE in yFw.
    by case/norP: Dy; rewrite -(eqP yFw) (valP (h'' w)) (valP w).
  suffices: pred2 y (node y) (face y).
    rewrite /= andbT orbC [_ == _](contraFF _ (F'eG (node y))) //.
    by move/eqP=> fn_y; rewrite 2!cface1r nodeK fn_y.
  have: pred2 x (node x) (face y).
    by rewrite -eey /= !(canF_eq (canF_sym nodeK)) nnx orbC.
  by case/pred2P=> ->; case/pred2P: Dy => ->; rewrite /= ?nnx eqxx ?orbT.      
case: pickP => [w eyFw | a'ey0].
  suffices cycFey: fcycle face [:: edge y].
    rewrite /a' [cface _ _](fconnect_cycle cycFey) ?mem_head // inE in eyFw.
    by case/norP: Dey; rewrite -(eqP eyFw) (valP (h'' w)) (valP w).
  suffices: pred2 (edge y) (node (edge y)) (face (edge y)).
    rewrite /= andbT orbC [_ == _](contraFF _ (F'eG (node (edge y)))) //.
    by move/eqP=> fn_ey; rewrite 2!cface1r nodeK fn_ey.
  have: pred2 x (node x) (face (edge y)).
    by rewrite /= !(canF_eq (canF_sym nodeK)) nnx orbC.
  by case/pred2P=> ->; case/pred2P: Dey => ->; rewrite /= ?nnx eqxx ?orbT.
apply/eqP; move: Dy => /=; case: eqP => [-> | _]; first by rewrite plain_neq.
by move/eqP=> ynx; rewrite (a'F _ x a'ey0) ?eqxx // cface1 ynx nodeK.
Qed.

Coercion minimal_counter_example_is_cubic : minimal_counter_example >-> cubic.

End MinimalCounterExample.

(* Used for symmetry disposition, and flipped configuration match. *)
Lemma minimal_counter_example_mirror : forall G,
  minimal_counter_example G -> minimal_counter_example (mirror G).
Proof.
move=> G; do 4![case] => planarG bridge'G plainG cubicG noncolG minG.
split; last 1 [by move/colorable_mirror | by []].
split; last by rewrite precubic_mirror.
split; last by rewrite plain_mirror.
split; last by rewrite bridgeless_mirror.
by rewrite planar_mirror.
Qed.

Section ConfigurationProperties.

Variables (n0 : nat) (G : hypermap) (r cc : seq G).

(******************************************************************************)
(*   We state and prove separately the geometrical and semantic requirements  *)
(* on configurations. The former ("embeddable") are established by the quiz   *)
(* construction; the latter ("C_reducible") by the reducibility check.        *)
(*   The geometrical requirements are that configuration maps must be plain   *)
(* quasicubic planar bridgeless maps with a simple ring, that satisfy two     *)
(* additional conditions: the ring faces arities must be in the 3..6 range,   *)
(* and the kernel must have radius 2. These two additional properties are     *)
(* used in embed.v to extend a partial hypermap morphism into an embedding.   *)
(******************************************************************************)

Definition good_ring_arity (x : G) : bool := pred4 3 4 5 6 (order face x).

Section Radius2.

(******************************************************************************)
(*   Since our configuration maps have at most one "bridge" face, we can use  *)
(* a slightly more restrictive definition of "radius 2" : we insist that      *)
(* every region is a exactly two adj "hops" away from the center rather than  *)
(* just "at most two" (the extra requirement will always be met, because we   *)
(* can always take a detour through an adjacent spoke. The weaker definition  *)
(* is more complex, and in particular it's easier to check the stricter       *)
(* condition using the configuration data.                                    *)
(******************************************************************************)

Variable A : pred G.

Definition at_radius2 := [rel x y | ~~ [disjoint adj y & [predI adj x & A]]].

Lemma at_radius2P {x y} :
   fclosed face A ->
 reflect (exists x', exists2 y', cface x x' /\ cface y y'
                               & edge x' \in A /\ cface (edge x') (edge y'))
         (at_radius2 x y).
Proof.
move=> clFA; apply: (iffP pred0Pn); case.
  move=> z /and3P[/adjP[y' yFy' y'Rz] /adjP[x' xHx' x'Rz] Az].
  exists x', y' => //; split; first by rewrite (closed_connect clFA x'Rz).
  by rewrite (same_cface x'Rz) cfaceC.
move=> x' [y' [xFx' yFy'] [Aex' ex'Fey']]; exists (edge x').
by rewrite !inE /in_mem /= (adjF xFx') (adjF yFy') (adjFr ex'Fey') !adjE.
Qed.

Definition radius2 := ~~ [disjoint A & [pred x | A \subset at_radius2 x]].

Lemma radius2P :
  reflect (exists2 x, x \in A & {subset A <= at_radius2 x}) radius2.
Proof.
apply: (iffP pred0Pn) => [[x /andP[]] | [x]] Ax /subsetP; exists x => //.
by rewrite !inE Ax.
Qed.

End Radius2.

Record embeddable : Prop := Embeddable {
  embeddable_base :> scycle_planar_bridgeless_plain_quasicubic_connected r;
  embeddable_ring : all good_ring_arity r;
  embeddable_kernel : radius2 (kernel r)
}.

Definition sparse (p : seq G) := simple (p : seq (permF G)).

Lemma sparse_cons x p : sparse (x :: p) = ~~ has (cnode x) p && sparse p.
Proof. exact: (@simple_cons (permF G)). Qed.

Lemma sparse_catC p1 p2 : sparse (p1 ++ p2) = sparse (p2 ++ p1).
Proof. exact: (@simple_catC (permF G)). Qed.

Lemma sparse_catCA p1 p2 p3 : sparse (p1 ++ p2 ++ p3) = sparse (p2 ++ p1 ++ p3).
Proof. exact: (@simple_catCA (permF G)). Qed.

Lemma sparse_rot p : sparse (rot n0 p) = sparse p.
Proof. exact: (@simple_rot n0 (permF G)). Qed.

Definition triad (p : seq G) :=
  let adjp y := fband p (edge y) in
  [pred x | (2 < count adjp (orbit face x)) && ~~ (p \subset adj x)].

Record valid_contract : Prop := ValidContract {
  valid_contract_is_off_ring : [disjoint r & insertE cc];
  valid_contract_is_sparse : sparse (insertE cc);
  valid_contract_size : pred4 1 2 3 4 (size cc);
  valid_contract_triad :
     size cc = 4 -> ~~ [disjoint kernel r & triad (insertE cc)]
}.

Record C_reducible : Prop := Creducible {
  C_reducible_base :> valid_contract;
  C_reducible_coclosure : forall et : colseq,
    cc_ring_trace cc (rev r) et -> Kempe_coclosure (ring_trace (rev r)) et
}.

End ConfigurationProperties.

Arguments good_ring_arity {G} x.
Arguments radius2 {G} A.
Arguments sparse {G} p.
Arguments triad {G} p.

Section Preembedding.

(******************************************************************************)
(*   The properties of the partial morphism contructed in quiz, and extended  *)
(* to an embedding in embed. The morphism is only defined on the kernel of    *)
(* the configuration. On this subset, it should be a strict morphism for face *)
(* and arity. The darts on which it commutes with edge should form an         *)
(* rlink-connected cover of the kernel, up to cface.                          *)
(******************************************************************************)

Variables (G G' : hypermap) (A : pred G) (h : G -> G').

Definition edge_central := [pred x | h (edge x) == edge (h x)].

Lemma edge_central_edge : plain G -> plain G' ->
  forall x, edge_central (edge x) = edge_central x.
Proof.
move=> plainG plainG' x; rewrite /= eq_sym plain_eq //.
by rewrite (canF_eq (plain_eq plainG')).
Qed.

Record preembedding : Prop := Preembedding {
  preembedding_face : {in A, {morph h: x / face x}};
  preembedding_arity : {in A, {mono h: x / order face x}};
  preembedding_cover : A \subset fclosure face edge_central;
  preembedding_rlinked : rlink_connected [predI A & edge_central]
}.

Lemma preembedding_simple_path : preembedding -> fclosed face A ->
    forall x y, edge x \in A -> y \in A ->
 exists2 p, [/\ path rlink x p, cface (last x p) y & p != [::]]
          & simple p /\ all [predI A & edge_central] p.
Proof.
case=> _ _ hfA heA Af x y Aex Ay; set B := [predI A & edge_central].
have /pred0Pn[z /andP[/= exFz zcE]] := subsetP hfA _ Aex.
have{hfA} /pred0Pn[t /andP[/= yFt tcE]] := subsetP hfA _ Ay.
have Bz: B z by rewrite !inE -[_ \in _](closed_connect Af exFz) Aex.
have Bt: B t by rewrite !inE -[_ \in _](closed_connect Af yFt) Ay.
have{heA} [p nfzRp Bp] := heA _ _ Bz Bt; rewrite -/B in Bp.
have{nfzRp} xRp: path rlink x (rcons p t).
  by move: nfzRp; rewrite headI /= {1}/rlink faceK -(same_cface exFz).
have [q [xRq Uq] [Eq Eq0 /allP sqp]] := simplify_rlink xRp.
exists q; split=> //; first by rewrite -Eq last_rcons cfaceC.
  by rewrite (sameP eqP nilP) -Eq0 headI.
by apply/allP=> u /sqp; apply/allP; rewrite all_rcons Bt.
Qed.

End Preembedding.

Arguments edge_central {G G'} h.
