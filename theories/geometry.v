(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype path fingraph.
From fourcolor Require Import hypermap jordan.

(******************************************************************************)
(* The geometrical interpretation of hypermap, the definition of most of the  *)
(* geometrical notions relevant to the statement and proof of the Four Color  *)
(* Theorem. For G : hypermap we define :                                      *)
(*   bridgeless G <-> no face (F-cycle) of G contains both ends of an E-link. *)
(*     loopless G <-> no node (N-cycle) of G contains both ends of an E-link. *)
(*        plain G <-> all edges (E-cycles) of G have size 2.                  *)
(*        cubic G <-> all nodes (N-cycles) of G have size 3.                  *)
(*     precubic G <-> all nodes of G have size at most 3.                     *)
(*   quasicubic r <-> all nodes of G not contained in r have size 3.          *)
(*        arity z == the face order of z : G, i.e., #|cface z|.               *)
(*   pentagonal G <-> all faces of G have size at least 5.                    *)
(*       simple p <=> p : seq G is face-simple: no two darts in p lie in the  *)
(*                   same face.                                               *)
(*   simple_rec p <=> alternative recursive definition of simple p.           *)
(*     scycle e p <-> p is simple and e-cyclic.                               *)
(*      rlink x y <=> y is in the same face as node x (:= cface (node x) y).  *)
(* --> We refer to rlink paths as R-paths, and rlink cycles as R-cycles.      *)
(*     srpath x p <=> x :: p is a simple R-path.                              *)
(*      srcycle r <=> r is a simple R-cycle                                   *)
(* --> We refer to simple R-cycles as 'rings'.                                *)
(*  rlink_connected A <-> A is R-path connected (with paths included in A).   *)
(*   Note that N-paths are always R-paths and that contours contain a uniq    *)
(* R-cyclic subsequence, from which they can be reconstructed. This R-cycle   *)
(* is a ring for simple contours, and indeed any ring corresponds to a simple *)
(* contour in this way.                                                       *)
(*      fproj r x <=> some y in the intersection of r and the face of x, else *)
(*                    froot face x; usually r is simple, so y is unique.      *)
(*      fband p x <=> x is in the face closure of p : seq G.                  *)
(*     kernel p x <=> x is NOT in fband p; usually p is a node (N-cycle) that *)
(*                   delimits G so kernel p is the union of the "inner" faces *)
(*                   of G, that do not intersect with p.                      *)
(*        adj x y <=> x and y belong to adjacent faces, that contain the ends *)
(*                    of an N-link (i.e., rlink z y for some z in cface x).   *)
(*    chordless r <=> no non-consecutive darts in the cycle r belong to       *)
(*                    adjacent faces (r is usually a ring).                   *)
(*       insertE p == the edge closure of p, when G is plain; more precisely, *)
(*                    [:: e1; edge e1; ...; e_n; edge e_n] when p : seq G is  *)
(*                    [:: e1; ... ; e_n].                                     *)
(* Several of the Prop predicates above just encapsulate coercions of bool    *)
(* predicates, which are exposed by bool equivalences in patch.v:             *)
(*  bridgelessb G <=> bool version of bridgeless G.                           *)
(*       plainb G <=> bool version of plain G.                                *)
(*       cubicb A <=> all darts in A belong to cubic nodes (both cubic G and  *)
(*                    quasicubic r are derived from this).                    *)
(*    scycleb e p <=> bool version of scycle e p.                             *)
(* We use a set of record declarations with self-explanatory names to regroup *)
(* geometrical properties as they are used at various points in the proof:    *)
(*   planar_bridgeless -- in combinatorial4ct (main assumption).              *)
(*   planar_bridgeless_plain_precubic -- in combinatorial4ct, coloring        *)
(*                                       (inductive assumption).              *)
(*   planar_bridgeless_plain_connected -- in revsnip.                         *)
(*   plain_cubic -- in quiz, quiztree, part.                                  *)
(*   plain_quasicubic r -- in quiz; r is the configuration perimeter.         *)
(*   plain_cubic_pentagonal -- in part, redpart and hubcap.                   *)
(*   planar_plain_cubic_connected -- in discharge.                            *)
(*   plain_cubic_connected -- special "cubic" form of the Euler formula.      *)
(*   ucycle_plain_quasicubic_connected r -- Euler formula for a configuration *)
(*     with perimeter r; ucycle refers to the assumption r is a uniq N-cycle. *)
(*   ucycle_planar_plain_quasicubic r -- in kempe.                            *)
(*   scycle_planar_bridgeless_plain_quasicubic_connected r -- in redpart,     *)
(*     embed; scycle refers to the assumption r is a face-simple N-cycle.     *)
(* Note that walkup, jordan, snip, sew, patch, and cube do not require any    *)
(* of these geometry assumptions (indeed, in cube we refine an arbitrary map  *)
(* to a plain cubic one). In contrast, in quiz and embed we build and use an  *)
(* embedding of a configuration map in the map to be colored, so we need two  *)
(* sets of assumptions.                                                       *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section BridgeAndLoopLess.

Variable G : hypermap.

Definition bridgelessb := ~~ [exists x : G, cface x (edge x)].
Definition bridgeless : Prop := ~~ [exists x : G, cface x (edge x)].

Lemma bridgeless_cface : bridgeless -> forall x : G, cface x (edge x) = false.
Proof. by move/negbNE/pred0P. Qed.

Definition loopless : Prop := ~~ [exists x : G, cnode x (edge x)].

End BridgeAndLoopLess.

Lemma bridgeless_dual G : bridgeless (dual G) = loopless G.
Proof.
congr (~~ ~~ _ = _); apply/pred0P/pred0P => /(_ _) /= loop'G x /=.
  by rewrite cnodeC -(same_fconnect_finv nodeI) -{2}(finv_f edgeI x) loop'G.
by rewrite (same_fconnect_finv nodeI) cnodeC -{2}(f_finv edgeI x) loop'G.
Qed.

Lemma bridgeless_mirror G : bridgeless (mirror G) = bridgeless G.
Proof.
congr (~~ ~~ _ = _); apply/pred0P/pred0P => [] /(_ _) /= bridge'G x /=.
  rewrite cfaceC -{2}[x]edgeK cface1 cface1r -(same_fconnect_finv faceI).
  exact: bridge'G.
rewrite (same_fconnect_finv faceI) cfaceC /comp -cface1 -{2}[x]nodeK -cface1r.
exact: bridge'G.
Qed.

Section EqmBridgeLess.

Variables G G' : hypermap.
Hypothesis eqG : G =m G'.

Lemma eqm_bridgeless : bridgeless G = bridgeless G'.
Proof.
congr (~~ _ = _); case: G eqG => [d e n f GeK] [e' n' f' G'eK /= eqE _ eqF].
by apply: eq_existsb => x; rewrite eqE; apply: eq_fconnect.
Qed.

Lemma eqm_loopless : loopless G = loopless G'.
Proof.
congr (~~ _ = _); case: G eqG => [d e n f GeK] [e' n' f' G'EK /= eqE eqK _].
by apply: eq_existsb => x; rewrite eqE; apply: eq_fconnect.
Qed.

End EqmBridgeLess.

(*   Since edge and node arity are fixed, face arity plays a central role    *)
(* in the theory, so we use a special `arity' syntax to refer to it.         *)

Notation "@ 'arity' G" := (@order G face)
  (at level 10, G at level 8, format "'@' 'arity'  G").
Notation arity := (@arity _).

Section FacePaths.

(* Arity lemmas, and the other face-centric notions: simple paths, their    *)
(* projection, ring band, and (outer) ring kernel.                          *)

Variables (n0 : nat) (G : hypermap).
Implicit Types x y : G.

Lemma arity_cface x y : cface x y -> arity x = arity y.
Proof. by move=> xFy; apply: (eq_card (same_cface xFy)). Qed.

Lemma arity_iter_face n x : arity (iter n face x) = arity x.
Proof. by apply: arity_cface; rewrite cfaceC fconnect_iter. Qed.

Lemma arity_face x : arity (face x) = arity x.
Proof. exact: (arity_iter_face 1). Qed.

Lemma iter_face_arity x : iter (arity x) face x = x.
Proof. exact/iter_order/faceI. Qed.

Lemma iter_face_subn n x :
  n <= arity x -> iter (arity x - n) face (iter n face x) = x.
Proof. by move=> le_n_x; rewrite -iterD subnK ?iter_face_arity. Qed.

Lemma arity_mirror : @arity (mirror G) =1 @arity G.
Proof. by move=> x; apply/eq_card/(cface_mirror x). Qed.

Section SimplePaths.

Variables (e : rel G) (p : seq G).

Definition fband : pred G := fun x => has (cface x) p.

Lemma ring_fband : p \subset fband.
Proof. by apply/subsetP => x px; apply/hasP; exists x. Qed.

Lemma fbandF : fclosed face fband.
Proof.
apply: (intro_closed cfaceC) => x _ /eqP <- /hasP[z pz xFz]; apply/hasP.
by exists z; last by rewrite -cface1.
Qed.

(* kernel can be defined as the complement of band, since it is only used *)
(* when r is the outer ring of a configuration.                           *)

Definition kernel : pred G := [predC fband].

Lemma kernel_off_ring : kernel \subset [predC p].
Proof.
by rewrite -disjoint_subset disjoint_sym -subset_disjoint ring_fband.
Qed.

Lemma kernelF : fclosed face kernel.
Proof. exact/predC_closed/fbandF. Qed.

Definition fproj x := nth (froot face x) p (find (cface x) p).

Lemma fprojP x : x \in fband -> fproj x \in p /\ cface x (fproj x).
Proof. by move=> pFx; rewrite /fproj mem_nth ?nth_find // -has_find. Qed.

Lemma fproj_cface x y : cface x y -> fproj x = fproj y.
Proof.
move=> xFy; rewrite /fproj (rootP cfaceC xFy); congr (nth _ p _).
exact/eq_find/(same_cface xFy).
Qed.

Definition simple := uniq (map (froot face) p).

Lemma simple_uniq : simple -> uniq p.
Proof. exact: map_uniq. Qed.

(* scycle is a coercion target. *)
Definition scycleb : bool := cycle e p && simple.
Definition scycle : Prop := cycle e p && simple.

Lemma scycle_cycle : scycle -> cycle e p.
Proof. by case/andP. Qed.

Lemma scycle_simple : scycle -> simple.
Proof. by case/andP. Qed.

Lemma scycle_uniq : scycle -> uniq p.
Proof. by move/scycle_simple; apply simple_uniq. Qed.

Lemma scycle_ucycle : scycle -> ucycle e p.
Proof. by case/andP=> Cp Up; rewrite /ucycle Cp simple_uniq. Qed.

Coercion scycle_ucycle : scycle >-> ucycle.

Lemma simple_fproj : simple -> {in p, fproj =1 id}.
Proof.
rewrite /simple /fproj => Up x px; case/splitPr: px Up => p1 p2.
rewrite map_cat cat_uniq /= => /and3P[_ /norP[p1'Fx _] _].
rewrite find_cat /= connect0 addn0.
case: hasP => [[y py xFy] | _]; last by rewrite nth_cat ltnn subnn.
by case/mapP: p1'Fx; exists y; rewrite ?(rootP cfaceC xFy).
Qed.

Lemma scycle_fproj : scycle -> {in p, fproj =1 id}.
Proof. by move/scycle_simple/simple_fproj. Qed.

Lemma simple_cface : simple -> {in p &, forall x y, cface x y -> x = y}.
Proof.
move=> Up x y px py xFy.
by rewrite -(simple_fproj Up px) (fproj_cface xFy) simple_fproj.
Qed.

Lemma scycle_cface : scycle -> {in p &, forall x y, cface x y -> x = y}.
Proof. by move/scycle_simple/simple_cface. Qed.

Lemma simple_fcard_fband : simple -> fcard face fband = size p.
Proof.
move=> Up; rewrite -(size_map (froot face) p) -(card_uniqP Up).
apply/eq_card=> x; apply/andP/mapP=> [[rFx /hasP[y py xFy]] | [y py ->]].
  by exists y; rewrite // -(rootP cfaceC xFy) (eqP rFx).
split; first exact: (roots_root cfaceC y).
by apply/hasP; exists y; last by rewrite cfaceC connect_root.
Qed.

Lemma scycle_fcard_fband : scycle -> fcard face fband = size p.
Proof. by move/scycle_simple/simple_fcard_fband. Qed.

Lemma predI_cface_simple x : simple -> #|[predI cface x & p]| = (x \in fband).
Proof.
move=> Up; case: (x \in _) / hasP => [[y py xFy] | pF'x]; last first.
  by apply/eq_card0=> y; apply/andP=> [[xFy py]]; case: pF'x; exists y.
rewrite (cardD1 y) inE /= [y \in _]xFy py eq_card0 // => z.
apply/and3P=> [[/= y'z xFz pz]]; case/eqP: y'z.
by apply: simple_cface => //; rewrite -(same_cface xFz).
Qed.

End SimplePaths.

Lemma fband_cons x p y : (y \in fband (x :: p)) = cface y x || (y \in fband p).
Proof. done. Qed.

Lemma fband_rcons x p y :
  (y \in fband (rcons p x)) = cface y x || (y \in fband p).
Proof. exact: has_rcons. Qed.

Lemma fband_nseq x y :
  cface x y -> forall n, fband (nseq n x) =i fband (nseq n y).
Proof.
move=> xFy n z; rewrite !unfold_in.
by elim: n => //= n <-; rewrite !(cfaceC z) (same_cface xFy).
Qed.

Fixpoint simple_rec (p : seq G) : bool :=
  if p is x :: p' then (x \notin fband p') && simple_rec p' else true.

Lemma simple_recI : simple =1 simple_rec.
Proof.
rewrite /simple; elim=> //= x p ->; congr (~~ _ && _).
by apply/mapP/hasP=> [] [y py /(rootP cfaceC)]; exists y.
Qed.

Lemma simple_cons x p : simple (x :: p) = (x \notin fband p) && simple p.
Proof. by rewrite !simple_recI. Qed.

Lemma fband_cat p1 p2 x :
  (x \in fband (p1 ++ p2)) = (x \in fband p1) || (x \in fband p2).
Proof. exact: has_cat. Qed.

Lemma fproj_cons x p y :
  fproj (x :: p) y = (if cface x y then x else fproj p y).
Proof. by rewrite /fproj /= cfaceC; case: ifP. Qed.

Lemma fproj_cat p1 p2 x :
  fproj (p1 ++ p2) x = fproj (if x \in fband p1 then p1 else p2) x.
Proof.
elim: p1 => [|y p1 IHp1] //=; rewrite fband_cons cfaceC fproj_cons IHp1.
by case: ifP => yFx /=; last case: ifP => // _; rewrite fproj_cons yFx.
Qed.

Lemma has_fband_sym p1 p2 : has (mem (fband p1)) p2 = has (mem (fband p2)) p1.
Proof.
apply/hasP/hasP=> [] [x px /hasP[y py xFy]];
  by exists y => //; apply/hasP; exists x; rewrite // cfaceC.
Qed.

Lemma simple_cat p1 p2 :
  simple (p1 ++ p2) = [&& simple p1, ~~ has (mem (fband p1)) p2 & simple p2].
Proof.
rewrite !simple_recI has_fband_sym; elim: p1 => [|x p1 IHp1] //=.
by rewrite fband_cat IHp1 !negb_or -!andbA; do !bool_congr.
Qed.

Lemma simple_rcons x p : simple (rcons p x) = (x \notin fband p) && simple p.
Proof. by rewrite -cats1 simple_cat andbT /= orbF andbC. Qed.

Lemma simple_catC p1 p2 : simple (p1 ++ p2) = simple (p2 ++ p1).
Proof. by rewrite /simple !map_cat uniq_catC. Qed.

Lemma simple_catCA p1 p2 p3 : simple (p1 ++ p2 ++ p3) = simple (p2 ++ p1 ++ p3).
Proof. by rewrite /simple !map_cat uniq_catCA. Qed.

Lemma fband_rot p : fband (rot n0 p) =i fband p.
Proof. by move=> x; apply: has_rot. Qed.

Lemma simple_rot p : simple (rot n0 p) = simple p.
Proof. by move=> *; rewrite /simple map_rot rot_uniq. Qed.

Lemma rot_scycle e p : scycle e (rot n0 p) = scycle e p.
Proof. by rewrite /scycle rot_cycle simple_rot. Qed.

Lemma fproj_rot p : simple p -> fproj (rot n0 p) =1 fproj p.
Proof.
move=> Up x; have [pFx | pF'x] := boolP (x \in fband p); last first.
  by rewrite /fproj !nth_default // leqNgt -has_find // has_rot.
case/fprojP: pFx; move: (fproj p x) => y py xFy.
by rewrite (fproj_cface _ xFy) simple_fproj ?simple_rot ?mem_rot.
Qed.

Lemma eq_simple p q :
  fband p =i fband q -> size p = size q -> simple p = simple q.
Proof.
move=> eq_fband eq_sz; apply/eq_uniq=> [|x]; first by rewrite !size_map.
apply/mapP/mapP=> [[y q_y] | [y p_y]] -> {x}.
  have: (y \in fband q) by rewrite -eq_fband (subsetP (ring_fband _)).
  by case/hasP=> z qz yFz; exists z; last by rewrite (rootP cfaceC yFz).
have: (y \in fband p) by rewrite eq_fband (subsetP (ring_fband _)).
by case/hasP=> [z pz yFz]; exists z; last by rewrite (rootP cfaceC yFz).
Qed.

Lemma simple_rev p : simple (rev p) = simple p.
Proof. by rewrite /simple map_rev rev_uniq. Qed.

Lemma fband_rev p : fband (rev p) =i fband p.
Proof. by move=> x; apply: {x} eq_has_r => x; apply: mem_rev. Qed.

End FacePaths.

Lemma simple_map (G G' : hypermap) (h : G -> G') :
    (forall x y, cface (h x) (h y) = cface x y) ->
  forall p, simple (map h p) = simple p.
Proof.
move=> eq_hF; elim=> [|x p IHp] //; rewrite map_cons !simple_cons {}IHp.
by congr (~~ _ && _); elim: p => // y p IHp; rewrite !fband_cons eq_hF IHp.
Qed.

Notation sfcycle f := (scycle (frel f)).

Arguments fband {G} p x.
Arguments kernel {G} p x : rename.
Arguments fproj {G} p x.
Arguments simple {G} p.
Arguments simple_rec {G} p.
Arguments scycle {G} e p.

(* Special geometries: plain map (binary edges), cubic map (ternary nodes),   *)
(* precubic map (at most ternary nodes), pentagonal map (faces 5-ary, at      *)
(* least). The reduction to plain cubic map will be established in cube.v.    *)
(* All these predicates take a set argument, as we also consider quasi-plain  *)
(* / quasi-cubic map, that are only plain / cubic on a subset of the darts.   *)

Section SpecialMaps.

Variable G : hypermap.
Implicit Types (x y : G) (A : pred G).

Definition plainb A := A \subset order_set edge 2.
Definition plain : Prop := plainb G.

Lemma plainP A :
  reflect {in A, forall x, edge (edge x) = x /\ edge x != x} (plainb A).
Proof.
apply: (iffP subsetP) => plainA x Ax.
  have oEx: order edge x = 2 by apply/eqP; apply: plainA.
  split; first by rewrite -{2}(iter_order edgeI x) oEx.
  by have:= orbit_uniq edge x; rewrite /orbit oEx /= andbT inE eq_sym.
have [eex_x x'ex] := plainA x Ax.
have Ce2x: fcycle edge [:: x; edge x] by rewrite /= eex_x !eqxx.
by apply/eqP/(order_cycle Ce2x); rewrite ?mem_head //= andbT inE eq_sym.
Qed.

Lemma plain_eq : plain -> forall x, edge (edge x) = x.
Proof. by move/plainP=> plainG x; case: (plainG x). Qed.

Lemma plain_eq' : plain -> forall x, node (face x) = edge x.
Proof. by move=> plainG x; rewrite -{2}[x]faceK plain_eq. Qed.

Lemma plain_neq : plain -> forall x, (edge x == x) = false.
Proof. by move/plainP=> plainG x; apply/idPn; case: (plainG x). Qed.

Lemma plain_orbit : plain -> forall x y, cedge x y = (y \in [:: x; edge x]).
Proof.
by move/subsetP=> plainG x y; rewrite fconnect_orbit /orbit (eqnP (plainG x _)).
Qed.

Definition cubicb A := A \subset order_set node 3.
Definition cubic : Prop := cubicb G.
Definition precubic : Prop := G \subset [pred x | order node x <= 3].

Lemma cubicP A :
  reflect {in A, forall x, node (node (node x)) = x /\ node x != x} (cubicb A).
Proof.
apply: (iffP subsetP) => cubicA x Ax.
  have oNx: order node x = 3 by apply/eqP; apply: cubicA.
  split; first by rewrite -{2}(iter_order nodeI x) oNx.
  by move: (orbit_uniq node x); rewrite /orbit oNx eq_sym => /andP[/norP[]].
have [n3x_x x'nx] := cubicA x Ax.
have cycN3x: fcycle node (traject node x 3) by rewrite /= n3x_x !eqxx.
apply/eqP/(order_cycle cycN3x); last exact: mem_head.
by rewrite /= !inE negb_or -{3}n3x_x !(inj_eq nodeI) eq_sym x'nx.
Qed.

Lemma cubic_eq : cubic -> forall x, node (node (node x)) = x.
Proof. by move/cubicP=> cubicG x; case: (cubicG x). Qed.

Lemma cubic_eq' : cubic -> forall x, node (node x) = face (edge x).
Proof. by move=> cubicG x; rewrite -{1}[x]edgeK cubic_eq. Qed.

Lemma cubic_neq : cubic -> forall x, (node x == x) = false.
Proof. by move/cubicP=> cubicG x; apply/idPn; case: (cubicG x). Qed.

Lemma cubic_orbit :
  cubic -> forall x y, cnode x y = (y \in [:: x; node x; node (node x)]).
Proof.
by move/subsetP=> cubicG x y; rewrite fconnect_orbit /orbit (eqnP (cubicG x _)).
Qed.

Lemma precubic_leq : precubic -> forall x, order node x <= 3.
Proof. by move/subsetP/in1T. Qed.

Lemma cubic_precubic : cubic -> precubic.
Proof.
by move/subsetP=> cubicG; apply/subsetP => x /cubicG/eqnP <-; apply: leqnn.
Qed.

Definition pentagonal : Prop := forall x, 4 < arity x.

(* Requirement for the four color theorem. *)
Record planar_bridgeless : Prop := PlanarBridgeless {
  planar_bridgeless_is_planar :> planar G;
  planar_bridgeless_is_bridgeless :> bridgeless G
}.

(* Required by quiz, quiztree, part. *)
Record plain_cubic : Prop := PlainCubic {
  plain_cubic_is_plain :> plain;
  plain_cubic_is_cubic :> cubic
}.

(* Required for special Euler formula. *)
Record plain_cubic_connected : Prop := PlainCubicConnected {
  plain_cubic_connected_base :> plain_cubic;
  plain_cubic_connected_is_connected :> connected G
}.

(* Required by discharge. *)
Record planar_plain_cubic_connected : Prop := PlanarPlainCubicConnected {
  planar_plain_cubic_connected_base :> plain_cubic_connected;
  planar_plain_cubic_connected_is_planar :> planar G
}.

(* Required by part, redpart, hubcap. *)
Record plain_cubic_pentagonal : Prop := PlainCubicPentagonal {
  plain_cubic_pentagonal_base :> plain_cubic;
  plain_cubic_pentagonal_is_pentagonal :> pentagonal
}.

(* Factored intermediate signature. *)
Record planar_bridgeless_plain : Prop := PlanarBridgelessPlain {
  planar_bridgeless_plain_base :> planar_bridgeless;
  planar_bridgeless_plain_is_plain :> plain
}.

(* Required by revsnip. *)
Record planar_bridgeless_plain_connected : Prop :=
PlanarBridgelessPlainConnected {
  planar_bridgeless_plain_connected_base :> planar_bridgeless_plain;
  planar_bridgeless_plain_connected_is_connected :> connected G
}.

(* Inductive assumption. *)
Record planar_bridgeless_plain_precubic : Prop :=
PlanarBridgelessPlainPrecubic {
  planar_bridgeless_plain_precubic_base :> planar_bridgeless_plain;
  planar_bridgeless_plain_precubic_is_precubic :> precubic
}.

Section QuasicubicMaps.

Variable r : seq G.

Definition quasicubic : Prop := cubicb [predC r].

Lemma quasicubic_eq :
  quasicubic -> forall x, x \notin r -> node (node (node x)) = x.
Proof. by move/cubicP=> cubicG x /cubicG[]. Qed.

(* Required by quiz. *)
Record plain_quasicubic : Prop := PlainQuasicubic {
  plain_quasicubic_is_plain :> plain;
  plain_quasicubic_is_quasicubic :> quasicubic
}.

(* Intermediate common base *)
Record ucycle_plain_quasicubic : Prop := UcyclePlainQuasicubic {
  ucycle_plain_quasicubic_base :> plain_quasicubic;
  ucycle_plain_quasicubic_is_ucycle :> ufcycle node r
}.

(* Required by kempe. *)
Record ucycle_planar_plain_quasicubic : Prop := UcyclePlanarPlainQuasicubic {
  ucycle_planar_plain_quasicubic_base :> ucycle_plain_quasicubic;
  ucycle_planar_plain_quasicubic_is_planar :> planar G
}.

(* Required by for special Euler formula *)
Record ucycle_plain_quasicubic_connected : Prop :=
UcyclePlainQuasicubicConnected {
  ucycle_plain_quasicubic_connected_base :> ucycle_plain_quasicubic;
  ucycle_plain_quasicubic_connected_is_connected :> connected G
}.

(* Required by embed and redpart. Two additional geometrical conditions are   *)
(* also needed; these will be defined below, but will assumed separately in   *)
(* reducible.v, along with reducibility.                                      *)
Record scycle_planar_bridgeless_plain_quasicubic_connected : Prop :=
ScyclePlanarBridgelessPlainQuasicubicConnected {
  scycle_planar_bridgeless_plain_quasicubic_connected_base :>
    ucycle_plain_quasicubic_connected;
  scycle_planar_bridgeless_plain_quasicubic_connected_is_simple : simple r;
  scycle_planar_bridgeless_plain_quasicubic_connected_is_planar :> planar G;
  scycle_planar_bridgeless_plain_quasicubic_connected_is_bridgeless
    :> bridgeless G
}.

Lemma scycle_planar_bridgeless_plain_quasicubic_connected_is_scycle :
  scycle_planar_bridgeless_plain_quasicubic_connected -> sfcycle node r.
Proof. by do 3![case] => _ /andP[] *; apply/andP. Qed.

Coercion scycle_planar_bridgeless_plain_quasicubic_connected_is_scycle :
  scycle_planar_bridgeless_plain_quasicubic_connected >-> scycle.

Definition scycle_planar_bridgeless_plain_quasicubic_connected_pbpc_base :
  scycle_planar_bridgeless_plain_quasicubic_connected
    -> planar_bridgeless_plain_connected.
by do 4!case.
Defined.

Coercion scycle_planar_bridgeless_plain_quasicubic_connected_pbpc_base :
 scycle_planar_bridgeless_plain_quasicubic_connected
   >-> planar_bridgeless_plain_connected.

(* The special form of the Euler formula for plain quasicubic connected maps. *)
Lemma quasicubic_Euler : ucycle_plain_quasicubic_connected ->
  let nb_face := ~~ nilp r + fcard face G in
  planar G = (6 * nb_face == #|G| + ((size r).*2 + 12)).
Proof.
move=> [] [] [plainG cubicG] /andP[cycNr Ur] ccG.
congr (is_true _); transitivity (6 * Euler_lhs G == 6 * Euler_rhs G).
  rewrite eqn_pmul2l // -(inj_eq double_inj) -(eqn_add2r (Euler_rhs G)).
  by rewrite -even_genusP.
set szr := size r; set nbF := fcard face G.
rewrite /Euler_rhs -/nbF; set nbE := fcard edge G; set nbN := fcard node G.
have DnbE: #|G| = 2 * nbE.
  by apply: eqP; rewrite mulnC -(fcard_order_set edgeI plainG).
have [nn DnbN Dnn]: exists2 nn, nbN = ~~ nilp r + nn & #|G| = szr + 3 * nn.
  exists (fcard node [predC r]).
    rewrite [nbN](n_compC (mem r)); congr (_ + _).
    case Dr: r => [|x r1]; first by apply: eq_card0 => x; rewrite !inE andbF.
    apply: etrans (n_comp_connect cnodeC x); apply/esym/eq_n_comp_r.
    by apply: fconnect_cycle; rewrite ?mem_head // -Dr.
  have clNr: fclosed node [predC r].
    apply: predC_closed; apply: (intro_closed cnodeC) => /= x _ /eqP <- rx.
    by rewrite -(fconnect_cycle cycNr rx); apply: fconnect1.
  rewrite -[szr](card_uniqP Ur) -(cardC (mem r)); congr (_ + _); apply: eqP.
  by rewrite mulnC -(fcard_order_set nodeI cubicG).
rewrite /Euler_lhs (eqnP ccG) mulnDr -[6 * _]/12 -{2}[6]/(1 + 2 + 3).
rewrite 2!{1}mulnDl mul1n {2}Dnn {2}DnbE mulnDr !mulnA !mul2n muln2.
rewrite (addnC nbN) DnbN !mulnDr 3!addnA addnC eqn_add2l addnA eqn_add2r.
by rewrite -addnA addnC -addnA eq_sym addnC.
Qed.

End QuasicubicMaps.

(* The special form of the Euler formula for plain cubic connected maps. *)

Lemma cubic_Euler : plain_cubic_connected ->
  planar G = (6 * fcard face G == #|G| + 12).
Proof. by do 2![case] => *; rewrite (@quasicubic_Euler nil). Qed.

End SpecialMaps.

Arguments plainP {G A}.
Arguments cubicP {G A}.

Section MirrorSpecials.

Variable G : hypermap.

Lemma plain_dual : plain (dual G) = plain G.
Proof.
congr (is_true _); apply: eq_subset_r => x.
by rewrite /order_set /in_mem /= (order_finv edgeI).
Qed.

Lemma plain_mirror : plain (mirror G) = plain G.
Proof.
congr (is_true _); apply/subsetP/subsetP=> plainG x _; rewrite !inE.
  by rewrite -[x]edgeK -order_mirror_edge; apply: plainG.
by rewrite /order_set order_mirror_edge; apply: plainG.
Qed.

Lemma cubic_mirror : cubic (mirror G) = cubic G.
Proof.
congr (is_true _); apply: eq_subset_r => x.
by rewrite !inE /= (order_finv nodeI).
Qed.

Lemma precubic_mirror : precubic (mirror G) = precubic G.
Proof.
congr (is_true _); apply: eq_subset_r => x.
by rewrite !inE /= (order_finv nodeI).
Qed.

End MirrorSpecials.

Section Adj.

Variables (n0 : nat) (G : hypermap).
Implicit Types x y : G.

Definition rlink : rel G := fun x => cface (edge x).

Lemma rlinkE x : rlink x (edge x).
Proof. exact: connect0. Qed.

Lemma rlinkFr y1 y2 : cface y1 y2 -> forall x, rlink x y1 = rlink x y2.
Proof.
by move=> y1Fy2 x; rewrite /rlink !(cfaceC (edge x)) (same_cface y1Fy2).
Qed.

Fixpoint srpath x0 x p : bool :=
  if p is y :: p' then
    [&& cface (edge x) y, all (predC (cface x)) p' & srpath x0 y p']
  else cface (edge x) x0.

Definition srcycle r := if r is x :: p then srpath x x p else true.

Lemma srcycleI : bridgeless G -> forall r, scycle rlink r = srcycle r.
Proof.
move=> bridge'G [|x0 p] //; rewrite /scycle simple_recI /=; congr (is_true _).
elim: p {1 3 5}x0 => [|y p IHp] x /=; first by rewrite !andbT.
rewrite -{}IHp -!andbA unfold_in /=; apply: andb_id2l => exFy.
bool_congr; congr (_ && _); rewrite cfaceC -(same_cface exFy) cfaceC.
by rewrite bridgeless_cface // -all_predC.
Qed.

Definition rlink_connected (a : pred G) :=
  {in a &,
     forall x y, exists2 p, path rlink (node (face x)) (rcons p y) & all a p}.

Lemma simplify_rlink x p :
   path rlink x p ->
 exists2 p', path rlink x p' /\ simple p'
          & [/\ last x p = last x p', nilp p = nilp p' & all [mem p] p'].
Proof.
elim: {p}_.+1 x {-2}p (ltnSn (size p)) => // n IHn x.
case=> [|y p]; [by exists [::] | rewrite /= ltnS] => lt_p_n /andP[xRy yRp].
case pFy: (y \in fband p); last first.
  have{n IHn lt_p_n yRp} [q [xRq Uq] [Lq _ /allP/= sqp]] := IHn y p lt_p_n yRp.
  exists (y :: q); split; rewrite /= ?xRy ?mem_head //=.
    rewrite simple_cons (contraFN _ pFy) // => /hasP[z /sqp qz yFz].
    by apply/hasP; exists z.
  by apply/allP=> z qz; rewrite !inE sqp ?orbT.
case/fprojP: pFy; move: (fproj p y) => z pz yFz.
case/splitPr: pz yRp lt_p_n => p1 p2; rewrite cat_path /= => /and3P[_ _ zRp2].
rewrite last_cat /= size_cat => /(leq_ltn_trans (leq_addl _ _)) lt_p2_n.
have{zRp2} xRp2: path rlink x (z :: p2) by rewrite /= -(rlinkFr yFz) xRy.
have{n IHn lt_p2_n} [q [xRq Uq] [Lq ntq /allP/= sqp2]] := IHn x _ lt_p2_n xRp2.
by exists q; split=> //; apply/allP=> t qt; rewrite !inE mem_cat sqp2 ?orbT.
Qed.

Definition adj : rel G := fun x y => has (fun x' => rlink x' y) (orbit face x).
Canonical adj_app_pred x := ApplicativePred (adj x).

Lemma adjP {x y} : reflect (exists2 z, cface x z & rlink z y) (adj x y).
Proof.
apply: (iffP hasP) => [] [z xFz zRy];
  by exists z; rewrite // -fconnect_orbit in xFz *.
Qed.

Lemma rlink_adj x y : rlink x y -> adj x y.
Proof. by move=> xRy; apply/adjP; exists x. Qed.

Lemma adjE x : adj x (edge x).
Proof. exact/rlink_adj/rlinkE. Qed.

Lemma adjF x1 x2 : cface x1 x2 -> adj x1 =1 adj x2.
Proof.
move=> x1Fx2 y; apply: {y}eq_has_r => y.
by rewrite -!fconnect_orbit (same_cface x1Fx2).
Qed.

Lemma adjFr y1 y2 : cface y1 y2 -> forall x, adj x y1 = adj x y2.
Proof.
move=> y1Fy2 x; apply: {x}eq_has => x.
by rewrite /rlink !(cfaceC (edge x)) (same_cface y1Fy2).
Qed.

Lemma adjF1 x : adj x =1 adj (face x).
Proof. exact/adjF/fconnect1. Qed.

Lemma adjF1r x y : adj x y = adj x (face y).
Proof. exact/adjFr/fconnect1. Qed.

Lemma adjN x : adj (node x) x.
Proof. by rewrite -{2}[x]nodeK -adjF1r adjE. Qed.

Lemma adjC : plain G -> symmetric adj.
Proof.
move=> plainG; apply: symmetric_from_pre => x y /adjP[z xFz zRy].
by apply/adjP; exists (edge z); rewrite /rlink cfaceC ?plain_eq.
Qed.

Lemma no_adj_adj x y1 y2 : ~~ adj x y1 -> adj x y2 -> cface y1 y2 = false.
Proof. by move=> xA'y1 xAy2; apply: contraNF xA'y1 => /adjFr->. Qed.

Lemma adj_no_cface : bridgeless G -> forall x y, adj x y -> cface x y = false.
Proof.
move=> bridge'G x y /adjP[z xFz zRy]; rewrite cfaceC -(same_cface zRy) cfaceC.
by rewrite (same_cface xFz) bridgeless_cface. 
Qed.

Definition chordless (r : seq G) :=
  let non_adj_r x := [predD1 [predD1 r & prev r x] & next r x] in
  r \subset [pred x | [disjoint adj x & non_adj_r x]].

Lemma chordless_rot r : uniq r -> chordless (rot n0 r) = chordless r.
Proof.
move=> Ur; rewrite /chordless (eq_subset (mem_rot n0 r)).
apply: eq_subset_r => x; rewrite !inE (next_rot n0 Ur) (prev_rot n0 Ur).
by apply: eq_disjoint_r => y; rewrite !inE mem_rot.
Qed.

(* Edge closure of a sequence, in a plain graph; used mainly for contracts.  *)

Fixpoint insertE (p : seq G) : seq G :=
  if p is x :: p' then [:: x, edge x & insertE p'] else [::].

Lemma insertE_seqb (b : bool) x :
  insertE (nseq b x) = nseq b x ++ nseq b (edge x).
Proof. by case: b. Qed.

Lemma size_insertE p : size (insertE p) = (size p).*2.
Proof. by elim: p => //= x p ->. Qed.

Lemma insertE_cat p1 p2 : insertE (p1 ++ p2) = insertE p1 ++ insertE p2.
Proof. by elim: p1 => //= x p1 ->. Qed.

Lemma mem_insertE : plain G -> forall p x, (x \in insertE p) = has (cedge x) p.
Proof.
move=> plainG p x; elim: p => //= y p <-.
by rewrite cedgeC [cedge y x](plain_orbit plainG) !inE orbA.
Qed.

Lemma insertE_rot p : insertE (rot n0 p) = rot (double n0) (insertE p).
Proof.
have [p_ge_n0 | p_lt_n0] := leqP (size p) n0.
  by rewrite !rot_oversize // size_insertE leq_double.
rewrite -{2}(cat_take_drop n0 p) {1}/rot !insertE_cat -rot_size_cat.
by rewrite size_insertE (size_takel (ltnW _)).
Qed.

End Adj.

Arguments plainb {G} A.
Arguments cubicb {G} A.
Arguments quasicubic {G} r.
Arguments rlink {G} x y.
Arguments adj {G} x y.
Arguments chordless {G} r.
Arguments insertE {G} p.

