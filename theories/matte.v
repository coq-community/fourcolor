(* (c) Copyright 2006-2015 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import path order ssralg ssrnum ssrint div intdiv.
From fourcolor Require Import grid.

(******************************************************************************)
(* Mattes are finite sets of grid squares that are delimited by a simple grid *)
(* ring; we explicitly include the enumeration of the region and the ring.    *)
(* Mattes will be used to define conservative approximations of arbitrary     *)
(* connected open sets of points (regions). We therefore need to provide      *)
(* operations for extending a matte in order to improve the approximation.    *)
(* This involves three different operations :                                 *)
(*   - adding pixels within a specified rectangle that the matte meets, so    *)
(*     that a specific pixel is covered.                                      *)
(*   - adding the pixels surrounding a grid point of the matte boundary.      *)
(*   - refining the grid to ensure that the two previous operations are safe. *)
(* Note that we can't add a large rectangle blindly to a matte if we want to  *)
(* preserve its geometrical properties (we might end up with a disconnected   *)
(* contour). We reduce the first two operations above to two primitives that  *)
(* add a pixel that has exactly one or two consecutive sides in common with   *)
(* the matte, respectively (more precisely, 2 or 3 consecutive vertices in    *)
(* common with the matte contour vertices). We don't actually provide the     *)
(* second operation here, because it requires multiple grid refinements.      *)
(* Instead we provide a basic step that needs to be iterated to accomplish    *)
(* the operation, along with the metric ("matte_order") that decreases with   *)
(* that step.                                                                 *)
(*   The main definitions in this file are:                                   *)
(*       mrlink d1 d2 <=> the end of grid dart d1 (interpreted as a directed  *)
(*                        grid edge -- see grid.v) coincides with the start   *)
(*                        of grid dart d2. This is the successor relation for *)
(*                        the contour cycle of mattes.                        *)
(*    d \in gborder m <=> d is a border edge of the collection m of pixels    *)
(*                        (represented as a sequence of gpoints): the pixel   *)
(*                        on the left of d interpreted as a directed edge     *)
(*                        (a.k.a. the pixel of d) lies in m, while the one on *)
(*                        the right does not.                                 *)
(*               matte == the representation of a simple grid polymino. An    *)
(*                        m : matte comprises two somewhat redundant data:    *)
(*             mdisk m == a (nonempty) sequence comprising the pixels covered *)
(*                        by m : matte; m coerces to both mdisk m and the     *)
(*                        extent of mdisk m (as a collective predicate).      *)
(*             mring m == the node-simple mring-cycle of darts tracing the    *)
(*                        counterclockwise birder of m : matte.               *)
(*       point_matte p == the matte comprising the single pixel p, with mdisk *)
(*                        pmdisk p := [:: p], and mring pmring p.             *)
(*         madj m1 m2 <=> m1 and m2 are adjacent: their respective borders    *)
(*                        contain converse directed edges, separating two     *)
(*                        pixels on the periphery of m1 and m2.               *)
(*      coarse_in r m <-> within r : grect, the matte m is the binary         *)
(*                        refinement of a coarser region: for all r \in p,    *)
(*                        p \in m depends only on halfg p.                    *)
(*      refine_matte m == the matte that covers exactly the subpixels of m in *)
(*  +--+--+--+            the binary refinement of the grid pixels, with      *)
(*  |  |  |  |            mdisk refine_mdisk and mring refine_mring.          *)
(*  +--+--+--+  ehex d == the 3x2 rectangle covering the pixel of the dart d  *)
(*  |  |d |  |            and the five pixels adjacent to it that are in the  *)
(*  +--+->+--+            half-plane to the left of d interpreted as a        *)
(*                        directed edge.                                      *)
(*  +--+--+    equad d == the 2x2 square covering the pixel of the dart d     *)
(*  |  |  |               and the three pixels adjacent to it that are in     *)
(*  +--+--+               quadrant that is both left of d and of gface d      *)
(*  |  |d | gface d       (the next edge after d in the counter-clockwise     *)
(*  +--+->+               border of the pixel of d -- see grid.v).            *)
(*       ext1_hex m d <=> m contains the pixel to the right of d and none of  *)
(*                        the pixels in ehex d.                               *)
(*     ext1_matte Emd <=> the matte extending a matte m with the pixel p of a *)
(*                        dart d, given a proof Emd of ext1_hex m d, which    *)
(*                        implies p is ouside m and touches the border of m   *)
(*                        on exactly one side, at d. The mdisk of ext1_matte  *)
(*                        is ext_mdisk m d := p :: m and its mring is         *)
(*                        ext1_mring m d.                                     *)
(*      ext2_quad m d <=> m contains the pixels to the right of both d and    *)
(*                        gface d, but none of the pixels in equad d.         *)
(*     ext2_matte Emd <=> the matte extending a matte m with the pixel p of a *)
(*                        dart d, given a proof Emd of ext2_quad m d, which   *)
(*                        implies p is ouside m and touches the border of m   *)
(*                        on exactly two consecutive sides, at d and gface d. *)
(*                        The mdisk ext2_matte is ext_mdisk m d and its mring *)
(*                        is ext1_mring m d.                                  *)
(*  matte_extension m xm <-> inductive (indexed) predicate asserting that     *)
(*                        there is a sequence of mattes from m to xm in which *)
(*                        each matte differs from the next by the addition of *)
(*                        exactly ONE adjacent pixel. We use induction on     *)
(*                        this predicate to obtain an extension that is       *)
(*                        adjacent to a given matte.                          *)
(*   extends_in m r p <-> there is some matte_extension xm of m that contains *)
(*                        p and only extends m inside rectangle r; we show    *)
(*                        this holds whenever m is coarse in r, m meets r,    *)
(*                        and p is strictly inside r (i.e., in inset r).      *)
(*         mcorner m q == the number of pixels incident to grid node q that   *)
(*                        are NOT in matte m, other than (upper right) pixel  *)
(*                        q, with the upper left and lower right pixels       *)
(*                        counted twice and the lower left pixel counted only *)
(*                        once. The assymmetry of this definition reflects    *)
(*                        the assymetry of the extent of a pixel in the real  *)
(*                        plane, which includes only the lower left corner    *)
(*                        and edges. Thus, when p \in m and mcorner m p == 0  *)
(*                        all of the pixel p, including the grid point p and  *)
(*                        edges incident to p, lie in the interior of the     *)
(*                        extent of the matte m. If mcorner m p > 0, for any  *)
(*                        dart q of p, viewed as a subpixel of p, we can      *)
(*                        construct an extension xm of refine_matte m such    *)
(*                        that mcorner xm q < mcorner m p.                    *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Definition mrlink := [rel d1 d2 | end1g d1 == end0g d2].

Definition gborder (m : seq gpoint) :=
  [pred d | halfg d \in m & halfg (gedge d) \notin m].

Record matte := Matte {
  mdisk :> seq gpoint;
  mring : seq gpoint;
  matte_ne : ~~ nilp mdisk;
  mring_cycle : cycle mrlink mring;
  mring_simple : uniq (map end0g mring);
  in_mring : mring =i gborder mdisk
}.

Coercion in_matte m := [pred p | p \in mdisk m].

Lemma mring_edge m p : p \in mring m -> gedge p \notin mring m.
Proof. by rewrite !in_mring !inE => /andP[_ /negPf->]. Qed.

Lemma mring_uniq m : uniq (mring m).
Proof. exact: map_uniq (mring_simple m). Qed.

(* Matte adjacency. *)

Definition madj m1 m2 := has [preim gedge of mring m1] (mring m2).

Lemma madj_sym : symmetric madj.
Proof.
apply/symmetric_from_pre=> m1 m2 /hasP[d m2d m1ed].
by apply/hasP; exists (gedge d); rewrite ?inE ?gedge2.
Qed.

Lemma madj_irrefl : irreflexive madj.
Proof.
by move=> m; apply/hasPn=> d; rewrite !inE !in_mring !inE => /andP[_ /negPf->].
Qed.

(* Initial single_square matte. *)

Section PointMatte.

Variable p : gpoint.

Definition pmdisk : seq gpoint := [:: p].
Definition pmring : seq gpoint := traject gface (p *+ 2) 4.

Lemma pmatte_ne : ~~ nilp pmdisk. Proof. by []. Qed.

Lemma pmring_cycle : cycle mrlink pmring.
Proof. by rewrite /= /mrlink -!end0g_face gface4 !eqxx. Qed.

Lemma pmring_simple : uniq (map end0g pmring).
Proof.
rewrite [map _ _]/= /end0g !halfg_face !oddg_face oddg_double.
by rewrite (map_inj_uniq (addrI _) [:: _; _; _; _]).
Qed.

Lemma in_pmring : pmring =i [pred d | halfg d == p].
Proof.
move=> d; rewrite -[p]halfg_double [RHS]eq_sym.
by apply/idP/eqP=> [/trajectP[i _ ->] | /same_halfg]; rewrite ?halfg_iter_face.
Qed.

Lemma pmring_def : pmring =i gborder pmdisk.
Proof.
move=> x; rewrite in_pmring !inE andb_idr // => /eqP<-.
by rewrite eq_sym neq_halfg_edge.
Qed.

Definition point_matte := Matte pmatte_ne pmring_cycle pmring_simple pmring_def.

End PointMatte.

(* Grid refinement for mattes.                                                *)

Section RefineMatte.

Definition coarse_in (r : gregion) (m : matte) :=
  forall p q, r p -> halfg q = halfg p -> (q \in m) = (p \in m).

Variable m : matte.

Definition refine_mring (mr : seq gpoint) : seq gpoint :=
  flatten [seq [seq p *+ 2 + oddg d | p <- [:: d; gface d]] | d <- mr].

Definition refine_mdisk (md : seq gpoint) : seq gpoint :=
  flatten [seq pmring p | p <- md].

Lemma in_refine_mdisk md p : (p \in refine_mdisk md) = (halfg p \in md).
Proof.
apply/flatten_mapP/idP=> [[x] | ] md_x; first by rewrite in_pmring => /eqP->.
by exists (halfg p); last rewrite in_pmring inE.
Qed.

Lemma refine_matte_ne : ~~ nilp (refine_mdisk m).
Proof. by case: (mdisk m) (matte_ne m). Qed.

Lemma refine_mring_cycle : cycle mrlink (refine_mring (mring m)).
Proof.
case: (mring m) (mring_cycle m) => // [d0 mr0]; rewrite !(cycle_path d0).
rewrite [last _ _]/=; set d := last d0 mr0; set mr := d0 :: mr0.
have ->: last d0 (refine_mring mr) = gface d *+ 2 + oddg d.
  by rewrite [mr]lastI /refine_mring -cats1 map_cat flatten_cat last_cat.
elim: {d0 mr0}mr d => //= d2 _ IHmr d1 /andP[/eqP-Ed12 /IHmr{IHmr}->].
rewrite -!subr_eq /end1g !halfg_eq ?oddg_eq ?eqxx // andbC -addrA eqxx /=.
by rewrite -[gface d1]end0g_eq oddg_face subrK end0g_face Ed12 end0g_eq.
Qed.

Lemma in_refine_mring (mr : seq gpoint) d :
 reflect (exists2 d0, d0 \in mr /\ oddg d = oddg d0
                & halfg d = d0 \/ halfg d = gface d0)
         (d \in refine_mring mr).
Proof.
apply: (iffP flatten_mapP) => [[d0 mr_d0 /mapP[p]] | [d0 [mr_d0 Dd] /pred2P]].
  by rewrite !inE => /pred2P-Dp ->; rewrite !oddg_eq ?halfg_eq //; exists d0.
by exists d0 => //; apply/mapP; exists (halfg d); rewrite ?inE // -Dd halfgK.
Qed.

Lemma refine_mring_simple : uniq (map end0g (refine_mring (mring m))).
Proof.
have /hasPn := @mring_edge m; move: (mring m) (mring_simple m).
elim=> //= d r IHr /andP[r'd Ur] /norP[_]; rewrite has_predU => /norP[r'E /IHr].
move=> -> {Ur}//; rewrite !/(end0g _) !halfg_eq ?oddg_eq // inE -addrA subrK.
rewrite (inj_eq (addrI _)) eq_sym neq_ccw /= andbC.
rewrite !(contra _ r'd) /end0g // => /mapP[d1 /in_refine_mring[d0 [r_d0 ->]]].
  case=> -> Dd; first by rewrite -[_ + _]halfg_add_odd Dd halfg_add_odd map_f.
  have /eqP/idPn[]:= congr1 oddg Dd; rewrite oddg_add oddg_double.
  by rewrite oddg_add oddg_face; case: (oddgP d0).
case=> -> Dd; last rewrite -addrA subrK in Dd.
  have:= congr1 oddg Dd; rewrite [RHS]oddg_add oddg_double.
  by rewrite oddg_add; case: (oddgP d).
suff Dd0: oddg d0 = oddg d by move: Dd; rewrite Dd0 => /addIr->; apply: map_f.
have:= congr1 oddg Dd; rewrite oddg_add [RHS]oddg_add.
have{r'E r_d0}: gedge d0 != d := hasPn r'E d0 r_d0.
by rewrite /gedge 2!addrA -Dd -!addrA -subr_eq0 addrC addKr; do 2!case: oddgP.
Qed.

Lemma refine_mring_def : refine_mring (mring m) =i gborder (refine_mdisk m).
Proof.
move: (mdisk m) (in_mring m) => md Dmr d.
rewrite inE !in_refine_mdisk halfg_edge halfg_add; set p := halfg d.
apply/in_refine_mring/andP=> [[d1 [mr_d1 Dd] Dp] | [md_p md'ep]].
  rewrite Dmr !inE halfg_edge -/p in mr_d1 Dp; have [md_d1] := andP mr_d1.
  by case: Dp => ->; rewrite ?halfg_face ?oddg_face -Dd; case: oddgP.
have Dd: pred2 (oddg d) (ccw (oddg d)) (oddg p).
  by have/(memPn md'ep):= md_p; rewrite addrC -subr_eq subrr; do 2!case: oddgP.
exists (halfg p *+ 2 + oddg d).
  rewrite Dmr !inE halfg_edge halfg_eq ?oddg_eq ?md_p //.
  by case: (oddgP d) (oddgP p) Dd md'ep => -[] //.
rewrite gface_def oddg_eq ?halfg_eq //.
by case/pred2P: Dd => <-; [left | right]; rewrite halfgK.
Qed.

Definition refine_matte :=
  Matte refine_matte_ne refine_mring_cycle refine_mring_simple refine_mring_def.

Lemma in_refine_matte p : (p \in refine_matte) = (halfg p \in m).
Proof. exact: in_refine_mdisk. Qed.

Lemma refine_matte_coarse r : coarse_in r refine_matte.
Proof. by move=> p q _ Dq; rewrite /= !in_refine_matte Dq. Qed.

End RefineMatte.

Section ExtendMatte.

Variable m : matte.

Definition ext_mdisk d : seq gpoint := halfg d :: m.

Lemma ext_mdisk_ne d : ~~ nilp (ext_mdisk d).
Proof. by []. Qed.

Definition ehex d := gchop_rect (gtouch (halfg d)) d.

Definition equad d := gchop_rect (ehex d) (gface d).

Lemma ehexF d : subpred (equad d) (ehex (gface d)).
Proof.
by move=> p; rewrite !(inE, in_gchop_rect) halfg_face andbAC => /andP[].
Qed.

Lemma end0g_equad d : ~~ has (equad (gface d)) m -> m (end0g d) = false.
Proof.
move/hasPn/(_ _)/contraTF; apply; rewrite !(inE, in_gchop_rect) /gchop.
rewrite !halfg_face !oddg_face /end0g; case: (halfg d) => x y.
by case: oddgP; rewrite /= !lter_add2 /= ?ler_addl ?ger_addl.
Qed.

Lemma mring_equad d :
  ~~ has (equad (gface d)) m -> (end0g d \in map end0g (mring m)) = false.
Proof.
move=> m'fd; apply/mapP => -[d1 m_d1 Dp].
rewrite in_mring inE (contraTF (hasPn m'fd _)) {m'fd}// in m_d1.
rewrite !(inE, in_gchop_rect) /gchop !halfg_face !oddg_face /end0g.
rewrite -{Dp}(canLR (addrK _) Dp) -addrA; case: (halfg d) => x y.
by do 2!case: oddgP; rewrite /= !lter_add2 ?ger_addl ?ler_addl.
Qed.

Section Extend1.

Variable d : gpoint.

Definition ext1_hex := m (halfg (gedge d)) && ~~ has (ehex d) m.

Hypothesis ext1d : ext1_hex.

Let m'd : (halfg d \in m) = false.
Proof.
have [_] := andP ext1d; apply: contraNF => m_d; apply/hasP.
by exists (halfg d); rewrite // in_gchop_rect /= gtouch_refl gchop_halfg.
Qed.

Let rm_ed : gedge d \in mring m.
Proof. by rewrite in_mring inE gedge2 m'd andbT; case/andP: ext1d. Qed.

Let m'f3d : ~~ has (equad (iter 3 gface d)) m.
Proof.
have [_] := andP ext1d; apply: contra => /hasP[p m_p /ehexF].
by rewrite gface4 => d_p; apply/hasP; exists p.
Qed.

Let m'f4d : ~~ has (equad (iter 4 gface d)) m.
Proof.
have [_] := andP ext1d; apply: contra => /hasP[p m_p].
by rewrite /= gface4 in_gchop_rect => /andP[d_p _]; apply/hasP; exists p.
Qed.

Let ext1_loop := traject gface (gface d) 3.
Definition ext1_mring := let: RotToSpec _ r _ := rot_to rm_ed in ext1_loop ++ r.

Lemma ext1_mring_cycle : cycle mrlink ext1_mring.
Proof.
rewrite /ext1_mring; case: (rot_to _) => i r Dr.
have:= mring_cycle m; rewrite -(rot_cycle i) {i}Dr !(cycle_path d) /=.
rewrite /mrlink !end0g_face !eqxx /= end0g_edge.
by case: r => [|d1 r]; rewrite /= end1g_edge -!end0g_face gface4.
Qed.

Lemma ext1_mring_simple : uniq (map end0g ext1_mring).
Proof.
rewrite /ext1_mring; case: (rot_to _) => i r Dr.
case: (mring_equad m'f4d, mring_simple m); rewrite -(rot_uniq i) -(mem_rot i).
move: (mring_equad m'f3d); rewrite -[LHS](mem_rot i) -map_rot {i}Dr.
rewrite !map_cons !inE !end0g_edge -!end0g_face.
move: {r}(map _ r) (gface d) => r d1 /=; rewrite !inE ![_ == end0g d1]eq_sym.
move=> /norP[/negPf-> /negPf->] /norP[/negPf-> /negPf->] /andP[-> ->] /=.
by rewrite eq_sym end0g_face (inj_eq (addrI _)) neq_ccw.
Qed.

Let m'Eloop : all (fun f => halfg (gedge f) \notin m) ext1_loop.
Proof.
apply/allP=> _ /trajectP[i lti3 ->]; set p := halfg _.
have [_] := andP ext1d; apply/contra=> m_p; apply/hasP; exists p => {m_p}//.
rewrite in_gchop_rect /= /gchop {}/p -iterSr halfg_edge halfg_iter_face.
case: (halfg d) => x y; rewrite oddg_iter_face.
by case: oddgP i lti3 => -[|[|[]]] //=; rewrite ?lter_add2 ?ler_addl ?ger_addl.
Qed.

Lemma ext1_mring_def : ext1_mring =i gborder (ext_mdisk d).
Proof.
move=> p; rewrite /ext1_mring; case: (rot_to _) => i r Dr.
have [m'ef1d m'ef2d m'ef3d _] := and4P m'Eloop; rewrite !inE !(eq_sym p).
have [<- | p'f1d] := altP eqP.
  by rewrite halfg_face eqxx m'd /= eq_sym -halfg_face neq_halfg_edge.
have [<- | p'f2d] := altP eqP.
  by rewrite !halfg_face eqxx m'd /= eq_sym -2!halfg_face neq_halfg_edge.
have [<- | p'f3d] := altP eqP.
  by rewrite !halfg_face eqxx m'd /= eq_sym -3!halfg_face neq_halfg_edge.
rewrite /= negb_or andbCA andb_orl -[rhs in _ || rhs]in_mring orbC andbC.
have [mr_p | mr'p] /= := boolP (p \in mring m).
  have [/andP[r'ed _]]: uniq (gedge d :: r) /\ p \in gedge d :: r.
    by rewrite -Dr rot_uniq mem_rot (map_uniq (mring_simple m)).
  rewrite inE => /predU1P[->|r_p]; first by rewrite gedge2 eqxx (negPf r'ed).
  move: mr_p; rewrite in_mring => /andP[/contraTneq->//] /esym/same_halfg.
  by rewrite !inE !(inv_eq gedge2) -implyNb (memPn r'ed) //= => /or3P[]/eqP->.
apply/negb_inj; have /norP[_ ->]: p \notin gedge d :: r by rewrite -Dr mem_rot.
apply/esym/nandP; left; apply: contraL rm_ed => /andP[/eqP/esym/same_halfg].
rewrite !inE in_mring negb_and => /predU1P[-> -> //|/norP[]].
by rewrite !(eq_sym p) negb_or p'f2d.
Qed.

Definition ext1_matte :=
  Matte (ext_mdisk_ne d) ext1_mring_cycle ext1_mring_simple ext1_mring_def.

End Extend1.

Section Extend2.

Variable d : gpoint.

Definition ext2_quad :=
  [&& halfg (gedge d) \in m, halfg (gedge (gface d)) \in m
    & ~~ has (equad d) m].

Hypothesis ext2d : ext2_quad.

Let m'd : (halfg d \in m) = false.
Proof.
have [_ _] := and3P ext2d; apply: contraNF => m_d; apply/hasP.
exists (halfg d); rewrite // !(inE, in_gchop_rect) gtouch_refl.
by rewrite gchop_halfg -halfg_face gchop_halfg.
Qed.

Let m'f4d : ~~ has (equad (iter 4 gface d)) m.
Proof. by have [_ _] := and3P ext2d; rewrite /= gface4. Qed.

Let mr_efd : gedge (gface d) \in mring m.
Proof.
by rewrite in_mring inE gedge2 halfg_face m'd; have [_ ->] := and3P ext2d.
Qed.

Let mr_ed : gedge d \in mring m.
Proof. by rewrite in_mring inE gedge2 m'd; have [->] := andP ext2d. Qed.

Fact ext2_P : {ir | rot ir.1 (mring m) = [:: gedge (gface d), gedge d & ir.2]}.
Proof.
have [i [|d1 r] Dr] := rot_to mr_efd.
  have /idPn[] := mring_cycle m; rewrite -(rot_cycle i) Dr /= /mrlink.
  by rewrite (inj_eq (addrI _)) neq_ccw.
exists (i, r); rewrite Dr; congr [:: _, _ & _].
move: (mring_cycle m) mr_ed (mring_simple m).
rewrite -(rot_cycle i) -(mem_rot i) -(rot_uniq i) -map_rot Dr.
case/andP=> /eqP-Dd1 _; rewrite end1g_edge end0g_face -end0g_edge in Dd1.
rewrite -(mem_rot 1) -(rot_uniq 1) -map_rot rot1_cons /= inE.
by case/predU1P=> // r_ed; rewrite -Dd1 map_f.
Qed.

Let ext2_loop := traject gface (gface (gface d)) 2.
Definition ext2_mring := let: exist (_, r) _ := ext2_P in ext2_loop ++ r.

Lemma ext2_mring_cycle : cycle mrlink ext2_mring.
Proof.
rewrite /ext2_mring; case: ext2_P (mring_cycle m) => -[i r] /= Dr.
rewrite -(rot_cycle i) {i}Dr /= !rcons_path /= end1g_edge !end0g_edge.
rewrite !end0g_face !eqxx /= -[d in gedge d]gface4.
by case: r => [|d1 r] /=; rewrite end1g_edge end0g_face.
Qed.

Lemma ext2_mring_simple : uniq (map end0g ext2_mring).
Proof.
rewrite -(rot_uniq 1) /ext2_mring; case: ext2_P => -[i r] Dr; rewrite /= in Dr.
have:= mring_simple m; rewrite -(rot_uniq i) -(rot_uniq 1).
have:= mring_equad m'f4d; rewrite -(mem_rot i) -(mem_rot 1) -!map_rot {i}Dr.
rewrite !rot1_cons !map_rcons end0g_edge -end0g_face /= inE => /norP[_ ->].
by case/andP.
Qed.

Let m'Eloop : all (fun fd => halfg (gedge fd) \notin m) ext2_loop.
Proof.
apply/allP=> _ /trajectP[i lti2 ->]; rewrite -!iterSr.
have [_ _ /hasPn/(_ _)/contraL] := and3P ext2d; apply.
rewrite halfg_edge halfg_iter_face oddg_iter_face !(inE, in_gchop_rect).
rewrite /gchop halfg_face oddg_face; case: (halfg d) => x y.
by case: oddgP i lti2 => -[|[]] //= _; rewrite !lter_add2 ?ler_addl ?ger_addl.
Qed.

Lemma ext2_mring_def : ext2_mring =i gborder (ext_mdisk d).
Proof.
rewrite /ext2_mring; case: ext2_P => -[i r] /= Dr p; rewrite !inE.
have [m'ef2d m'ef3d _] := and3P m'Eloop.
have [-> | f2d'p] /= := altP eqP.
  by rewrite andbC eq_sym -2!halfg_face eqxx neq_halfg_edge andbT.
have [-> | f3d'p] /= := altP eqP.
  by rewrite andbC eq_sym -3!halfg_face eqxx neq_halfg_edge andbT.
rewrite negb_or andbCA andb_orl -[rhs in _ || rhs]in_mring orbC andbC.
have [mr_p | mr'p] /= := boolP (p \in mring m).
  apply/esym; apply/eqP/idP=> [|[/esym/same_halfg/(map_f gedge)Dp r_p]].
    have:= mr_p; rewrite -(mem_rot i) Dr !inE orbA.
    by case/orP; [case/pred2P=> ->; left; rewrite gedge2 ?halfg_face | right].
  have:= map_uniq (mring_simple m); rewrite -(rot_uniq i) Dr.
  rewrite (cat_uniq [:: _; _]) andbCA andbC => /andP[_] /hasPn/(_ p r_p).
  rewrite !inE orbC => p'efd; rewrite gedge2 !inE orbA (negPf p'efd) /= in Dp.
  by have:= mr_p; rewrite in_mring => /nandP[]; left; case/pred2P: Dp => ->.
have:= mr'p; rewrite -(mem_rot i) Dr !inE orbA => /norP[_ /negPf->].
apply/esym/nandP; left; apply: contraL mr_efd => /andP[/eqP/esym/same_halfg].
rewrite !inE (negPf f2d'p) (negPf f3d'p) !orbF in_mring negb_and gedge2.
by rewrite halfg_face m'd orbF => /pred2P[->|<-//]; have [->] := andP ext2d.
Qed.

Definition ext2_matte :=
  Matte (ext_mdisk_ne d) ext2_mring_cycle ext2_mring_simple ext2_mring_def.

End Extend2.

End ExtendMatte.

Section MatteExtension.

Variable m : matte.

Inductive matte_extension : matte -> Type :=
  | Mext_nil : matte_extension m
  | Mext_add d (xm0 xm : matte) of
      matte_extension xm0 & gedge d \in mring xm0 & xm =i ext_mdisk xm0 d :
    matte_extension xm.

Arguments Mext_add : clear implicits.

Lemma in_extension xm : matte_extension xm -> {subset m <= xm}.
Proof.
elim: xm / => [|d xm0 xm _ IHxm _ Dxm] p m_p //.
by rewrite Dxm mem_behead /= ?IHxm.
Qed.

Variant extends_in (r : grect) (p : gpoint) :=
  ExtendsIn xm of matte_extension xm & {subset xm <= predU r m} & p \in xm.

Lemma extends_in_sub (r1 r2 : grect) :
  subpred r1 r2 -> forall p, extends_in r1 p -> extends_in r2 p.
Proof.
move=> sr12 p [xm xmP sxmr xm_p]; exists xm => {p xm_p}// p /sxmr.
by rewrite !inE -(orb_idl (sr12 p)) orbAC => ->.
Qed.

Lemma coarse_extends_in (r : grect) :
  coarse_in r m -> has r m -> forall p, inset r p -> extends_in r p.
Proof.
move=> r0Emh m_r p r0p; set r0 := r in r0Emh r0p; pose m0 := predI r0 m.
have [r_m0 r0_r]: subpred m0 r /\ subpred r r0 by split=> [q /andP[]|].
have r_p: r p := insetW r0p; move: {2}_.+1 (ltnSn (garea r)) => n le_r_n.
elim: n => // n IHn in r (r0) p m0 le_r_n m_r r_p r_m0 r0_r r0p r0Emh *.
have [m_p | m'p] := boolP (p \in m).
  by exists m => // [|q m_q]; [left | apply/orP; right].
have ext_hex d (ed := gedge d) :
    halfg d = p -> ~~ has (ehex d) m ->
  extends_in (gchop_rect r ed) (halfg ed) -> extends_in r p.
- move=> Dp d'm [xm xmP rm_xm xm_ed].
  have ext1d: ext1_hex xm d.
    rewrite /ext1_hex !inE xm_ed; apply/hasPn=> q /rm_xm/orP[|/(hasPn d'm)//].
    by rewrite !in_gchop_rect /= gchop_edge negb_and orbC => /andP[_ ->].
  do [exists (ext1_matte ext1d); rewrite ?inE ?Dp ?eqxx //] => [|q].
    right with d xm; rewrite // in_mring inE gedge2 Dp xm_ed.
    apply/(contra (rm_xm p)); rewrite inE in_gchop_rect /= gchop_edge.
    by rewrite -Dp gchop_halfg andbF Dp.
  rewrite !inE => /predU1P[->|/rm_xm]; first by rewrite Dp r_p.
  by rewrite inE in_gchop_rect orb_andl => /andP[].
have{IHn} IHp d: halfg d = p -> has (predD r0 (gchop1 d)) m -> extends_in r p.
  move=> Dp m_r0d; pose r01 := gchop1_rect r0 d.
  have r01p: inset r01 p.
    apply/insetP=> q p1q; rewrite in_gchop1_rect /= (insetP r0p) //=.
    by have:= p1q; rewrite -Dp gtouch_chop1 => /andP[].
  have [m_r01 | r01'm] := boolP (has r01 m).
    pose r1 := gchop1_rect r d; have r_r1: subpred r1 r := @gchop_rect_sub r _.
    apply/(extends_in_sub r_r1)/(IHn r1 r01)=> //.
    - have [q m_q /andP[d'q r0q]] := hasP m_r0d.
      apply: leq_trans (n) _ le_r_n; apply: (@ltn_garea_subrect q) => //=.
      by rewrite in_gchop1_rect /= r_m0 ?d'q //= r0q.
    - have [q m_q] := hasP m_r01; rewrite in_gchop1_rect => /andP[r0q d_q].
      by apply/hasP; exists q; rewrite // in_gchop1_rect /= r_m0 //= r0q.
    - by rewrite in_gchop1_rect /= r_p -Dp gchop_chop1 ?gchop_halfg.
    - by move=> q; rewrite !(inE, in_gchop1_rect) andbAC => /andP[/r_m0->].
    - by move=> q; rewrite !in_gchop1_rect /= => /andP[/r0_r->].
    by move=> q1 q2 /gchop_rect_sub; apply: r0Emh.
  apply: ext_hex (Dp) (contra _ r01'm) _.
    by apply/sub_has=> q; rewrite in_gchop_rect Dp => /andP[/(insetP r01p)].
  set r1 := gchop_rect r _; have r_r1: subpred r1 r := @gchop_rect_sub r _.
  have m_r1: has r1 m.
    have [q m_q /andP[d'q r0q]] := hasP m_r0d.
    apply/hasP; exists q; rewrite ?in_gchop_rect //= r_m0 /= ?r0q //.
    by rewrite gchop_edge (contra _ d'q) => // /gchop_chop1.
  apply (IHn _ r0) => //; last 2 [by move=> q /r_r1/r0_r].
  - apply: leq_trans (n) _ le_r_n; apply: (@ltn_garea_subrect p) => //=.
    by rewrite in_gchop_rect /= r_p gchop_edge -Dp gchop_halfg.
  - by have [q _] := hasP m_r1; apply: gchop_rect_edge; rewrite gedge2 Dp.
  - move=> q m0q; rewrite in_gchop_rect /= r_m0 // gchop_edge.
    case/andP: m0q => r0q /(hasPn r01'm); apply: contra => d_q.
    by rewrite in_gchop1_rect /= r0q gchop_chop1.
  set ed := gedge d; case Ded: (halfg ed) => [x y].
  case Dr0: r0 => [x0 x1 y0 y1] /=; rewrite -!ler_subr_addr !ltr_subr_addr.
  have r0efd i: r0 (halfg (gedge (iter i gface (gedge ed)))).
    by rewrite (insetP r0p) // -Dp -(halfg_iter_face i) gedge2 gtouch_edge.
  have /= (d2 := gedge (gface (gface ed))): gchop_rect r0 d2 (halfg d2).
    have [q m_q /andP[d'q r0q]] := hasP m_r0d; apply: gchop_rect_edge (q) _.
      by rewrite gedge2 (insetP r0p) // !halfg_face -Dp gtouch_edge.
    by rewrite in_gchop_rect /= r0q gchop_edge.
  rewrite in_gchop_rect /= gchop_halfg andbT; have [] := (r0efd 1, r0efd 3)%N.
  rewrite !(Ded, halfg_edge, halfg_face, oddg_edge, oddg_face) -!addrA Dr0.
  by case: oddgP; do ![case/andP | move-> | clear 1].
(* nd q is the dart of q whose edge separates q from gnode q *)
pose nd (q : gpoint) : gpoint := q *+ 2 + iter 3 ccw (oddg q).
have h_nd q: halfg (nd q) = q by rewrite halfg_eq //= !ccw_odd.
have o_nd q: oddg (nd q) = ccw (ccw (ccw (oddg q))).
  by rewrite oddg_eq //= !ccw_odd.
have hEnd q: halfg (gedge (nd q)) = gnode q.
  by rewrite halfg_edge h_nd o_nd ccw4.
have ndN q: nd (gnode q) = gedge (gnode (gedge (nd q))).
  rewrite -[gedge (nd q)]halfgK hEnd -[gnode q in RHS]h_nd.
  by rewrite oddg_edge o_nd -oddg_node -o_nd -gface_def gfaceK.
have ndFE q: nd (gface (gedge q)) = gedge (gface (nd q)).
  by rewrite -[q in RHS]gedgeK ndN gnodeK gedge2.
have m_nd4 q: r0 q -> has (equad (nd q)) m -> q \in m.
  move=> r0q /hasP[q1 m_q1 q4q1]; rewrite -[_ \in m](r0Emh _ q1) {m_q1}//.
  apply/esym/eqP; rewrite -[_ == _]/(_ && _) !eq_le -andbA; apply/and4P.
  move: q4q1; rewrite !(inE, in_gchop_rect) /gchop halfg_face -[halfg _]halfgK.
  rewrite h_nd oddg_face o_nd ccw4; case: (halfg q) q1 => x y [x1 y1] /=.
  rewrite -!(ltz_addr1 (_ %/ _)%Z) !ltz_divLR ?lez_divRL // !mulrDl !mulz2.
  by case: oddgP; rewrite /= ?addr0 ?addrK !(addrA _ 1 1) !ltz_addr1;
     do ![case/andP | move-> | clear 1].
have gchop1F3E d: gchop1 (iter 3 gface (gedge d)) = gchop1 (gface d).
  by rewrite -gchop1_shift gface4 gedge2.
have ehex_shift_quad q q' (efq := gedge (gface q)):
  ehex q q' || ehex (gface efq) q' ==> equad q q' || equad efq q'.
- have chop1idl q1 q2 b: gchop1 q1 q2 && b && gchop q1 q2 = gchop q1 q2 && b.
    by rewrite andbAC (andb_idl (@gchop_chop1 _ _)).
  rewrite !(inE, in_gchop_rect) !gtouch_chop1 /= !andbT gface4 !chop1idl.
  do 2!rewrite [in _ && _ && _]andbCA chop1idl; rewrite gchop_shift gchop1F3E.
  case: (gchop q _); rewrite //= orbC andbC andbCA; case: (gchop1 _ _) => //=.
  rewrite andbT gchop_edge -[gface q as fq in gface (gface fq)]gedge2.
  by case: (gchop _ _); rewrite ?orbF; case: orP => //= -[]/andP[/gchop_chop1].
have r0_np: r0 (gnode p).
  by rewrite (insetP r0p) // -hEnd -[p in gtouch p]h_nd gtouch_edge.
have r0_fep: r0 (gface (gedge p)).
  rewrite -[gface _]h_nd -[nd _]gedge2 (insetP r0p) //.
  by rewrite -[p in gtouch p]gedgeK -hEnd gtouch_edge.
have p4'm: ~~ has (equad (nd p)) m by apply/(contra _ m'p)/m_nd4/r0_r.
have [m_p6 | p6'm] := boolP (has (ehex (nd p)) m).
  have{m_p6} m_efp: halfg (gedge (gface (nd p))) \in m.
    have [q m_q p6_q] := hasP m_p6; apply/m_nd4/hasP; rewrite -ndFE h_nd //.
    have:= ehex_shift_quad (nd p) q; rewrite p6_q /= ndFE.
    by rewrite (negPf (hasPn p4'm q m_q)); exists q.
  have [m_fp6 | /ext_hex] := boolP (has (ehex (gface (nd p))) m); last first.
    rewrite halfg_face; apply=> //.
    by exists m => // [|q m_q]; [left | apply/orP; right].
  have m_ep: halfg (gedge (nd p)) \in m.
    have [q m_q p6_q] := hasP m_fp6; apply/m_nd4/hasP; rewrite hEnd //.
    have:= ehex_shift_quad (nd (gnode p)) q; rewrite -ndFE gnodeK /= p6_q orbT.
    by rewrite (negPf (hasPn p4'm q m_q)) orbF; exists q.
  have ext2p: ext2_quad m (nd p) by apply/and3P.
  exists (ext2_matte ext2p); last by rewrite inE h_nd eqxx.
    right with (nd p) m => //; first by left.
    by rewrite in_mring inE gedge2 h_nd m_ep.
  by move=> q /predU1P[->|m_q]; [rewrite h_nd inE r_p | apply/orP; right].
have [m_p | {}m'p] := boolP (has (gtouch p) m); last first.
  suffices: has [pred q | has (predD r0 (gchop1 q)) m] (traject gface (nd p) 4).
    case/hasP/sig2W=> _ /trajectP/sig2_eqW[i _ ->].
    by apply: IHp; rewrite halfg_iter_face.
  have [q m_q r_q] := hasP m_r; apply: contraR m'p; rewrite -all_predC => m'p.
  apply/hasP; exists q => //; rewrite -[p]h_nd gtouch_chop1.
  by apply: sub_all m'p => ? /hasPn/(_ q m_q); rewrite negb_and negbK orbC r0_r.
apply: ext_hex (h_nd p) (p6'm) _.
have [m_nd | m'nd] := boolP (gnode p \in m).
  by exists m => [|q m_q|]; [left | rewrite !inE m_q orbT | rewrite hEnd].
have nd4'm: ~~ has (equad (nd (gnode p))) m by apply: contra m'nd => /m_nd4->.
have r0_n2p: r0 (gnode (gnode p)).
  rewrite -[gnode _]addrA oddg_node (insetP r0p) //.
  by case: oddgP; case: (p) => x y; rewrite /= !lter_add2.
have m_n2p: gnode (gnode p) \in m.
  have [q m_q p9q] := hasP m_p; apply/m_nd4/hasP=> //; exists q => //.
  have ep_q: gchop (gedge (nd p)) q.
    rewrite gchop_edge; apply: contra p6'm => p_q.
    by apply/hasP; exists q; rewrite // in_gchop_rect /= h_nd p9q.
  have /implyP := ehex_shift_quad (nd (gnode (gnode p))) q.
  rewrite ndN gnodeK gedge2 (negPf (hasPn nd4'm q m_q)) orbF => -> //.
  apply/orP; right; rewrite in_gchop_rect /= ndN gnodeK ep_q gtouch_chop1 /=.
  rewrite gchop1F3E gchop_chop1 //= -gchop1F3E gedge2 !andbT andbC.
  by rewrite -[p]h_nd gtouch_chop1 in p9q; case/and5P: p9q => /gchop_chop1-> ->.
have r_np: r (gnode p).
  have: r (gnode (gnode p)) by rewrite r_m0 //= r0_n2p.
  rewrite /gnode oddg_node -addrA; case: (p) (r) r_p => x y [x0 x1 y0 y1].
  by case: oddgP; rewrite /= !addr0; do ![case/andP | move-> | clear 1].
have ext1nd: ext1_hex m (nd (gnode p)).
  rewrite /ext1_hex !inE hEnd m_n2p; apply/hasP => -[q m_q nd4q].
  have := ehex_shift_quad (nd (gnode p)) q; rewrite -ndFE gnodeK nd4q /=.
  by case/norP; rewrite (hasPn nd4'm) ?(hasPn p4'm).
exists (ext1_matte ext1nd) => [|q|]; last by rewrite inE h_nd hEnd eqxx.
  right with (nd (gnode p)) m => //; first by left.
  by rewrite in_mring inE hEnd m_n2p gedge2 h_nd m'nd.
rewrite !inE => /predU1P[] ->; last by rewrite orbT.
by rewrite h_nd in_gchop_rect /= r_np -hEnd gchop_halfg.
Qed.

(* We will use refined_extends_in to show directly that the union of set of   *)
(* extensions of a mattte included in a region is closed (relatively to the   *)
(* region). To show that this union is open we will need the MatteOrder       *)
(* lemmas below. We use the refined_extend_meet lemma to extend the mattes of *)
(* adjacent regions so that their contours have a common edge.                *)

Lemma extend_madj (m1 : matte) (r : grect) :
    coarse_in r m -> has r m -> has (inset r) m1 -> ~~ has m m1 ->
  let m2 := [predD predU r m & m1] in
  {xm : matte | {subset m <= xm} /\ {subset xm <= m2} & madj m1 xm}.
Proof.
rewrite (has_sym m) => rEmh r_m /hasP/sig2W[p m1_p r_p] /negP-m1'm m2.
have{rEmh r_m r_p} [xm xmP sxmr xm_p] := coarse_extends_in rEmh r_m r_p.
have{p m1_p xm_p} m1_xm: has m1 xm by apply/hasP; exists p.
elim: {xm}xmP => {m1'm}// p xm0 xm xm0P IHxm xm0ep Dxm in sxmr m1_xm.
have sxm0r: {subset xm0 <= predU r m}.
  by move=> q xm0q; rewrite sxmr // !inE Dxm inE xm0q orbT.
have [m1_xm0 | m1'xm0] := boolP (has m1 xm0); first exact: IHxm.
exists xm0; first do [split; first exact: in_extension].
  by move=> q xm1q; rewrite inE (hasPn m1'xm0) //= sxm0r.
apply/hasP; exists (gedge p); rewrite //= gedge2 in_mring inE.
rewrite andbC (hasPn m1'xm0); last by move: xm0ep; rewrite in_mring => /andP[].
by have [q] := hasP m1_xm; rewrite Dxm => /predU1P[-> | /(hasPn m1'xm0)/negP].
Qed.

End MatteExtension.

Section MatteOrder.

Implicit Types m xm : matte.

Definition mcorner m q : nat :=
  let m'q i := q - iter i ccw 0 \notin m in (m'q 2 + (m'q 1 + m'q 3).*2)%N.

Lemma mcorner0 m q : q \in m -> mcorner m q = 0%N -> subpred (ltouch q) m.
Proof.
have negb_Ngt0 b: ~~ (~~ b > 0)%N = b by case: b.
move=> mq /eqP; rewrite eqn0Ngt !(addn_gt0, double_gt0) !negb_or !{}negb_Ngt0.
case: q => x y in mq *; rewrite /+%R /= !subr0 => /and3P[mq11 mq01 mq10] p.
by rewrite -mem_enum_grect /= !zspan_dec_inc; apply/allP/and5P.
Qed.

Lemma refine_mcorner m r q (p := halfg q):
   p \in m -> inset r p -> (0 < mcorner m p)%N ->
   let ext_m_r xm := {subset [preim halfg of m] <= xm}
                  /\ {subset xm <= [preim halfg of predU r m]} in
  {xm | ext_m_r xm & mcorner xm q < mcorner m p}%N.
Proof.
move=> m_p r_p mp_gt0 ext_m_r; pose m_pc c := p + halfg (- c + oddg q) \in m.
pose xmE xm c0 c := (q - c \notin xm) = ~~ [|| c == c0, m_pc c | q - c \in xm].
have ext_along d: {xm : matte | ext_m_r xm & forall c, xmE xm (oddg d) c}.
  pose xr := refine_rect r; pose xm := refine_matte m.
  have xrExmh: coarse_in xr xm by apply: refine_matte_coarse.
  have xr_xm: has xr xm.
    by apply/hasP; exists q; rewrite ?in_refine_matte ?in_refine_rect 1?insetW.
  have xr_qd: inset xr (q - oddg d).
    rewrite -in_refine_rect refine_inset in r_p; apply/(insetP r_p).
    by case: oddgP (q) => -[x y] /=; rewrite !lter_add2.
  have[xm1 xm1P xrm_xm1 xm1c1] := coarse_extends_in xrExmh xr_xm xr_qd.
  exists xm1 => [|c].
    split=> p1 xm1p1; first by rewrite (in_extension xm1P) ?in_refine_matte.
    by rewrite !inE -in_refine_rect -in_refine_matte [_ || _]xrm_xm1.
  rewrite /xmE orbA orb_idl // => /predU1P[->|] //.
  by rewrite /m_pc -halfg_add -in_refine_matte => /in_extension->.
have [oq0 | o_q] := eqVneq (oddg q) 0; last first.
  have [xm mr_xm Dxm] := ext_along (ccw (ccw (oddg q))); exists xm => {mr_xm}//.
  rewrite /mcorner !{}Dxm /m_pc; rewrite -[p]addr0 in m_p.
  by case: oddgP o_q; rewrite ?m_p //=; have [[->]|] := norP; rewrite ?addnS.
have{mp_gt0} [d o_d /negPf-m'pd]: {d | oddg d != 0 & p - oddg d \notin m}.
  have:= mp_gt0; rewrite /mcorner.
  by do ![set d := (d in p - d); case m'd: (~~ _); [by exists d | clear d m'd]].
have [xm mr_xm Dxm] := ext_along d; exists xm => {mr_xm}//.
rewrite /mcorner !inE !{}Dxm /m_pc oq0.
by case: oddgP o_d m'pd => //= _ ->; do !have [[->]|] := norP; rewrite ?addnS.
Qed.

End MatteOrder.

