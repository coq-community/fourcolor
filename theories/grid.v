(* (c) Copyright 2006-2015 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp Require Import div choice order ssralg ssrnum ssrint intdiv.
From fourcolor Require Import hypermap.

(******************************************************************************)
(*    Geometry over an integer grid, that is, raster graphics.                *)
(* We define integer point arithmetic, which we then use to define            *)
(* coordinates for three kinds of basic geometric objects: grid points, grid  *)
(* pixels (unit squares), and grid darts (pixel corners, selecting one of the *)
(* four vertices of a given pixel). A pixel is denoted by its lower left      *)
(* vertex, while a dart d of a pixel p is denoted by the subpixel of p in a   *)
(* refined (bisected) grid, that contains the vertex q of d.                  *)
(*   We also use a dart d to denote the directed pixel edge starting at the   *)
(* vertex of d and wrapping counterclockwise around the pixel of d.           *)
(*   We define an infinite hypermap on grid darts, whose faces are pixels and *)
(* nodes are grid points (we don't represent undirected edges, however).      *)
(*    Interpreting darts as subpixels works rather nicely for binary grid     *)
(* subdivision, which is used heavily in the construction of discrete         *)
(* approximations of topological regions of the real plane.                   *)
(*       gpoint == type for grid points/pixels/darts; gpoint is a zmodType.   *)
(*   Gpoint x y == the grid point/pixel/dart with coordinates x y.            *)
(*      halfg d == the pixel of which the grid dart d is a corner of; the     *)
(*                 coordinates of halfg d are half those of its subpixel d.   *)
(*       oddg d == the vertex of the unit square congruent to the vertex of d *)
(*                 in its pixel; the coordinates of oddg d are 0 or 1,        *)
(*                 accoring to the parity of the coordinates of d (i.e.,      *)
(*                 oddg d has the coordinates of d mod 2).                    *)
(*    is_oddg q <-> q : gpoint is one of the unit square vertices.            *)
(*      oddgP d == proof of is_oddg (oddg d); case analysis on oddgP          *)
(*                 determines which vertex oddg d is, and replaces oddg d.    *)
(* oddg_cases c b00 b01 b10 b11 == bxy, when c is Gpoint x y, x, y in {0, 1}. *)
(*          ccw == the 90 degree counterclockwise rotation of the grid point  *)
(*                 plane that permutes the unit square corners.               *)
(*       arcg q == the chord from q to ccw q (:= ccw q - q).                  *)
(*      end0g d == the start vertex of dart d, which d shares with its pixel. *)
(*      end1g d == the end vertex of the directed edge denoted by dart d.     *)
(*      gface d == the next dart (counterclockwise) with the same pixel as d. *)
(*      gnode d == the next dart sitting at the same point as d.              *)
(*      gedge d == the dart denoting the edge opposite to that denoted by d.  *)
(*      gregion == discrete pixel set (:= pred gpoint).                       *)
(*        grect == type for rectangular pixel sets (coerces to gregion).      *)
(*  Grect x0 x1 y0 y1 == grect for the set of pixels with coordinates x, y    *)
(*                 such that x0 <= x < x1 and y0 <= y < y1.                   *)
(*  extend_grect r p == the smallest grect that contains both r and p.        *)
(*  zwidth z0 z1 == number of integers z in the interval [z0, z1].            *)
(*      gwidth r == pixel width of r : grect.                                 *)
(*     gheight r == pixel height of r : grect.                                *)
(*       garea r == number of pixels in r : grect.                            *)
(*   gr_proper r <=> r is a proper (non-empty) grid rectangle.                *)
(*  enum_grect r == sequence enumerating all the pixels in r : grect.         *)
(*       inset r == the grect obtained by removing a one-pixel border from r. *)
(*      gtouch p == the 3x3 grect of pixels that touch pixel p.               *)
(*      ltouch q == the 2x2 grect of pixels that touch grid point q.          *)
(*       gchop d == the half-plane region delimited by the line through the   *)
(*                  edge denoted by dart d, which contains the pixel of d.    *)
(*      gchop1 d == the half-plane region delimited by the line parallel to   *)
(*                  the edge denoted by dart d, one pixel off, and that       *)
(*                  contains all pixels adjacent to the pixel of d.           *)
(*  gchop_rect r d == the grect corresponding to the intersection of grect r  *)
(*                  with the half-plane gchop d.                              *)
(*  gchop1_rect r d == the grect corresponding to the intersection of grect r *)
(*                  with the half-plane gchop1 d.                             *)
(*  refine_rect r == the grect that contains exactly the subpixels of r, in   *)
(*                  the binary subdivision of the grid.                       *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(* Complement to intdiv. *)
Lemma modz2 x : (x %% 2)%Z = odd `|x|.
Proof. by rewrite -modn2 -modz_nat abszEsign -modzMml -modzXm expr1n mul1r. Qed.

Inductive gpoint := Gpoint of int & int.

Definition gregion := pred gpoint.

Identity Coercion in_gregion : gregion >-> pred.

Module GridPoint.

Definition code p : int * int := let: Gpoint x y := p in (x, y).
Definition decode xy := Gpoint xy.1 xy.2.
Lemma codeK : cancel code decode. Proof. by case. Qed.

#[export]
HB.instance Definition _ := Countable.copy gpoint (can_type codeK).

Definition zero := Gpoint 0 0.

Definition opp p := let: Gpoint x y := p in Gpoint (- x) (- y).

Definition add p1 p2 :=
  let: Gpoint x1 y1 := p1 in let: Gpoint x2 y2 := p2 in
  Gpoint (x1 + x2) (y1 + y2).

Fact addA : associative add.
Proof. by case=> x1 y1 [x2 y2] [x3 y3] /=; rewrite !addrA. Qed.

Fact addC : commutative add.
Proof. by case=> x1 y1 [x2 y2]; congr Gpoint; apply: addrC. Qed.

Fact add0 : left_id zero add.
Proof. by case=> x y /=; rewrite !add0r. Qed.

Fact addN : left_inverse zero opp add.
Proof. by case=> x y /=; rewrite !addNr. Qed.

#[export]
HB.instance Definition _ := GRing.isZmodule.Build gpoint addA addC add0 addN.

Module Exports. HB.reexport. End Exports.
End GridPoint.
Export GridPoint.Exports.

Bind Scope ring_scope with gpoint.

Section GridGeometry.

(* By convention, p and q denote pixel or grid point coordinates, c denotes   *)
(* corner (unit square vertex) coordinates, and d dart coordinates (linear    *)
(* combination of pixel and corner).                                          *)
Implicit Type p q d c : gpoint.

Definition halfg d := let: Gpoint x y := d in Gpoint (x %/ 2)%Z (y %/ 2)%Z.

Definition oddg d := let: Gpoint x y := d in Gpoint (x %% 2)%Z (y %% 2)%Z.

Variant is_oddg : gpoint -> Type :=
  | Gpoint00 : is_oddg 0
  | Gpoint01 : is_oddg (Gpoint 0 1)
  | Gpoint11 : is_oddg (Gpoint 1 1)
  | Gpoint10 : is_oddg (Gpoint 1 0).

Definition oddg_cases T c b00 b01 b10 b11 : T :=
  let: Gpoint x y := c in
  if x == 0 then if_expr (y == 0) b00 b01 else if_expr (y == 0) b10 b11.

Lemma halfg_add2 p d : halfg (p *+ 2 + d) = p + halfg d.
Proof. by case: p d => xp yp [xd yd] /=; rewrite -!mulz2 !divzMDl. Qed.

Lemma oddg_add2 p d : oddg (p *+ 2 + d) = oddg d.
Proof. by case: p d => xp yp [xd yd] /=; rewrite -!mulz2 !modzMDl. Qed.

Lemma halfg_double p : halfg (p *+ 2) = p.
Proof. by rewrite -[p *+ 2]addr0 halfg_add2 addr0. Qed.

Lemma oddg_double p : oddg (p *+ 2) = 0.
Proof. by rewrite -[p *+ 2]addr0 oddg_add2. Qed.

Lemma halfgK d : halfg d *+ 2 + oddg d = d.
Proof. by case: d => x y; congr (Gpoint _ _); rewrite -mulz2 -divz_eq. Qed.

Lemma oddg_add d1 d2 : oddg (d1 + d2) = oddg (d2 + oddg d1).
Proof. by rewrite -[d1 in LHS]halfgK addrAC -addrA oddg_add2. Qed.

Lemma halfg_add d1 d2 : halfg (d1 + d2) = halfg d1 + halfg (d2 + oddg d1).
Proof. by rewrite -[d1 in LHS]halfgK addrAC -addrA halfg_add2. Qed.

Lemma oddgP d : is_oddg (oddg d).
Proof. by case: d => x y /=; rewrite !modz2; do 2!case: odd; constructor. Qed.
Hint Resolve oddgP : core.

Lemma oddg_id c : is_oddg c -> oddg c = c. Proof. by case. Qed.

Lemma halfg_odd c : is_oddg c -> halfg c = 0. Proof. by case. Qed.

Lemma oddg_eq p c : is_oddg c -> oddg (p *+ 2 + c) = c.
Proof. by rewrite oddg_add2 => /oddg_id. Qed.

Lemma halfg_eq p c : is_oddg c -> halfg (p *+ 2 + c) = p.
Proof. by rewrite halfg_add2 -[RHS]addr0 => /halfg_odd->. Qed.

(* Turning 90^o counterclockwise around the center of the unit square. *)

Definition ccw p := let: Gpoint x y := p in Gpoint (1 - y) x.

Lemma ccw_odd d : ccw (oddg d) = oddg (ccw d).
Proof. by case: d => x y /=; rewrite -modzDmr -modzNm modz2; case: (odd _). Qed.

Lemma neq_ccw d : (ccw d == d) = false.
Proof. by apply/eqP=> /(congr1 oddg); rewrite -ccw_odd; case: oddgP. Qed.

Lemma ccw4 p : ccw (ccw (ccw (ccw p))) = p.
Proof. by case: p => x y; congr (Gpoint _ _); apply: subKr. Qed.

Lemma ccw2 p : ccw (ccw p) = Gpoint 1 1 - p. Proof. by case: p. Qed.

Definition arcg c := ccw c - c.

Lemma arcg_ccw2 c : arcg (ccw (ccw c)) = - arcg c.
Proof. by rewrite /arcg !ccw2 !opprB addrCA addrAC add0r. Qed.

(* The dart interpretation of points: the half point gives the coordinates of *)
(* the origin of the square, the parity bits specify the side. The origin and *)
(* target of each dart (end0g and end1g, respectively) are computed using the *)
(* functions below.                                                           *)

Definition end0g d := halfg d + oddg d.
Definition end1g d := halfg d + ccw (oddg d).

Lemma end0g_eq d : end0g d *+ 2 - oddg d = d.
Proof. by rewrite mulrnDl addrA halfgK addrK. Qed.

Lemma halfg_add_odd d : halfg (d + oddg d) = end0g d.
Proof. by rewrite halfg_add halfg_double. Qed.

Lemma end0g_sub1 d : end0g d - Gpoint 1 1 = halfg (d - Gpoint 1 1).
Proof. by rewrite halfg_add -addrA; case: oddgP. Qed.

(* The infinite hypermap of a grid. *)

Definition gedge d := d + (arcg (oddg d) - arcg (ccw (oddg d))).

Definition gnode d :=  d - arcg (oddg d).

Definition gface d := d + arcg (oddg d).

Lemma oddg_face d : oddg (gface d) = ccw (oddg d).
Proof. by rewrite oddg_add subrK ccw_odd oddg_id. Qed.

Lemma halfg_face d : halfg (gface d) = halfg d.
Proof. by rewrite halfg_add subrK ccw_odd (halfg_odd (oddgP _)) addr0. Qed.

Lemma halfg_iter_face i d : halfg (iter i gface d) = halfg d.
Proof. by elim: i => //= i IHi; rewrite halfg_face. Qed.

Lemma oddg_iter_face i d : oddg (iter i gface d) = iter i ccw (oddg d).
Proof. by elim: i => //= i IHi; rewrite oddg_face IHi. Qed.

Lemma gface_def d : gface d = halfg d *+ 2 + ccw (oddg d).
Proof. by rewrite -halfg_face -oddg_face halfgK. Qed.

Lemma gface4 d : gface (gface (gface (gface d))) = d.
Proof. by rewrite gface_def !halfg_face !oddg_face ccw4 halfgK. Qed.

Lemma end0g_face d : end0g (gface d) = end1g d.
Proof. by rewrite /end0g oddg_face halfg_face. Qed.

Lemma same_halfg d1 d2 : halfg d1 = halfg d2 -> d2 \in traject gface d1 4.
Proof.
have Ed d: halfg d = halfg d2 -> (d2 == d) = (oddg d2 == oddg d).
  by move=> Ed; rewrite -[RHS](inj_eq (addrI (halfg d *+ 2))) halfgK Ed halfgK.
by move=> Ed12; rewrite !inE !Ed ?halfg_face // !oddg_face; do 2!case: oddgP.
Qed.

Lemma gnode_sub1 d : gnode d - Gpoint 1 1 = gface (d - Gpoint 1 1).
Proof. by rewrite /gface -!addrA oddg_add; case: oddgP. Qed.

Lemma oddg_node d : oddg (gnode d) = ccw (oddg d).
Proof. by rewrite -(oddg_add2 (arcg (oddg d))) addrCA addrK oddg_face. Qed.

Lemma halfg_node d : halfg (gnode d) = halfg d - arcg (oddg d).
Proof. by rewrite -(halfg_face d) addrC -halfg_add2 addrCA subrK. Qed.

Lemma neq_halfg_node p : (halfg p == halfg (gnode p)) = false.
Proof. by rewrite halfg_node -subr_eq0 opprD addNKr; case: oddgP. Qed.

Lemma end0g_node d : end0g (gnode d) = end0g d.
Proof. by rewrite /end0g halfg_node oddg_node opprB addrA subrK. Qed.

Lemma gnode4 d : gnode (gnode (gnode (gnode d))) = d.
Proof. by apply/(addIr (- Gpoint 1 1)); rewrite !gnode_sub1 gface4. Qed.

Lemma same_end0g d1 d2 : end0g d1 = end0g d2 -> d2 \in traject gnode d1 4.
Proof.
move/(congr1 (+%R^~ (- Gpoint 1 1))); rewrite !end0g_sub1 => /same_halfg.
by rewrite !inE -!gnode_sub1 !(inj_eq (addIr _)).
Qed.

Lemma gnode_face d : gnode (gface d) = gedge d.
Proof. by rewrite [RHS]addrA -oddg_face. Qed.

Lemma oddg_edge p : oddg (gedge p) = ccw (ccw (oddg p)).
Proof. by rewrite -gnode_face oddg_node oddg_face. Qed.

Lemma halfg_edge p : halfg (gedge p) = halfg p - arcg (ccw (oddg p)).
Proof. by rewrite -gnode_face halfg_node halfg_face oddg_face. Qed.

Lemma neq_halfg_edge p : (halfg p == halfg (gedge p)) = false.
Proof. by rewrite halfg_edge -subr_eq0 opprD addNKr; case: oddgP. Qed.

Lemma end0g_edge p : end0g (gedge p) = end1g p.
Proof. by rewrite -gnode_face end0g_node end0g_face. Qed.

Lemma gedge2 p : gedge (gedge p) = p.
Proof. by rewrite {1}/gedge oddg_edge !arcg_ccw2 -opprD addrK. Qed.

Lemma end1g_edge p : end1g (gedge p) = end0g p.
Proof. by rewrite -end0g_edge gedge2. Qed.

Lemma gedgeK : cancel3 gedge gnode gface.
Proof. by move=> d; rewrite /= gnode_face gedge2. Qed.

Lemma gfaceK : cancel3 gface gedge gnode.
Proof. by move=> d; rewrite /= gnode_face gedge2. Qed.

Lemma gnodeK : cancel3 gnode gface gedge.
Proof. by move=> p /=; rewrite -[p]gface4 gfaceK. Qed.

(* Rectangles on the grid. *)

Inductive grect := Grect (xmin xmax ymin ymax : int).

Coercion in_grect r : gregion :=
  fun p => let: Grect xmin xmax ymin ymax := r in let: Gpoint x y := p in
  (xmin <= x < xmax) && (ymin <= y < ymax).

(* Extending a recangle to cover a specific pixel.                          *)

Definition extend_grect p r :=
  let: (Grect x0 x1 y0 y1, Gpoint x y) := (r, p) in
  Grect (Num.min x0 x) (Num.max x1 (x + 1)) (Num.min y0 y) (Num.max y1 (y + 1)).

Lemma in_extend_grect p (r : grect) : subpred (predU1 p r) (extend_grect p r).
Proof.
case: r p => x0 x2 y0 y2 [x1 y1] [x y] /predU1P[->|] /=.
  by rewrite !leIx !ltxU !lexx !ltr_addl !orbT.
by rewrite !leIx !ltxU -andbA => /and4P[-> -> -> ->].
Qed.

(* Rectangle dimensions and enumeration. *)

Definition zwidth xmin xmax := if xmax - xmin is w%:Z then w else 0%N.

Definition gwidth r := let: Grect xmin xmax _ _ := r in zwidth xmin xmax.

Definition gheight r := let: Grect _ _ ymin ymax := r in zwidth ymin ymax.

Definition garea r := (gwidth r * gheight r)%N.

Definition gr_proper r := (0 < garea r)%N.

Definition zspan xmin xmax := traject (+%R^~ 1) xmin (zwidth xmin xmax).

Definition enum_grect r :=
  let: Grect xmin xmax ymin ymax := r in
  [seq Gpoint x y | x <- zspan xmin xmax, y <- zspan ymin ymax].

Lemma size_zspan xmin xmax : size (zspan xmin xmax) = zwidth xmin xmax.
Proof. by rewrite /zspan size_traject. Qed.

Lemma size_enum_grect r : size (enum_grect r) = garea r.
Proof. by case: r => x0 x1 y0 y1; rewrite size_allpairs !size_zspan. Qed.

Lemma mem_zspan xmin xmax x : (x \in zspan xmin xmax) = (xmin <= x < xmax).
Proof.
rewrite -[xmax in RHS](subrK xmin) -ltr_subl_addr -subr_ge0 /zspan /zwidth.
case: {xmax}(xmax - xmin) => n; last by case: (x - xmin).
elim: n xmin => [|n IHn] x0; first by rewrite ltNge andbN.
rewrite inE -subr_eq0 {}IHn opprD addrA ler_subr_addl ltr_subl_addl.
by rewrite orb_andr eq_sym -le_eqVlt; case: eqP => // <-.
Qed.

Lemma mem_enum_grect r p : (p \in enum_grect r) = r p.
Proof.
case: r p => [x0 x1 y0 y1] [x y] /=; rewrite -!mem_zspan.
by apply/allpairsP/andP=> [[xy [r_x r_y [-> ->]]]|[]]; last exists (x, y).
Qed.

Lemma gr_properP (r : grect) : reflect (exists p, r p) (gr_proper r).
Proof.
rewrite /gr_proper -size_enum_grect -count_predT -has_count.
by apply (iffP hasP) => -[p r_p]; exists p; rewrite ?mem_enum_grect in r_p *.
Qed.

Lemma zspan_uniq xmin xmax : uniq (zspan xmin xmax).
Proof.
rewrite /zspan /zwidth; case: {xmax}(xmax - xmin) => -[|n] //.
apply/(sorted_uniq lt_trans ltxx)=> /=; set w := traject _ _ _.
have: fpath (+%R^~ 1) xmin w by apply: fpath_traject.
by apply/sub_path=> x _ /eqP<-; rewrite ltr_addl.
Qed.

Lemma enum_grect_uniq r : uniq (enum_grect r).
Proof.
case: r => x0 x1 y0 y1; rewrite allpairs_uniq ?zspan_uniq //.
by apply: in2W => -[_ _] [x y] [-> ->].
Qed.

Lemma garea_subrect (r s : grect) : subpred r s -> (garea r <= garea s)%N.
Proof.
move=> srs; rewrite -!size_enum_grect uniq_leq_size ?enum_grect_uniq // => p.
by rewrite !mem_enum_grect => /srs.
Qed.

Lemma ltn_garea_subrect p (r s : grect) :
  subpred r s -> predD s r p -> (garea r < garea s)%N.
Proof.
move=> sub_r_s; rewrite /= -!size_enum_grect -!mem_enum_grect ltnNge.
apply: contraL => /uniq_min_size[|q|_ ->]; rewrite ?andNb ?enum_grect_uniq //.
by rewrite !mem_enum_grect => /sub_r_s.
Qed.

(* The 3x3 rectangle of pixels that surround a central pixel. *)
Definition gtouch p :=
  let: Gpoint x y := p in Grect (x - 1) (x + 2) (y - 1) (y + 2).

(* The 2x2 rectangle of pixels that surround a grid point. *)
Definition ltouch q :=
  let: Gpoint x y := q in Grect (x - 1) (x + 1) (y - 1) (y + 1).

Lemma subgrectE x0 x1 x2 x3 y0 y1 y2 y3 :
    [/\ x0 <= x1, x2 <= x3, y0 <= y1 & y2 <= y3] ->
  subpred (Grect x1 x2 y1 y2) (Grect x0 x3 y0 y3).
Proof.
case=> lex01 lex23 ley01 ley23 [x y] /andP[] /=.
by do 2![case/andP=> /(le_trans _)-> // /lt_le_trans-> //].
Qed.

Lemma gtouch_l p : subpred (ltouch p) (gtouch p).
Proof. by case: p => x y; apply/subgrectE; rewrite !ler_add2l. Qed.

Lemma ltouch_refl q : ltouch q q.
Proof. by case: q => x y; rewrite /= !ger_addl !ltr_addl. Qed.

Lemma gtouch_refl p : gtouch p p.
Proof. by case: p => x y; rewrite /= !ger_addl !ltr_addl. Qed.

Lemma gtouch_edge d : gtouch (halfg d) (halfg (gedge d)).
Proof.
rewrite halfg_edge; case: (halfg d) => x y.
by case: oddgP; rewrite /= !ler_add2l !ltr_add2l.
Qed.

(* Explicit computation of gtouch and ltouch enumeration. *)
Lemma zspan_dec_inc x n :
  zspan (x - 1) (x + n%:Z) = x - 1 :: traject (+%R^~ 1) x n.
Proof. by rewrite /zspan /zwidth addrAC subKr /= subrK. Qed.

(* Shaving one row or column of pixels on each side of a rectangle. *)
Definition inset r :=
  let: Grect x0 x1 y0 y1 := r in Grect (x0 + 1) (x1 - 1) (y0 + 1) (y1 - 1).

Lemma insetP (r : grect) p : reflect (subpred (gtouch p) r) (inset r p).
Proof.
case: r p => x0 x1 y0 y1 [x y]; rewrite /= -andbA -!ler_subr_addr.
apply/(iffP and4P)=> [[lbx ubx lby uby] | r1x].
  by apply/subgrectE; rewrite !(addrA _ 1 1) !lez_addr1 -!ltr_subr_addr.
rewrite !ltr_subr_addr; have r1dx z := r1x (Gpoint (x + z) (y + z)).
have [] := (r1dx 1, r1dx (-1)); rewrite /= !ler_add2l !ltr_add2l.
by do ![case/implyP/andP | case/andP=> ? ?].
Qed.

Lemma insetW r : subpred (inset r) r.
Proof. by move=> p /insetP/(_ p (gtouch_refl p)). Qed.

(* The half-grid that lies counter-clockwise from a dart. *)

Definition gchop d : gregion :=
  fun p => let: (Gpoint x0 y0, Gpoint x y) := (halfg d, p) in
  oddg_cases (oddg d) (y0 <= y) (x0 <= x) (x <= x0) (y <= y0).

Lemma gchop_halfg d : gchop d (halfg d).
Proof. by rewrite /gchop; case: (halfg d) (oddgP d) => x y [] /=. Qed.

Lemma eq_gchop_halfg d p : halfg d = p -> gchop d p.

Proof. by move <-; apply: gchop_halfg. Qed.

Lemma gchop_edge d p : gchop (gedge d) p = ~~ gchop d p.
Proof.
rewrite /gchop halfg_edge oddg_edge; case: (halfg d) p => x0 y0 [x y] /=.
by case: oddgP; rewrite /= -!ltNge ?lez_addr1 // -ltz_addr1 addrK.
Qed.

Lemma gchop_face_node d : gchop (gface (gnode d)) = gchop (gface (gface d)).
Proof.
rewrite /gchop !halfg_face !oddg_face halfg_node oddg_node.
by case: (halfg d) (oddgP d) => x y [] //=; rewrite addr0.
Qed.

Lemma gchop_shift d : gchop (gface (gedge (gface d))) = gchop d.
Proof. by rewrite -gnode_face gchop_face_node gface4. Qed.

(* Same as above, but extended by a unit band.              *)

Definition gchop1 d : gregion := gchop (gface (gface (gedge d))).

Lemma gchop_chop1 d : subpred (gchop d) (gchop1 d).
Proof.
rewrite /gchop1 /gchop !halfg_face halfg_edge !oddg_face oddg_edge ccw4.
case: (halfg d) => x0 y0 [x y].
by case: oddgP => /= d_p; rewrite ltW // -?ltr_subr_addr ltz_addr1.
Qed.

Lemma gtouch_chop1 d p :
  gtouch (halfg d) p = all (gchop1^~ p) (traject gface d 4).
Proof.
case: p => x y; rewrite /= andbT /gchop1 /gchop !(halfg_face, halfg_edge).
case: (halfg d) => x0 y0; rewrite !(oddg_face, oddg_edge) !ccw4 /=.
rewrite !(addrA _ 1 1) !ltz_addr1.
by case: oddgP; rewrite /= -andbA -?ler_subr_addr; do !bool_congr.
Qed.

Lemma gchop1_shift d : gchop1 (gface (gedge (gface d))) = gchop1 d.
Proof.
by rewrite -[gface d]gnode4 gnode_face /gchop1 !gnodeK gchop_face_node.
Qed.

Section ChopRect.

(* Chopping off half of a rectangle (and excluding the boundary). *)
(* The dividing line is given as the side of an internal square.  *)

Variable r : grect.

Definition gchop_rect d :=
  let: (Grect x0 x1 y0 y1, Gpoint x y) := (r, halfg d) in
  match oddgP d with
  | Gpoint00 => Grect x0 x1 (Num.max y0 y) y1
  | Gpoint01 => Grect (Num.max x0 x) x1 y0 y1
  | Gpoint10 => Grect x0 (Num.min x1 (x + 1)) y0 y1
  | Gpoint11 => Grect x0 x1 y0 (Num.min y1 (y + 1))
  end.

Lemma in_gchop_rect d : gchop_rect d =1 predI r (gchop d).
Proof.
rewrite /gchop_rect /gchop; case: r (halfg d) => x0 x2 y0 y2 [x1 y1] [x y] /=.
case: oddgP; rewrite /= (leUx, ltxI) ?ltz_addr1 -!andbA; do !bool_congr.
Qed.

Lemma gchop_rect_sub d : subpred (gchop_rect d) r.
Proof. by move=> p; rewrite in_gchop_rect => /andP[]. Qed.

Lemma gchop_rect_edge d :
  r (halfg (gedge d)) -> forall p, gchop_rect d p -> gchop_rect d (halfg d).
Proof.
rewrite halfg_edge => r_ed [x y]; rewrite !in_gchop_rect /= gchop_halfg.
rewrite /gchop; case: r (halfg d) => [x0 x2 y0 y2] [x1 y1] /= in r_ed *.
rewrite andbT -!andbA -!lez_addr1 => /and5P[lbx ubx lby uby].
by case: oddgP r_ed; rewrite /= ?addr0 -andbA -!lez_addr1 ?subrK;
   case/and4P=> lbx1 ubx1 lby1 uby1 d_xy; apply/and4P; split=> //;
   rewrite ?lez_addr1 ?(le_trans _ d_xy, le_lt_trans d_xy) -?lez_addr1 //;
   apply/ltW; rewrite -lez_addr1 // -ler_subr_addr.
Qed.

Definition gchop1_rect d := gchop_rect (gface (gface (gedge d))).

Lemma in_gchop1_rect d : gchop1_rect d =1 predI r (gchop1 d).

Proof. apply: in_gchop_rect. Qed.

End ChopRect.

(* Grid refinement, which doubles coordinates and rectangle bounds. *)

Definition refine_rect r :=
  let: Grect x0 x1 y0 y1 := r in Grect (x0 *+ 2) (x1 *+ 2) (y0 *+ 2) (y1 *+ 2).

Lemma in_refine_rect r p : refine_rect r p = r (halfg p).
Proof.
by case: r p => x0 x1 y0 y1 [x y] /=; rewrite !lez_divRL ?ltz_divLR ?mulz2.
Qed.

Lemma garea_refine_rect r : garea (refine_rect r) = (garea r).*2.*2.
Proof.
suffices{r} Dzwidth2 x y: zwidth (x *+ 2) (y *+ 2) = (zwidth x y).*2.
  by case: r => x0 x1 y0 y1; rewrite doubleMl doubleMr -!Dzwidth2.
by rewrite /zwidth -mulrnBl; case: (y - x) => n //=; rewrite addnn.
Qed.

Lemma refine_inset r : refine_rect (inset r) = inset (inset (refine_rect r)).
Proof. by case: r => x0 x1 y0 y1 /=; rewrite !mulrnDl !addrA. Qed.

Lemma gr_proper_refine s r : gr_proper (iter s refine_rect r) = gr_proper r.
Proof.
by elim: s => // s; rewrite /gr_proper garea_refine_rect !double_gt0.
Qed.

End GridGeometry.

Hint Resolve oddgP : core.
Arguments insetP {r p}.
