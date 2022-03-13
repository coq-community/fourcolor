(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype path fingraph.
From fourcolor
Require Import hypermap geometry part quiz quiztree.

(******************************************************************************)
(*   Reducibility check for parts, that is, testing that every 2-neighborhood *)
(* that matches the part contains the embedding of teh kernel of one of the   *)
(* 633 reducible configurations. We use a zipper structure to navigate parts  *)
(* when searching for a reducible configuration. Once we detect a match for   *)
(* the top arity range values, we walk the config quiz again to look for a    *)
(* match for the other values (most of the time, though, the match spans only *)
(* singleton ranges).                                                         *)
(*   We work here under the assumption that the map is plain, cubic, and      *)
(* pentagonal, and that the quiz tree does not directly fit the map at any    *)
(* dart. We show that this lifts to parts for which redpart returns true (for *)
(* a fixed hub size).                                                         *)
(*   Defined here:                                                            *)
(*   redpart qzt p0 <=> if a map fits (exactly) part p0 at dart x0, then the  *)
(*                      quiz_tree qzt fits at some dart x adjacent to x0      *)
(*                      (adj x0 x), such that arity x <= 8 unless x is in the *)
(*                      node of a dart in the face of x0.                     *)
(*  We only prove soundness (the => direction of <=> in the specification     *)
(* above) of redpart; indeed the decision procedure we use is only complete   *)
(* for quiz trees that satisfy certain conditions (to be explained below), as *)
(* is indeed the case for the tree derived from our configuration data. The   *)
(* (experimental) evidence for this is that the unavoidability proof script   *)
(* only performs tests that succeed. However, note that incompleteness was an *)
(* issue during the initial development of our proof, where a subtlety in the *)
(* matching of spokes at articulation points caused an early proof to fail.   *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Redpart.

(* The function is only ever applied to the main quiz tree, but the tree is   *)
(* treated as a parameter here, to prevent unwanted expansions.               *)
Variables (qt : quiz_tree) (G : hypermap).

Hypothesis geoG : plain_cubic_pentagonal G.
Hypothesis fit'qt : forall y : G, ~~ qzt_fit y qt.

Let pentaG : pentagonal G := geoG. (* makes Pr59 (arity _) trivial. *)
Let De2 := plain_eq geoG.
Let Dnf := plain_eq' geoG.
Let Dn3 := cubic_eq geoG.
Let Dn2 := cubic_eq' geoG.
Let Dne (x : G): node (edge x) = face (edge (face x)).
Proof. by rewrite -Dn2 Dnf. Qed.

Let Dfn n (x : G) : arity x == n -> x = iter n face x.
Proof. by move=> /eqP <-; rewrite iter_face_arity. Qed.

Let Dfnn n (x : G) : arity x == n -> node x = edge (iter n.-1 face x).
Proof. by move=> /eqP <-; rewrite -Dnf (f_finv faceI). Qed.

Section RedpartRec.

(******************************************************************************)
(*   In this section we define the function that performs one step of redpart,*)
(* the part reducibility decision procedure: it traverses a given part p0r,   *)
(* looking for an occurrence of a configuration kernel whose face arities     *)
(* match the TOP of the part ranges; note that this automatically excludes    *)
(* subpart locations with a top value of 9 as the specification of redpart    *)
(* excludes such matches. Once a configuration match is found redpart         *)
(* recurses on a set of parts which fit maps that fit p0r but do not contain  *)
(* that particular configuration instance.                                    *)
(*   In this section p0l is the reversal of p0r, ahub the qarity of the hub   *)
(* face of the part (i.e., the size of p0r and p0l), red_rec the recursive    *)
(* check of redpart, and x0 a dart that fits p0r. We assume that red_rec p is *)
(* false for any part of size ahub that fits at a dart x; x need not be x0 as *)
(* we rotate the part so the recursive search cycles along all subparts.      *)
(*   We use zippers to speed up the part traversal during both the question   *)
(* check and the residual recursive checks. A zipper part is a pair of a left *)
(* and right part sectors with the left part reversed (not mirrored!), whose  *)
(* concatenation is twice p0r, together with an index that identifies the     *)
(* dart represented by the zipper part. Such darts are one of the following:  *)
(*  - the two node orbits that fall between the left and right parts, that    *)
(*    is, that contain a dart from both the left spoke and right spoke faces. *)
(*    The third dart is either the hub dart or a hat dart in the right part.  *)
(*  - the (disjoint) qstepL and qstepR trajectories that run around the left  *)
(*    spoke face, counter-clockwise and clockwise, respectively, and end with *)
(*    hat darts (the left chain ends with the hat of the right part and       *)
(*    conversely); positions are numbered in decreasing order, so the first   *)
(*    dart in either chain is number k-5, when the spoke has arity k, and the *)
(*    last (hat) dart is number 0.                                            *)
(* Note that this excludes the fan darts on the spoke face itself, which are  *)
(* not reached by quiz steps (they can only match the central start triangle  *)
(* and therefore don't occur in the recursive traversal).                     *)
(*   Auxiliary definitions in this section:                                   *)
(*      zpart == type of zipper parts.                                        *)
(*  zpart_loc == index type for zpart dart locations: Z[hub|hat][lr]? for the *)
(*               hub/hat inter-spoke nodes, ZfanNl, N in 0..3, for fan        *)
(*               locations, and Znil for 'out of bounds' locations.           *)
(*  zvalid pl pr <-> catrev_part pl pr = cat_part p0r p0r.                    *)
(*  zpvalid zp <-> the left/right sectors of zpart zp satisfy zvalid.         *)
(*  zproper zp <=> the index of zpart zp is not Znil.                         *)
(*     zorg pl == the reference hub dart (in the face orbit of x0) for a      *)
(*                zpart with left sector pl, i.e., the reference dart for the *)
(*                subpart just after pl (that is, face^(size_part pl) x0).    *)
(*  zmove zi x == the dart indexed by zi : zpart_loc, from reference dart x.  *)
(*    zdart zp == the dart in the second neighbourhood of x0 indexed by zp.   *)
(*             := zmove zi (zorg pl) when zp = Zdart zi pl _.                 *)
(*  zpfit zp x <-> if zp is proper, then zdart zp = x.                        *)
(*   zrange zp == the range for the arity of zdart zp.                        *)
(*   hub_range == the range for the hub. This is a singleton unless ahub > 8. *)
(*  shift_part pl pr == the part obtained by prepending the first subpart of  *)
(*                pl to pr; this is the 'right' shift used to rotate zparts   *)
(*                (the 'left' shift is performed by drop_part 1).             *)
(*  p0ll, p0lr, p0rl, p0rr == p0[lr] left/right shifted, respectively.        *)
(*  zshiftl zi zp == the zpart corresponding to the location zi in the        *)
(*                subpart to the left of zp's location.                       *)
(*  zshiftr zi zp == the zpart corresponding to the location zi in the        *)
(*                subpart to the right of zp's location.                      *)
(*  zfan[LR][t] p == the [Left|Right]-most zpart_loc in the Zfan[lr] chain    *)
(*                in the first subpart of p, or Znil if the fitting test is   *)
(*                destined to fail due to an unbounded arity (in particular,  *)
(*                if the spoke arity can't be determined). The t variant is   *)
(*                defined in more cases, because it assumes the spoke arity   *)
(*                is fixed to the top value of the range allowed by p.        *)
(*  zstep[LR][t] zp == a zpart that fits y = qstep[LR] x, where x = zdart zp; *)
(*                this can be an improper part if the question fitting test   *)
(*                at the part would be destined to fail by testing an         *)
(*                unbounded arity, e.g., when there is no zpart_loc value for *)
(*                its location. The t variants assume x's arity is the top    *)
(*                of zrange zp and return fewer improper zparts; conversely   *)
(*                the unadorned variants assume the zrange of their result    *)
(*                will be tested.                                             *)
(* --> We need the t variants to handle double qsteps, where the first step   *)
(* is NOT preceded by an arity check. This means that any step that might     *)
(* precede a double step should use the t variants, or else the check will be *)
(* incomplete for double steps wrapping around a spoke with arity range [5,6] *)
(* or [6]. We could indeed use the t variants for all other steps, but it     *)
(* turns out we only need to do so for QaskL and QaskR steps, and the plain   *)
(* variants somewhat simplify the proof, having fewer preconditions.          *)
(*    topqa qr == the top qarity of qr : prange; Qa9 if qr is unbounded.      *)
(*    fitqa qr qa <=> the top qarity of qr is qa <= 8.                        *)
(*    popqa qr == if qr : prange represents [M, N] with M < N < 9, the prange *)
(*                that represents [M, N-1].                                   *)
(* zpfit_top zp <-> the arity of zdart zp is the top of zprange zp; this is   *)
(*                precondition for using zstep[LR]t.                          *)
(*  fitqzp zp q <=> the arities specified by q : question for a traversal     *)
(*                strting at zdart zp, are the top of the corresponding       *)
(*                ranges in zp.                                               *)
(*  red_pcons pc qr pr <=> qr is unbounded or singleton, or red_rec succeeds  *)
(*                for the part of size ahub obtained by padding the part      *)
(*                sector pc (popqa qr) pr (with pc : prange -> part -> part), *)
(*                with a prefix of p0r.                                       *)
(*  red_popr_[spoke|hat] pr <=> either the spoke/hat range qr of pr is        *)
(*                unbounded or is a singleton, or red_rec succeeds on the     *)
(*                part obtained by 'popping' qr in pr (replacing qr with      *)
(*                popqa qr) and padding with p0r to get a part of size ahub.  *)
(*  red_popl_[spoke|hat|fan[123][lr]] pl pr <=> red_rec succeeds on the part  *)
(*                obtained by 'popping' the spoke/hat/Zfan[123][lr] range in  *)
(*                zshift pl pr, or this range is unbounded or a singleton.    *)
(*  red_pop zp <=> red_rec succeeds on the part obtained by popping zrange zp *)
(*  red_popqzp zp q <=> assuming fitqzp zp q, red_pop succeeds on all the     *)
(*                zparts tested for arity during the traversal of question q. *)
(* --> The recursive calls to red_part in red_popqzp will perform duplicate   *)
(* work if more than one of the ranges is not a singleton. This is not a real *)
(* performance issue, and could be avoided by returning a truncated zpart,    *)
(* where all tested ranges have been replaced by their upper bound.           *)
(* --> fitqzp is expected to usually fail, while red_popqzp should always     *)
(* succeed for questions in a leaf of qzt that satisfy fitqzp.                *)
(*  qzt_getr qr qt1 := qzt_get (topqa qr) qt1.                                *)
(*  red_qzt_leaf zp_1 zp_2 zp_3 qt0 <=> in the 0-height quiz_tree qt0, both   *)
(*                 fitqzp and red_popqzp succeed for all zp_i q_i pairs, for  *)
(*                 one of the leaves QztLeaf q_1 q_2 q_3 _.                   *)
(* --> qt0 is indexed by the arities of darts x_i in the node cycle of a dart *)
(* adjacent to x0, such that zpfit zp_i (qsteprR x_i); if one of the x_i is   *)
(* in a fan, then one of the zp_j (with j != i) will be invalid.              *)
(*  red_zpart_rec zp d <=> for one of the d first right shifts of zpart zp,   *)
(*                 one of the quizzes in qzt matches the range upper bounds   *)
(*                 at a node covered by zpart_loc variants of zp, and red_rec *)
(*                 succeeds on all the parts obtained by popping one of the   *)
(*                 matched ranges.                                            *)
(*   red_zpart <=> one of the quizzes in qzt matches the range upper bounds   *)
(*                 at some node in p0r, and red_rec succeeds on all the parts *)
(*                 obtained by popping one of the matched ranges.             *)
(* --> Under our assumptions about qzt, p0[lr], x0 and red_rec, we show that  *)
(* red_zpart must return false, whence by induction and contraposition that   *)
(* if redpart qzt p0 holds then p0 cannot fit at any dart x in G.             *)
(******************************************************************************)

(* The hub size must be in the qarity range.                                  *)
Variable ahub : qarity.
Let nhub : nat := ahub.

Variable red_rec : part -> bool. (* recursive call to redpart. *)

Hypothesis not_red_rec :
  forall (x : G) p, arity x = nhub -> exact_fitp x p -> ~~ red_rec p.

Variables (p0l p0r : part) (x0 : G).
Hypothesis Dp0l : p0l = rev_part p0r.

Hypotheses (fit_p0r : exact_fitp x0 p0r) (nFx0 : arity x0 = nhub).
Let Ep0r : size_part p0r = nhub.
Proof. by case/andP: fit_p0r => /eqP; rewrite nFx0. Qed.

Inductive zpart_loc : Set :=
  | Znil                               (* out-of-bounds error value *)
  | Zhub | Zhubl | Zhubr               (* hub-side node cycle *)
  | Zhat | Zhatl | Zhatr               (* hat-side node cycle *)
  | Zfan0l | Zfan1l | Zfan2l | Zfan3l  (* the left step chain *)
  | Zfan0r | Zfan1r | Zfan2r | Zfan3r. (* the right step chain *)

Inductive zpart := Zpart of zpart_loc & part & part.

Definition zproper zp := if zp is Zpart Znil _ _ then false else true.

Definition zvalid pl pr := catrev_part pl pr = cat_part p0r p0r.

Definition zpvalid zp := let: Zpart _ pl pr := zp in zvalid pl pr.

Lemma zvalid_init : zvalid p0l p0r.
Proof. by rewrite /zvalid catrev_part_eq Dp0l rev_rev_part. Qed.

Lemma zvalid_fit pl pr : zvalid pl pr -> fitp x0 (catrev_part pl pr).
Proof.
move->; rewrite fitp_cat.
by case/andP: fit_p0r => /eqP <-; rewrite /= (iter_face_arity x0) andbb.
Qed.

Definition zmove zi (x : G) :=
  match zi with
  | Znil => x
  | Zhub => x
  | Zhubl => node x
  | Zhubr => node (node x)
  | Zhat => node (edge (node (node x)))
  | Zhatl => edge (node (node x))
  | Zhatr => face (node (node x))
  | Zfan0l => face (edge (iter 2 (edge \o node) (node x)))
  | Zfan1l => face (edge (iter 3 (edge \o node) (node x)))
  | Zfan2l => face (edge (iter 4 (edge \o node) (node x)))
  | Zfan3l => face (edge (iter 5 (edge \o node) (node x)))
  | Zfan0r => edge (iter 2 face (node x))
  | Zfan1r => edge (iter 3 face (node x))
  | Zfan2r => edge (iter 4 face (node x))
  | Zfan3r => edge (iter 5 face (node x))
  end.

Arguments zmove : simpl never.

Definition zorg pl := iter (size_part pl) face x0.

Definition zporg zp := let: Zpart _ pl _ := zp in zorg pl.

Definition zdart zp := let: Zpart zi pl _ := zp in zmove zi (zorg pl).

Definition zpfit x zp := zproper zp -> zdart zp = x.

Definition hub_range :=
  match ahub with
  | Qa5 => Pr55
  | Qa6 => Pr66
  | Qa7 => Pr77
  | Qa8 => Pr88
  | _   => Pr99
  end.

Definition zrange zp :=
  match zp with
  | Zpart Znil   _  _ => Pr59
  | Zpart Zhub   _  _ => hub_range
  | Zpart Zhubl  pl _ => get_spoke pl
  | Zpart Zhubr  _ pr => get_spoke pr
  | Zpart Zhatl  pl _ => get_spoke pl
  | Zpart Zhat   _ pr => get_hat pr
  | Zpart Zhatr  _ pr => get_spoke pr
  | Zpart Zfan0l _ pr => get_hat pr
  | Zpart Zfan1l pl _ => get_fan1l pl
  | Zpart Zfan2l pl _ => get_fan2l pl
  | Zpart Zfan3l pl _ => get_fan3l pl
  | Zpart Zfan0r pl _ => get_hat pl
  | Zpart Zfan1r pl _ => get_fan1r pl
  | Zpart Zfan2r pl _ => get_fan2r pl
  | Zpart Zfan3r pl _ => get_fan3r pl
  end.

Lemma zrange_dart zp : zpvalid zp -> zrange zp (arity (zdart zp)).
Proof.
case: zp => zi pl pr /zvalid_fit; case: zi; rewrite /= /zmove //=.
- by rewrite arity_iter_face nFx0 /nhub /hub_range; case: ahub => /=.
- by case Dpl: pl; rewrite //= Dnf fitp_catrev; case/and3P.
- by rewrite fitp_catrev Dn2 arity_face; case Dpr: pr => //= /and3P[].
- by rewrite fitp_catrev Dne arity_face Dn2; case Dpr: pr => //= /and4P[].
- rewrite -arity_face nodeK.
  by case Dpl: pl; rewrite //= Dnf fitp_catrev; case/and3P.
- by rewrite fitp_catrev Dn2 !arity_face; case Dpr: pr => //= /and3P[].
- by rewrite fitp_catrev De2 Dne !arity_face Dn2; case Dpr: pr => //= /and4P[].
- by case Dpl: pl; rewrite //= fitp_catrev /= Dnf arity_face;
    case/and4P=> _ Ds _; do !case/andP=> [?]; rewrite (Dfn Ds) !faceK.
- by case Dpl: pl; rewrite //= fitp_catrev /= Dnf arity_face;
    case/and4P=> _ Ds _; do !case/andP=> [?]; rewrite (Dfn Ds) !faceK.
- by case Dpl: pl; rewrite //= fitp_catrev /= Dnf arity_face;
    case/and4P=> _ Ds _; do !case/andP=> [?]; rewrite (Dfn Ds) !faceK.
- by case Dpl: pl; rewrite //= fitp_catrev Dnf => /and4P[].
- by case Dpl: pl; rewrite //= fitp_catrev Dnf => /and5P[].
- by case Dpl: pl; rewrite //= fitp_catrev Dnf => /andP[_ /and5P[]].
by case Dpl: pl; rewrite //= fitp_catrev Dnf => /and3P[_ _ /and5P[]].
Qed.

Definition shift_part p1 p2 := cat_part (take_part 1 p1) p2.

Local Notation p0ll := (drop_part 1 p0l).
Local Notation p0lr := (shift_part p0l p0r).
Local Notation p0rr := (drop_part 1 p0r).
Local Notation p0rl := (shift_part p0r p0l).

Lemma zvalid_initl : zvalid p0ll p0lr.
Proof.
move: Ep0r; rewrite -size_rev_part -Dp0l -nFx0 -orderSpred /zvalid -zvalid_init.
by case p0l.
Qed.

Lemma zvalid_initr : zvalid p0rl p0rr.
Proof.
by move: Ep0r; rewrite -nFx0 -orderSpred /zvalid -zvalid_init; case p0r.
Qed.

Definition zshiftl zi zp :=
  match zp with
  | Zpart _ (Pcons _ _ Pnil) _        => Zpart zi p0l p0r
  | Zpart _ (Pcons6 _ _ Pnil) _       => Zpart zi p0l p0r
  | Zpart _ (Pcons7 _ _ _ Pnil) _     => Zpart zi p0l p0r
  | Zpart _ (Pcons8 _ _ _ _ Pnil) _   => Zpart zi p0l p0r
  | Zpart _ (Pcons s h pl) pr         => Zpart zi pl (Pcons s h pr)
  | Zpart _ (Pcons6 h f1 pl) pr       => Zpart zi pl (Pcons6 h f1 pr)
  | Zpart _ (Pcons7 h f1 f2 pl) pr    => Zpart zi pl (Pcons7 h f1 f2 pr)
  | Zpart _ (Pcons8 h f1 f2 f3 pl) pr => Zpart zi pl (Pcons8 h f1 f2 f3 pr)
  | Zpart _ Pnil _                    => Zpart zi p0ll p0lr
  end.

Definition zshiftr zi zp :=
  match zp with
  | Zpart _ _  (Pcons _ _ Pnil)       => Zpart zi p0l p0r
  | Zpart _ _  (Pcons6 _ _ Pnil)      => Zpart zi p0l p0r
  | Zpart _ _  (Pcons7 _ _ _ Pnil)    => Zpart zi p0l p0r
  | Zpart _ _  (Pcons8 _ _ _ _ Pnil)  => Zpart zi p0l p0r
  | Zpart _ pl (Pcons s h pr)         => Zpart zi (Pcons s h pl) pr
  | Zpart _ pl (Pcons6 h f1 pr)       => Zpart zi (Pcons6 h f1 pl) pr
  | Zpart _ pl (Pcons7 h f1 f2 pr)    => Zpart zi (Pcons7 h f1 f2 pl) pr
  | Zpart _ pl (Pcons8 h f1 f2 f3 pr) => Zpart zi (Pcons8 h f1 f2 f3 pl) pr
  | Zpart _ _  Pnil                   => Zpart zi p0rl p0rr
  end.

Lemma zpvalid_shiftl zi zp : zpvalid zp -> zpvalid (zshiftl zi zp).
Proof.
case: zp => [_ pl pr] /=; move: zvalid_init zvalid_initl.
by case: pl => //= [s h|h f1|h f1 f2|h f1 f2 f3] [].
Qed.

Lemma zproper_shiftl zi zp :
  zproper (zshiftl zi zp) = if zi is Znil then false else true.
Proof.
by case: zp => [_ pl pr] /=; case: pl => //= [s h|h f1|h f1 f2|h f1 f2 f3] [].
Qed.

Lemma zpvalid_shiftr zi zp : zpvalid zp -> zpvalid (zshiftr zi zp).
Proof.
case: zp => [_ pl pr] /=; move: zvalid_init zvalid_initr.
by case: pr => //= [s h|h f1|h f1 f2|h f1 f2 f3] [].
Qed.

Lemma zproper_shiftr  zi zp :
  zproper (zshiftr zi zp) = if zi is Znil then false else true.
Proof.
by case: zp => [_ pl pr] /=; case: pr => //= [s h|h f1|h f1 f2|h f1 f2 f3] [].
Qed.

Lemma zshiftl_eq zi zi' pl pr :
   1 < size_part pl ->
 zshiftl zi' (Zpart zi pl pr) = Zpart zi' (drop_part 1 pl) (shift_part pl pr).
Proof. by case: pl => // [s h|h f1|h f1 f2|h f1 f2 f3] []. Qed.

Lemma zshiftr_eq zi zi' pl pr :
   1 < size_part pr ->
 zshiftr zi' (Zpart zi pl pr) = Zpart zi' (shift_part pr pl) (drop_part 1 pr).
Proof. by case: pr => // [s h|h f1|h f1 f2|h f1 f2 f3] []. Qed.

Lemma zdart_shiftl zi zp :
  zdart (zshiftl zi zp) = zmove zi (edge (node (zporg zp))).
Proof.
have sz0l: size_part p0l = arity x0 by rewrite Dp0l size_rev_part Ep0r nFx0.
have zorg0l: zorg p0l = x0 by rewrite /zorg sz0l iter_face_arity.
case: zp => zi' pl pr; case sz_pl: (size_part pl) => [|n].
  rewrite -(finv_eq_can faceK); case: pl => // in sz_pl *.
  by congr (zmove zi _); rewrite /zorg size_drop_part sz0l subn1.
by case: pl sz_pl => // [s h|h ?|h ? ?|h ? ? ?] [] *; rewrite /= faceK ?zorg0l.
Qed.

Lemma zdart_shiftr zi zp :
  zpvalid zp -> zdart (zshiftr zi zp) = zmove zi (face (zporg zp)).
Proof.
case: zp => zi' pl pr /(congr1 size_part).
rewrite catrev_part_eq size_cat_part size_rev_part -iterS.
case sz_pr: (size_part pr) => [|[|n]] sz_pl; rewrite ?addn0 ?addn1 in sz_pl.
- rewrite {}sz_pl -zvalid_initr catrev_part_eq size_cat_part size_rev_part.
  rewrite size_drop_part subn1 Ep0r -nFx0 -addnS iterD [RHS]/=(f_finv faceI).
  by case: pr sz_pr.
- rewrite {}sz_pl -zvalid_init catrev_part_eq size_cat_part size_rev_part.
  rewrite iterD Ep0r -nFx0 iter_face_arity.
  by case: pr sz_pr => // [s h|h f1|h f1 f2|h f1 f2 f3] [].
by case: pr sz_pr => // [s h|h f1|h f1 f2|h f1 f2 f3] [].
Qed.

Definition zfanL pr :=
  match pr with
  | Pcons Pr55 _ _   => Zfan0l
  | Pcons6 _ _ _     => Zfan1l
  | Pcons7 _ _ _   _ => Zfan2l
  | Pcons8 _ _ _ _ _ => Zfan3l
  | _                => Znil
  end.

Definition zfanR pl :=
  match pl with
  | Pcons Pr55 _ _   => Zfan0r
  | Pcons6 _ _ _     => Zfan1r
  | Pcons7 _ _ _ _   => Zfan2r
  | Pcons8 _ _ _ _ _ => Zfan3r
  | _                => Znil

  end.

Definition zstepL zp :=
  match zp with
  | Zpart Zhub _ _     => zshiftl Zhubl zp
  | Zpart Zhubl pl pr  => Zpart Zhat pl pr
  | Zpart Zhubr _ _    => zshiftr Zhubr zp
  | Zpart Zhat _ pr    => zshiftr (zfanL pr) zp
  | Zpart Zhatl pl pr  => Zpart (zfanR pl) pl pr
  | Zpart Zhatr pl pr  => Zpart Zhub pl pr
  | Zpart Zfan0l pl pr => Zpart Zhatr pl pr
  | Zpart Zfan1l pl pr => Zpart Zfan0l pl pr
  | Zpart Zfan2l pl pr => Zpart Zfan1l pl pr
  | Zpart Zfan3l pl pr => Zpart Zfan2l pl pr
  | Zpart _ pl pr      => Zpart Znil pl pr
  end.

Definition zstepR zp  :=
  match zp with
  | Zpart Zhub _ _     => zshiftr Zhubr zp
  | Zpart Zhubl _ _    => zshiftl Zhubl zp
  | Zpart Zhubr pl pr  => Zpart Zhat pl pr
  | Zpart Zhat pl pr   => Zpart (zfanR pl) pl pr
  | Zpart Zhatl pl pr  => Zpart Zhub pl pr
  | Zpart Zhatr _ pr   => zshiftr (zfanL pr) zp
  | Zpart Zfan0r _ _   => zshiftl Zhatl zp
  | Zpart Zfan1r pl pr => Zpart Zfan0r pl pr
  | Zpart Zfan2r pl pr => Zpart Zfan1r pl pr
  | Zpart Zfan3r pl pr => Zpart Zfan2r pl pr
  | Zpart _ pl pr      => Zpart Znil pl pr
  end.

Lemma zproper_stepL zp : zproper (zstepL zp) -> zproper zp.
Proof. by case: zp => -[]. Qed.

Lemma zpvalid_stepL zp : zpvalid zp -> zpvalid (zstepL zp).
Proof.
by case: zp => -[] // pl pr; do [apply: zpvalid_shiftl | apply: zpvalid_shiftr].
Qed.

Lemma zdart_stepL zp : zpvalid zp -> zpfit (qstepL (zdart zp)) (zstepL zp).
Proof.
rewrite /zstepL /qstepL; case: zp => zi pl pr.
case Dzi: zi => // [] zp_ok zp_proper;
  rewrite ?zdart_shiftr ?zdart_shiftl //= /zmove /= ?Dn3 //;
  do [by rewrite ?Dnf ?De2 // ?Dn2 ?De2 ?nodeK | move/zvalid_fit: zp_ok].
- rewrite fitp_catrev; move: zp_proper; rewrite zproper_shiftr -/(zorg pl).
  by case: pr => [|[] h|h f1|h f1 f2|h f1 f2 f3] //= pr _ /and3P[_ Ds _];
     rewrite Dnf [in LHS](Dfn Ds) ?faceK !Dn2 !De2 -!Dnf Dn2 !Dnf.
by case: pl zp_proper => [|[] h|h f1|h f1 f2|h f1 f2 f3] //= pl _;
   rewrite fitp_catrev /= Dnf => /and3P[_ Ds _];
   rewrite [in RHS](Dfn Ds) ?faceK ?Dnf.
Qed.

Lemma zproper_stepR zp : zproper (zstepR zp) -> zproper zp.
Proof. by case: zp => -[]. Qed.

Lemma zpvalid_stepR zp : zpvalid zp -> zpvalid (zstepR zp).
Proof.
by case: zp => -[] // pl pr; do [apply: zpvalid_shiftl | apply: zpvalid_shiftr].
Qed.

Lemma zdart_stepR zp : zpvalid zp -> zpfit (qstepR (zdart zp)) (zstepR zp).
Proof.
rewrite /zstepR /qstepR; case: zp => zi pl pr.
case Dzi: zi => // [] zp_ok zp_proper;
  rewrite ?zdart_shiftr ?zdart_shiftl //= /zmove /= ?Dn3 ?De2 ?Dn3 ?Dnf //;
  do [by rewrite Dn2 De2 | move/zvalid_fit: zp_ok zp_proper].
- by case: pl => //= [s h|h f1|h f1 f2|h f1 f2 f3] pl; try case: s => //=;
     rewrite fitp_catrev /= => /and3P[_ Ds _] _;
     rewrite Dnf {1}[x0]lock (Dfn Ds) /= ?faceK -lock Dnf.
rewrite fitp_catrev zproper_shiftr !Dn2.
by case: pr => //= [[] //= h|h f1|h f1 f2|h f1 f2 f3] pr /and3P[_ Ds _] _;
   rewrite [in LHS](Dfn Ds) ?faceK !Dnf // -Dn2 Dnf.
Qed.

Definition topqa r :=
  match r with
  |                        Pr55 => Qa5
  |               (Pr56 | Pr66) => Qa6
  |        (Pr57 | Pr67 | Pr77) => Qa7
  | (Pr58 | Pr68 | Pr78 | Pr88) => Qa8
  |                          _  => Qa9
  end.

Definition fitqa r qa :=
  match r, qa with
  |                       Pr55,  Qa5 => true
  |               (Pr56 | Pr66), Qa6 => true
  |        (Pr57 | Pr67 | Pr77), Qa7 => true
  | (Pr58 | Pr68 | Pr78 | Pr88), Qa8 => true
  |                           _,   _ => false
  end.

Definition popqa r :=
  match r with
  | Pr56 => Pr55
  | Pr57 => Pr56
  | Pr58 => Pr57
  | Pr67 => Pr66
  | Pr68 => Pr67
  | Pr78 => Pr77
  | _    => Pr99
  end.

Lemma fitqa_topqa r qa : fitqa r qa = (qa <= 8) && (qa == topqa r :> nat).
Proof. by case: r qa => -[]. Qed.

Lemma fitqa_proper zp qa : fitqa (zrange zp) qa -> zproper zp.
Proof. by case: zp => -[]. Qed.

Lemma fitqa_popqa r qa :
  fitqa r qa -> forall n, r n && (popqa r 9 || ~~ popqa r n) -> n = qa.
Proof. by case: r qa => -[] // _; do 9!case=> //. Qed.

Definition zpfit_top zp := arity (zdart zp) = topqa (zrange zp).

(* Variants of the step functions that assume that (zpfit_top zp) holds. *)

Definition zfanLt pr :=
  match pr with
  | Pcons Pr55 _ _   => Zfan0l
  | Pcons Pr56 _ _   => Zfan1l
  | Pcons Pr66 _ _   => Zfan1l
  | Pcons6 _ _ _     => Zfan1l
  | Pcons7 _ _ _ _   => Zfan2l
  | Pcons8 _ _ _ _ _ => Zfan3l
  | _                => Znil
  end.

Definition zfanRt pl :=
  match pl with
  | Pcons Pr55 _ _   => Zfan0r
  | Pcons Pr56 _ _   => Zfan1r
  | Pcons Pr66 _ _   => Zfan1r
  | Pcons6 _ _ _     => Zfan1r
  | Pcons7 _ _ _ _   => Zfan2r
  | Pcons8 _ _ _ _ _ => Zfan3r
  | _                => Znil
  end.

Definition zstepLt zp : zpart :=
  match zp with
  | Zpart Zhub _ _     => zshiftl Zhubl zp
  | Zpart Zhubl pl pr  => Zpart Zhat pl pr
  | Zpart Zhubr _ _    => zshiftr Zhubr zp
  | Zpart Zhat _ pr    => zshiftr (zfanL pr) zp
  | Zpart Zhatl pl pr  => Zpart (zfanRt pl) pl pr
  | Zpart Zhatr pl pr  => Zpart Zhub pl pr
  | Zpart Zfan0l pl pr => Zpart Zhatr pl pr
  | Zpart Zfan1l pl pr => Zpart Zfan0l pl pr
  | Zpart Zfan2l pl pr => Zpart Zfan1l pl pr
  | Zpart Zfan3l pl pr => Zpart Zfan2l pl pr
  | Zpart _ pl pr      => Zpart Znil pl pr
  end.

Definition zstepRt zp :=
  match zp with
  | Zpart Zhub _ _     => zshiftr Zhubr zp
  | Zpart Zhubl _ _    => zshiftl Zhubl zp
  | Zpart Zhubr pl pr  => Zpart Zhat pl pr
  | Zpart Zhat pl pr   => Zpart (zfanR pl) pl pr
  | Zpart Zhatl pl pr  => Zpart Zhub pl pr
  | Zpart Zhatr _ pr   => zshiftr (zfanLt pr) zp
  | Zpart Zfan0r _ _   => zshiftl Zhatl zp
  | Zpart Zfan1r pl pr => Zpart Zfan0r pl pr
  | Zpart Zfan2r pl pr => Zpart Zfan1r pl pr
  | Zpart Zfan3r pl pr => Zpart Zfan2r pl pr
  | Zpart _ pl pr      => Zpart Znil pl pr
  end.

Lemma zproper_stepLt zp : zproper (zstepLt zp) -> zproper zp.
Proof. by case: zp => -[]. Qed.

Lemma zpvalid_stepLt zp : zpvalid zp -> zpvalid (zstepLt zp).
Proof.
by case: zp => -[] // pl pr; do [apply: zpvalid_shiftl | apply: zpvalid_shiftr].
Qed.

Lemma zdart_stepLt zp :
  zpfit_top zp -> zpvalid zp -> zpfit (qstepL (zdart zp)) (zstepLt zp).
Proof.
case: zp => zi pl pr zp_top /zdart_stepL; case: zi zp_top => // /eqP/Dfn->.
by case: pl => // -[] // h pl _ _ /=; rewrite /qstepL !faceK nodeK Dnf.
Qed.

Lemma zproper_stepRt zp : zproper (zstepRt zp) -> zproper zp.
Proof. by case: zp => [[]]. Qed.

Lemma zpvalid_stepRt zp : zpvalid zp -> zpvalid (zstepRt zp).
Proof.
by case: zp => -[] // pl pr; do [apply: zpvalid_shiftl | apply: zpvalid_shiftr].
Qed.

Lemma zdart_stepRt zp :
  zpfit_top zp -> zpvalid zp -> zpfit (qstepR (zdart zp)) (zstepRt zp).
Proof.
case: zp => zi pl pr zp_top zp_ok; have /zdart_stepR := zp_ok.
case: zi zp_ok zp_top => // zp_ok /eqP/Dfn/(congr1 (iter 4 (edge \o node))).
rewrite /zpfit !zdart_shiftr ?zproper_shiftr {zp_ok}//= [qstepR _]Dne /zmove /=.
by case: pr => // -[] // h pr; rewrite !faceK Dn3 Dnf !De2 => ->; rewrite Dnf.
Qed.

(* Updating a part. *)

Definition red_pcons pc r (pr : part) :=
  let rpc r' := red_rec (take_part nhub (cat_part (pc r' pr) p0r)) in
  match r with
  | Pr56 => rpc Pr55
  | Pr57 => rpc Pr56
  | Pr58 => rpc Pr57
  | Pr67 => rpc Pr66
  | Pr68 => rpc Pr67
  | Pr78 => rpc Pr77
  | _    => true
  end.

Lemma red_pcons_fit pc j :
    part_update pc j ->
    forall r pl pr, zvalid pl (pc r pr) ->
    forall qa, fitqa r qa -> red_pcons pc r pr ->
  arity (j G (zorg pl)) = qa.
Proof.
move: j => df Dpcj r pl pr p_ok qa Eqa pc_red; apply: (fitqa_popqa Eqa).
have:= zvalid_fit p_ok; rewrite fitp_catrev => /andP[_ fit_pc_r].
set y := iter _ _ x0 in fit_pc_r *.
have Ey: arity y = nhub by rewrite /y arity_iter_face.
case: (Dpcj r pr) => Epr /(_ G y fit_pc_r)[-> fit_pc].
rewrite orbC -implybE; apply/implyP => Ery.
set p0r1 := cat_part (pc (popqa r) pr) p0r.
suffices fit_p0r1: exact_fitp y (take_part nhub p0r1).
  by apply: contraR (not_red_rec Ey fit_p0r1); rewrite /p0r1; case: (r) pc_red.
have[[_ x0p0r] Ep0r1] := (andP fit_p0r, cat_take_drop_part nhub p0r1).
apply/andP; split.
  move/eqP: (congr1 size_part Ep0r1); rewrite size_cat_part Ey eq_sym.
  by rewrite size_drop_part size_cat_part Ep0r addnK addnC eqn_add2r.
suffices: fitp y p0r1 by rewrite -{1}Ep0r1 fitp_cat => /andP[].
rewrite fitp_cat fit_pc // -iterD addnC.
have [-> _] := Dpcj (popqa r) pr; rewrite -{}Epr -(size_rev_part pl).
rewrite -size_cat_part -catrev_part_eq p_ok size_cat_part  Ep0r -nFx0.
by rewrite iterD !iter_face_arity.
Qed.

Definition red_popr_spoke pr :=
  if pr is Pcons s h p then red_pcons (Pcons^~ h) s p else true.

Lemma red_popr_spoke_fit pl pr :
    zvalid pl pr ->
    forall qa, fitqa (get_spoke pr) qa -> red_popr_spoke pr -> 
  arity (edge (zorg pl)) = qa.
Proof.
by case: pr => // [s h|h f1|h f1 f2|h f1 f2 f3] pr;
   do [ apply: (red_pcons_fit (updatePs h))
      | move/zvalid_fit; rewrite fitp_catrev /= => /and3P[_ /eqP-> _] []].
Qed.

Definition red_popr_hat pr :=
  match pr with
  | Pcons s h p         => red_pcons (Pcons s) h p
  | Pcons6 h f1 p       => red_pcons (Pcons6^~ f1) h p
  | Pcons7 h f1 f2 p    => red_pcons (fun h' => Pcons7 h' f1 f2) h p
  | Pcons8 h f1 f2 f3 p => red_pcons (fun h' => Pcons8 h' f1 f2 f3) h p
  | _                   => true
  end.

Lemma red_popr_hat_fit pl pr :
    zvalid pl pr ->
    forall qa, fitqa (get_hat pr) qa -> red_popr_hat pr ->
  arity (Phat G (zorg pl)) = qa.
Proof.
case: pr => // [s h | h f1 | h f1 f2 | h f1 f2 f3] pr.
- exact: (red_pcons_fit (updatePh s)).
- exact: (red_pcons_fit (updateP6h f1)).
- exact: (red_pcons_fit (updateP7h f1 f2)).
exact: (red_pcons_fit (updateP8h f1 f2 f3)).
Qed.

Definition red_popl_spoke pl pr :=
  if pl is Pcons s h _ then red_pcons (Pcons^~ h) s pr else true.

Lemma red_popl_spoke_fit pl pr :
    zvalid pl pr ->
    forall qa, fitqa (get_spoke pl) qa -> red_popl_spoke pl pr ->
  arity (node (zorg pl)) = qa.
Proof.
by case: pl => // [s h|h f1|h f1 f2|h f1 f2 f3] pl; rewrite /zvalid /= Dnf;
  do [ apply: (red_pcons_fit (updatePs h))
     | move/zvalid_fit; rewrite fitp_catrev /= => /and3P[_ /eqP-> _] []].
Qed.

Definition red_popl_hat pl pr :=
  match pl with
  | Pcons s h _         => red_pcons (fun r => Pcons s r) h pr
  | Pcons6 h f1 _       => red_pcons (fun r => Pcons6 r f1) h pr
  | Pcons7 h f1 f2 _    => red_pcons (fun r => Pcons7 r f1 f2) h pr
  | Pcons8 h f1 f2 f3 _ => red_pcons (fun r => Pcons8 r f1 f2 f3) h pr
  | _                   => true
  end.

Lemma red_popl_hat_fit pl pr :
    zvalid pl pr ->
    forall qa, fitqa (get_hat pl) qa -> red_popl_hat pl pr ->
  arity (edge (iter 2 face (node (zorg pl)))) = qa.
Proof.
case: pl => //= [s h | h f1 | h f1 f2 | h f1 f2 f3] pl; rewrite Dnf /zvalid /=.
- exact: (red_pcons_fit (updatePh _)).
- exact: (red_pcons_fit (updateP6h _)).
- exact: (red_pcons_fit (updateP7h _ _)).
exact: (red_pcons_fit (updateP8h _ _ _)).
Qed.

Definition red_popl_fan1l pl pr :=
  match pl with
  | Pcons6 h f1 _       => red_pcons (fun r => Pcons6 h r) f1 pr
  | Pcons7 h f1 f2 _    => red_pcons (fun r => Pcons7 h f1 r) f2 pr
  | Pcons8 h f1 f2 f3 _ => red_pcons (fun r => Pcons8 h f1 f2 r) f3 pr
  | _                   => true
  end.

Definition red_popl_fan2l pl pr :=
  match pl with
  | Pcons7 h f1 f2 _    => red_pcons (fun r => Pcons7 h r f2) f1 pr
  | Pcons8 h f1 f2 f3 _ => red_pcons (fun r => Pcons8 h f1 r f3) f2 pr
  | _                   => true
  end.

Definition red_popl_fan3l pl pr :=
  match pl with
  | Pcons8 h f1 f2 f3 _ => red_pcons (fun r => Pcons8 h r f2 f3) f1 pr
  | _                   => true
  end.

Definition red_popl_fan1r pl pr :=
  match pl with
  | Pcons6 h f1 _       => red_pcons (fun r => Pcons6 h r) f1 pr
  | Pcons7 h f1 f2 _    => red_pcons (fun r => Pcons7 h r f2) f1 pr
  | Pcons8 h f1 f2 f3 _ => red_pcons (fun r => Pcons8 h r f2 f3) f1 pr
  | _                   => true
  end.

Definition red_popl_fan2r pl pr :=
  match pl with
  | Pcons7 h f1 f2 _    => red_pcons (fun r => Pcons7 h f1 r) f2 pr
  | Pcons8 h f1 f2 f3 _ => red_pcons (fun r => Pcons8 h f1 r f3) f2 pr
  | _                   => true
  end.

Definition red_popl_fan3r pl pr :=
  match pl with
  | Pcons8 h f1 f2 f3 _ => red_pcons (fun r => Pcons8 h f1 f2 r) f3 pr
  | _                   => true
  end.

Lemma red_popl_fan1l_fit pl pr : zvalid pl pr ->
    forall qa, fitqa (get_fan1l pl) qa -> red_popl_fan1l pl pr ->
  arity (zdart (Zpart Zfan1l pl pr)) = qa.
Proof.
case: pl => // [h f1|h f1 f2|h f1 f2 f3] pl; rewrite /zvalid /= => Ep0r2;
  move/zvalid_fit: Ep0r2 (Ep0r2); rewrite fitp_catrev /= => /and3P[_ Dn _];
  rewrite /zmove /= Dnf (Dfn Dn) /= ?faceK arity_face.
- exact: (red_pcons_fit (updateP6f1 _)).
- exact: (red_pcons_fit (updateP7f2 _ _)).
exact: (red_pcons_fit (updateP8f3 _ _ _)).
Qed.

Lemma red_popl_fan2l_fit pl pr :
     zvalid pl pr ->
    forall qa, fitqa (get_fan2l pl) qa -> red_popl_fan2l pl pr ->
  arity (zdart (Zpart Zfan2l pl pr)) = qa.
Proof.
case: pl => // [h f1 f2|h f1 f2 f3] pl; rewrite /zvalid /= => Ep0r2;
  move/zvalid_fit: Ep0r2 (Ep0r2); rewrite fitp_catrev /= => /and3P[_ Dn _];
  rewrite /zmove /= Dnf (Dfn Dn) /= ?faceK arity_face.
- exact: (red_pcons_fit (updateP7f1 _ _)).
exact: (red_pcons_fit (updateP8f2 _ _ _)).
Qed.

Lemma red_popl_fan3l_fit pl pr :
    zvalid pl pr ->
    forall qa, fitqa (get_fan3l pl) qa -> red_popl_fan3l pl pr ->
  arity (zdart (Zpart Zfan3l pl pr)) = qa.
Proof.
case: pl => // [h f1 f2 f3] pl; rewrite /zvalid /= => Ep0r2.
move/zvalid_fit: Ep0r2 (Ep0r2); rewrite fitp_catrev /= => /and3P[_ Dn _].
rewrite /zmove /= Dnf (Dfn Dn) /= ?faceK arity_face.
exact: (red_pcons_fit (updateP8f1 _ _ _)).
Qed.

Lemma red_popl_fan1r_fit pl pr :
    zvalid pl pr ->
    forall qa, fitqa (get_fan1r pl) qa -> red_popl_fan1r pl pr ->
  arity (zdart (Zpart Zfan1r pl pr)) = qa.
Proof.
case: pl => // h f => [|f2|f2 f3] pl; rewrite /zvalid /= /zmove /= Dnf.
- exact: (red_pcons_fit (updateP6f1 _)).
- exact: (red_pcons_fit (updateP7f1 _ _)).
exact: (red_pcons_fit (updateP8f1 _ _ _)).
Qed.

Lemma red_popl_fan2r_fit pl pr :
    zvalid pl pr ->
    forall qa : qarity, fitqa (get_fan2r pl) qa -> red_popl_fan2r pl pr ->
  arity (zdart (Zpart Zfan2r pl pr)) = qa.
Proof.
case: pl => // h f1 f2 => [|f3] pl; rewrite /zvalid /= /zmove /= Dnf.
  exact: (red_pcons_fit (updateP7f2 _ _)).
exact: (red_pcons_fit (updateP8f2 _ _ _)).
Qed.

Lemma red_popl_fan3r_fit pl pr :
    zvalid pl pr ->
    forall qa, fitqa (get_fan3r pl) qa -> red_popl_fan3r pl pr ->
  arity (zdart (Zpart Zfan3r pl pr)) = qa.
Proof.
case: pl => // h f1 f2 f3 pl; rewrite /zvalid /= /zmove /= Dnf.
exact: (red_pcons_fit (updateP8f3 _ _ _)).
Qed.

Definition red_pop zp :=
  match zp with
  | Zpart Zhubl  pl pr => red_popl_spoke pl pr
  | Zpart Zhubr  pl pr => red_popr_spoke pr
  | Zpart Zhatl  pl pr => red_popl_spoke pl pr
  | Zpart Zhat   pl pr => red_popr_hat pr
  | Zpart Zhatr  pl pr => red_popr_spoke pr
  | Zpart Zfan0l pl pr => red_popr_hat pr
  | Zpart Zfan1l pl pr => red_popl_fan1l pl pr
  | Zpart Zfan2l pl pr => red_popl_fan2l pl pr
  | Zpart Zfan3l pl pr => red_popl_fan3l pl pr
  | Zpart Zfan0r pl pr => red_popl_hat pl pr
  | Zpart Zfan1r pl pr => red_popl_fan1r pl pr
  | Zpart Zfan2r pl pr => red_popl_fan2r pl pr
  | Zpart Zfan3r pl pr => red_popl_fan3r pl pr
  | _                  => true
  end.

Lemma red_pop_fit zp :
    zpvalid zp -> forall qa, fitqa (zrange zp) qa -> red_pop zp ->
  arity (zdart zp) = qa.
Proof.
case: zp => [[] //= pl pr]; rewrite /zmove /=; try exact: red_popl_spoke_fit.
- by rewrite arity_iter_face nFx0 /hub_range /nhub; case ahub => // _ [].
- by rewrite Dn2 arity_face; apply: red_popr_spoke_fit.
- by rewrite -Dnf !Dn2 arity_face; apply: red_popr_hat_fit.
- by rewrite -arity_face nodeK; apply: red_popl_spoke_fit.
- by rewrite Dn2 !arity_face; apply: red_popr_spoke_fit.
- by rewrite De2 -Dnf !Dn2 !arity_face; apply: red_popr_hat_fit.
- exact: red_popl_fan1l_fit.
- exact: red_popl_fan2l_fit.
- exact: red_popl_fan3l_fit.
- exact: red_popl_hat_fit.
- exact: red_popl_fan1r_fit.
- exact: red_popl_fan2r_fit.
exact: red_popl_fan3r_fit.
Qed.

Fixpoint fitqzp (zp : zpart) (q : question) {struct q} : bool :=
  match q with
  | Qask0 =>
      true
  | Qask1 qa =>
      fitqa (zrange zp) qa
  | QaskL qa ql =>
      if fitqa (zrange zp) qa then fitqzp (zstepLt zp) ql else false
  | QaskR qa qr =>
      if fitqa (zrange zp) qa then fitqzp (zstepRt zp) qr else false
  | QaskLR qa ql qr =>
      if fitqa (zrange zp) qa then
        if fitqzp (zstepL zp) ql then fitqzp (zstepR zp) qr else false
      else false
  | QaskLL qa ql =>
      let zpl := zstepL zp in
      if fitqa (zrange zpl) qa then fitqzp (zstepL zpl) ql else false
  | QaskRR qa qr =>
      let zpr := zstepR zp in
      if fitqa (zrange zpr) qa then fitqzp (zstepR zpr) qr else false
  end.

Fixpoint red_popqzp (zp : zpart) (q : question) {struct q} : bool :=
  match q with
  | Qask0 =>
      true
  | Qask1 _ =>
      red_pop zp
  | QaskL qa ql =>
      red_pop zp && red_popqzp (zstepLt zp) ql
  | QaskR qa qr =>
      red_pop zp && red_popqzp (zstepRt zp) qr
  | QaskLR qa ql qr =>
      [&& red_pop zp, red_popqzp (zstepL zp) ql & red_popqzp (zstepR zp) qr]
  | QaskLL qa ql =>
      let zpl := zstepL zp in red_pop zpl && red_popqzp (zstepL zpl) ql
  | QaskRR qa qr =>
      let zpr := zstepR zp in red_pop zpr && red_popqzp (zstepR zpr) qr
  end.

Lemma fitqzp_proper zp q : fitqzp zp q -> Qask0 = q \/ zproper zp.
Proof. by case: q; first by [left]; case: zp => -[]; right. Qed.

Lemma fitqzp_fit zp q :
  fitqzp zp q -> red_popqzp zp q -> zpvalid zp -> fitq (zdart zp) q.
Proof.
elim: q zp => //=.
- move=> qa zp Eqa red_zp zp_ok.
  by apply/eqP; rewrite /= (red_pop_fit zp_ok Eqa red_zp).
- move=> qa ql IHq zp; case: ifP => // Eqa fit_ql /andP[red_zp red_ql] zp_ok.
  have Dqa := red_pop_fit zp_ok Eqa red_zp; rewrite /fitq /= eqseq_cons Dqa.
  rewrite eqxx andTb; have [<- // | zpLok]  := fitqzp_proper fit_ql.
  move: Eqa; rewrite fitqa_topqa -{qa}Dqa => /andP[_ /eqP Eqa].
  by rewrite -zdart_stepLt //; apply: IHq => //; apply zpvalid_stepLt.
- move=> qa qr IHq zp; case: ifP => // Eqa fit_qr /andP[red_zp red_qr] zp_ok.
  have Dqa := red_pop_fit zp_ok Eqa red_zp; rewrite /fitq /= eqseq_cons Dqa.
  rewrite eqxx andTb; have [<- // | zpRok] := fitqzp_proper fit_qr.
  move: Eqa; rewrite fitqa_topqa -{qa}Dqa => /andP[_ /eqP Eqa].
  by rewrite -zdart_stepRt //; apply: IHq => //; apply zpvalid_stepRt.
- move=> qa ql IHql qr IHqr zp; case: ifP => // Eqa.
  case: ifP => // fit_ql fit_qr /and3P[red_zp red_ql red_qr] zp_ok.
  rewrite /fitq /= eqseq_cons fitq_cat (red_pop_fit zp_ok Eqa) ?eqxx //=.
  apply/andP; split.
    have [<- // | zpLok] := fitqzp_proper fit_ql.
    by rewrite -zdart_stepL // IHql //; apply: zpvalid_stepL.
  have [<- // | zpOrk] := fitqzp_proper fit_qr.
  by rewrite -zdart_stepR // [_ == _]IHqr //; apply: zpvalid_stepR.
- move=> qa ql IHq zp; set zpl := zstepL zp.
  case: ifP => // Eqa fit_ql /andP[red_zp red_ql] zp_ok.
  rewrite /fitq /= eqseq_cons -arity_face nodeK.
  rewrite -zdart_stepL // -/zpl; last by case: (zpl) Eqa => [[]].
  have{zp_ok} zpLok := zpvalid_stepL zp_ok.
  rewrite /zpl (red_pop_fit _ Eqa) // eqxx.
  have [<- // | zpLproper] := fitqzp_proper fit_ql.
  by rewrite -zdart_stepL // [_ == _]IHq //; apply: zpvalid_stepL.
move=> qa ql IHq zp; set zpr := zstepR zp.
case: ifP => // Eqa fit_qr /andP[red_zp req_qr] zp_ok.
rewrite /fitq /= eqseq_cons -zdart_stepR // -/zpr; last first.
  by case: (zpr) Eqa => [][].
have{zp_ok} zpRok := zpvalid_stepR zp_ok.
rewrite /zpr (red_pop_fit _ Eqa) // eqxx.
have [<- // | zpRproper] := fitqzp_proper fit_qr.
by rewrite -zdart_stepR // [_ == _]IHq => //; apply: zpvalid_stepR.
Qed.

Section RedQztLeaf.

Variable zp1 zp2 zp3 : zpart.

Fixpoint red_qzt_leaf (qtl : quiz_tree) : bool :=
  if qtl is QztLeaf q1 q2 q3 qtl' then
    if fitqzp zp3 q3 then
      if fitqzp zp2 q2 then
        if fitqzp zp1 q1 then 
          [&& red_popqzp zp1 q1, red_popqzp zp2 q2 & red_popqzp zp3 q3]
        else red_qzt_leaf qtl'
      else red_qzt_leaf qtl'
    else red_qzt_leaf qtl'
  else false.

Lemma red_qzt_leaf_fit qtl :
    red_qzt_leaf qtl ->
 [/\ qzt_proper qtl
   & forall x : G,
       zpfit (qstepR x) zp1               -> zpvalid zp1 ->
       zpfit (qstepR (node x)) zp2        -> zpvalid zp2 ->
       zpfit (qstepR (node (node x))) zp3 -> zpvalid zp3 ->
    ~ ~~ qzt_fitl x qtl].
Proof.
move=> fit'qtl; split; first by case: qtl fit'qtl.
move=> x fit_zp1 zp1ok fit_zp2 zp2ok fit_zp3 zp3ok => /negP[].
elim: qtl fit'qtl => //= q1 q2 q3 qtl IHq; rewrite orbC.
case fit_x: (qzt_fitl x qtl) => //; rewrite (contraFF IHq) {fit_x}//.
case/and4P=> fit_q3 fit_q2 fit_q1 /and3P[red_q1 red_q2 red_q3].
apply/and3P; split.
- by have [<- //|zp1nt] := fitqzp_proper fit_q1; rewrite -fit_zp1 ?fitqzp_fit. 
- by have [<- //|zp2nt] := fitqzp_proper fit_q2; rewrite -fit_zp2 ?fitqzp_fit. 
- by have [<- //|zp3nt] := fitqzp_proper fit_q3; rewrite -fit_zp3 ?fitqzp_fit. 
Qed.

End RedQztLeaf.

Definition qzt_getr r qt :=
  if qt isn't QztNode qt5 qt6 qt7 qt8 then QztNil else
  match r with
  | Pr55 => qt5
  | Pr56 => qt6
  | Pr66 => qt6
  | Pr57 => qt7
  | Pr67 => qt7
  | Pr77 => qt7
  | Pr58 => qt8
  | Pr68 => qt8
  | Pr78 => qt8
  | Pr88 => qt8
  | _    => QztNil
  end.

Lemma qzt_getr_fit r qt1 :
   qzt_proper (qzt_getr r qt1) ->
 let qa := topqa r in
 [/\ fitqa r qa, qzt_get1 qa qt1 = qzt_getr r qt1 & qzt_proper qt1].
Proof. by case: qt1 => // qt5 qt6 qt7 qt8; case: r. Qed.

Lemma redpart_no_qzt_fitl (y : G) (qa1 qa2 qa3 : qarity) :
    arity y = qa1 -> arity (node y) = qa2 -> arity (node (node y)) = qa3 ->
  negb (qzt_fitl y (qzt_get3 qa1 qa2 qa3 qt)).
Proof.
move=> Dqa1 Dqa2 Dqa3; have:= fit'qt y.
by rewrite /qzt_fit /qzt_fita Dqa1 Dqa2 Dqa3 !qarity_of_qarity !eqxx.
Qed.

Fixpoint red_zpart_rec (zp : zpart) (d : nat) : bool :=
  if d isn't d'.+1 then false else
  let zp' := zshiftr Zhub zp in
  let: Zpart _ pl pr := zp in
  let s := get_spoke pr in
  let sqt := qzt_getr s (qzt_truncate qt) in
  if (if qzt_proper sqt then
        let: Zpart _ pl' pr' := zp' in
        let sl := get_spoke pl in
        if red_qzt_leaf (Zpart Zhubr pl' pr')
                        (zshiftl Zhubl zp)
                        (Zpart Zhat pl pr)
                        (qzt_getr s (qzt_getr sl (qzt_get1 ahub qt)))
          then red_popr_spoke pr && red_popl_spoke pl pr else
        if red_qzt_leaf (Zpart (zfanLt pr) pl' pr') zp
                        (Zpart (zfanRt pl) pl pr)
                        (qzt_getr (get_hat pr) (qzt_getr sl sqt))
          then
            [&& red_popr_hat pr, red_popl_spoke pl pr & red_popr_spoke pr]
          else
        let zpnil := Zpart Znil pl' pr' in
        match pr with
        | Pcons Pr55 h _ =>
          if red_qzt_leaf (Zpart Zhatr pl' pr')
                          (Zpart Zhatl pl pr) zpnil
                          (qzt_getr (get_hat pr') (qzt_getr h sqt))
            then red_popr_hat pr' && red_popr_hat pr else false
        | Pcons6 h f1 _ =>
          if red_qzt_leaf (Zpart Zfan0l pl' pr')
                          (Zpart Zhatl pl pr)
                          zpnil
                          (qzt_getr f1 (qzt_getr h sqt))
          then red_popl_fan1r pl' pr' && red_popr_hat pr else
          if red_qzt_leaf (Zpart Zhatr pl' pr')
                          (Zpart Zfan0r pl' pr')
                          zpnil
                          (qzt_getr (get_hat pr') (qzt_getr f1 sqt))
          then red_popr_hat pr' && red_popl_fan1r pl' pr' else false
        | Pcons7 h f1 f2 _ =>
          if red_qzt_leaf (Zpart Zfan1l pl' pr')
                          (Zpart Zhatl pl pr)
                          zpnil
                          (qzt_getr f1 (qzt_getr h sqt))
            then red_popl_fan1r pl' pr' && red_popr_hat pr else
          if red_qzt_leaf (Zpart Zfan0l pl' pr')
                          (Zpart Zfan0r pl' pr')
                          zpnil
                          (qzt_getr f2 (qzt_getr f1 sqt))
            then red_popl_fan2r pl' pr' && red_popl_fan1r pl' pr' else
          if red_qzt_leaf (Zpart Zhatr pl' pr')
                          (Zpart Zfan1r pl' pr')
                          zpnil
                          (qzt_getr (get_hat pr') (qzt_getr f2 sqt))
            then red_popr_hat pr' && red_popl_fan2r pl' pr' else false
        | Pcons8 h f1 f2 f3 _ =>
          if red_qzt_leaf (Zpart Zfan2l pl' pr')
                          (Zpart Zhatl pl pr)
                          zpnil
                          (qzt_getr f1 (qzt_getr h sqt))
            then red_popl_fan1r pl' pr' && red_popr_hat pr else
          if red_qzt_leaf (Zpart Zfan1l pl' pr')
                          (Zpart Zfan0r pl' pr')
                          zpnil
                          (qzt_getr f2 (qzt_getr f1 sqt))
            then red_popl_fan2r pl' pr' && red_popl_fan1r pl' pr' else
          if red_qzt_leaf (Zpart Zfan0l pl' pr')
                          (Zpart Zfan1r pl' pr')
                           zpnil
                          (qzt_getr f3 (qzt_getr f2 sqt))
            then red_popl_fan3r pl' pr' && red_popl_fan2r pl' pr' else
          if red_qzt_leaf (Zpart Zhatr pl' pr')
                          (Zpart Zfan2r pl' pr')
                          zpnil
                          (qzt_getr (get_hat pr') (qzt_getr f3 sqt))
            then red_popr_hat pr' && red_popl_fan3r pl' pr' else false
        | _ =>
          false
        end
    else false) then true
  else red_zpart_rec zp' d'.

Definition red_zpart := red_zpart_rec (Zpart Zhub p0ll p0lr) nhub.

Lemma not_red_zpart : ~~ red_zpart.
Proof.
have nt_p0l: 1 < size_part p0l.
  by rewrite 3?ltnW // Dp0l size_rev_part Ep0r -nFx0.
have nt_pl: 0 < size_part p0ll by rewrite size_drop_part subn_gt0.
have nt_pr: nhub < size_part p0lr.
  by rewrite size_cat_part Ep0r (leq_add2r _ 1); case: (p0l) nt_p0l.
have zp_ok := zvalid_initl.
rewrite /red_zpart.
elim: nhub p0ll p0lr => // d IHd pl pr in nt_pl nt_pr zp_ok *.
pose pl1 := shift_part pr pl; pose pr1 := drop_part 1 pr.
have nt_pl1: 0 < size_part pl1 by rewrite size_cat_part ltn_addl.
have nt_pr1: d < size_part pr1 by rewrite size_drop_part ltn_subRL.
pose zp zi := Zpart zi pl pr; pose zp1 zi := Zpart zi pl1 pr1.
pose x := zorg pl; pose y i := iter i face (edge x).
have Ezp zi: zdart (zp zi) = zmove zi x by [].
have Dzp1 zi zi1: zshiftr zi1 (zp zi) = zp1 zi1.
  by rewrite /zp zshiftr_eq //; apply: leq_trans nt_pr.
have Ezp1 zi: zdart (zp1 zi) = zmove zi (face x).
  by rewrite -(Dzp1 Zhub) zdart_shiftr.
have XEzp1 := Ezp1; rewrite /zp1 in XEzp1.
have Dx1 := Ezp1 Zhub; rewrite /= /zmove /= in Dx1.
have zp1ok: zpvalid (zp1 Zhub) by rewrite -(Dzp1 Zhub); apply: zpvalid_shiftr.
rewrite [Zpart]lock /= -lock Dzp1 /zp1 -!/(zp _) -!/(zp1 _).
rewrite negb_or IHd // andbT negb_and -implybE.
apply/implyP=> sqt_ok; have [Es Ds _] := qzt_getr_fit sqt_ok.
rewrite -{}Ds in sqt_ok *; rewrite qzt_get1_truncate {sqt_ok}//.
case: ifP => [/red_qzt_leaf_fit[] | _].
  case/qzt_getr_fit=> _ <- /qzt_getr_fit[Esl <- _] /(_ x)IHssl.
  apply/andP=> -[red_sp red_slp]; case: IHssl => // [_|_||]; rewrite /zpfit.
  - by rewrite Ezp1 /zmove Dnf.
  - exact: zdart_shiftl.
  - exact: zpvalid_shiftl.
  apply: redpart_no_qzt_fitl; first by rewrite arity_iter_face.
    by rewrite -(red_popl_spoke_fit zp_ok).
  by rewrite -(red_popr_spoke_fit zp_ok) // Dn2 arity_face.
case: ifP => [/red_qzt_leaf_fit[] | _].
  case/qzt_getr_fit=> Eh <- /qzt_getr_fit[Esl <- _] /(_ (y 2))IHhssl.
  apply/and3P=> -[red_hp red_slp red_sp]; case: IHhssl => //; rewrite /zpfit.
  - rewrite -(Dzp1 Zhatr) /y /= -Dn2; apply: (@zdart_stepRt (zp Zhatr)) => //.
    by rewrite /zpfit_top !(Dn2, arity_face) -(red_popr_spoke_fit zp_ok).
  - by rewrite /qstepR faceK edgeK.
  - rewrite Dnf -Dn2; apply: (@zdart_stepLt (zp Zhatl))=> //.
    by rewrite /zpfit_top -arity_face nodeK -(red_popl_spoke_fit zp_ok).
  apply: redpart_no_qzt_fitl.
  - by rewrite !arity_face -(red_popr_spoke_fit zp_ok).
  - by rewrite -arity_face Dnf -Dne De2 -(red_popl_spoke_fit zp_ok).
  by rewrite Dn2 arity_face -(red_popr_hat_fit zp_ok).
move: Es => /(red_popr_spoke_fit zp_ok)/(_ _)/eqP-/implyP; set s := topqa _.
case Dpr: pr @s => //= [[]//= h p|h f1 p|h f1 f2 p|h f1 f2 f3 p] Ds;
  have Es := Dfn Ds; rewrite -/x /= in Ds Es.
- case: ifP => // /red_qzt_leaf_fit[].
  case/qzt_getr_fit=> Ehr <- /qzt_getr_fit[Eh <- _] /(_ (y 3))IHhhr.
  apply/andP=> -[red_hr1 red_hr]; case: IHhhr => // [_|_|]; rewrite /zpfit.
  + by rewrite Ezp1 /qstepR /zmove Dnf {1}Es !Dnf -Dn2 Dnf.
  + by rewrite Ezp /qstepR /zmove Dnf De2 Dnf Dn2.
  apply: redpart_no_qzt_fitl; first by rewrite /= !arity_face (eqP Ds).
    by rewrite /= Dnf -(red_popr_hat_fit zp_ok) // Dpr.
  rewrite -(red_popr_hat_fit zp1ok) //= Dx1 Dn2 -Dnf -(canLR faceK Es).
  by rewrite !Dne !arity_face.
- case: ifP => [/red_qzt_leaf_fit[] | _].
    case/qzt_getr_fit=> Ef1 <- /qzt_getr_fit[Eh <- _] /(_ (y 3))IHhf1.
    apply/andP=> -[red_f1 red_h]; case: IHhf1 => // [_|_|]; rewrite /zpfit. 
    + by rewrite Ezp1 /qstepR /zmove De2 /= Dnf (canLR faceK Es) Dnf Dne.
    + by rewrite Ezp /qstepR /zmove faceK Dnf Dn2.
    apply: redpart_no_qzt_fitl; first by rewrite /= !arity_face -(eqP Ds).
      by rewrite /= Dnf -(red_popr_hat_fit zp_ok) // Dpr.
    rewrite -(red_popl_fan1r_fit zp1ok) // ?XEzp1 /pl1 ?Dpr //=.
    by rewrite /zmove Dn2 arity_face Dnf.
  case: ifP => // /red_qzt_leaf_fit[].
  case/qzt_getr_fit=> Ehr <- /qzt_getr_fit[Ef1 <- _] /(_ (y 4))IHf1hr.
  apply/andP=> -[red_hr red_f1]; case: IHf1hr => // [_|_|]; rewrite /zpfit. 
  + by rewrite Ezp1 /qstepR /zmove Dnf {1}Es Dnf -Dn2 Dnf.
  + by rewrite Ezp1 /qstepR /zmove Dnf faceK Dnf.
  apply: redpart_no_qzt_fitl => //=; first by rewrite /= !arity_face -(eqP Ds).
    by rewrite -(red_popl_fan1r_fit zp1ok) // ?XEzp1 /pl1 ?Dpr //= /zmove !Dnf.
  rewrite -(red_popr_hat_fit zp1ok) //= Dx1 Dn2 -Dnf -(canLR faceK Es).
  by rewrite !Dne !arity_face.
- case: ifP => [/red_qzt_leaf_fit[] | _].
    case/qzt_getr_fit=> Ef1 <- /qzt_getr_fit[Eh <- _] /(_ (y 3))IHhf1.
    apply/andP=> -[red_f1 red_h]; case: IHhf1 => // [_|_|]; rewrite /zpfit.
    + by rewrite Ezp1 /qstepR /zmove De2 /= Dnf [in LHS]Es !faceK Dnf Dne.
    + by rewrite Ezp /qstepR /zmove faceK Dnf Dn2.
    apply: redpart_no_qzt_fitl; first by rewrite /= !arity_face -(eqP Ds).
      by rewrite /= Dnf -(red_popr_hat_fit zp_ok) // Dpr.
    rewrite -(red_popl_fan1r_fit zp1ok) // ?XEzp1 /pl1 ?Dpr //=.
    by rewrite /zmove Dn2 arity_face Dnf.
  case: ifP => [/red_qzt_leaf_fit[] | _].
    case/qzt_getr_fit=> Ef2 <- /qzt_getr_fit[Hf1 <- _] /(_ (y 4))IHf1f2.
    apply/andP=> -[red_f2 red_f1]; case: IHf1f2 => // [_|_|]; rewrite /zpfit.
    + by rewrite Ezp1 /qstepR /= /zmove Dnf {1}Es /= !faceK -Dn2 Dnf.
    + by rewrite Ezp1 /qstepR /= /zmove Dnf faceK Dnf.
    apply: redpart_no_qzt_fitl => //=; first by rewrite !arity_face -(eqP Ds).
      by rewrite -(red_popl_fan1r_fit zp1ok) // ?XEzp1 /pl1 ?Dpr // /zmove !Dnf.
    rewrite -(red_popl_fan2r_fit zp1ok) // ?XEzp1 /pl1 ?Dpr //= /zmove Dn2 !Dnf.
    by rewrite arity_face.
  case: ifP => // /red_qzt_leaf_fit[].
  case/qzt_getr_fit=> Ehr <- /qzt_getr_fit[Ef2 <- _] /(_ (y 5))IHf2hr.
  apply/andP=> -[red_hr red_f2]; case: IHf2hr => // [_|_|]; rewrite /zpfit.
  + by rewrite Ezp1 /qstepR /= /zmove Dnf {1}Es Dnf -Dn2 Dnf.
  + by rewrite Ezp1 /qstepR /= /zmove Dnf faceK Dnf.
  apply: redpart_no_qzt_fitl => //=; first by rewrite !arity_face -(eqP Ds).
    by rewrite -(red_popl_fan2r_fit zp1ok) // ?XEzp1 /pl1 ?Dpr // /zmove !Dnf.
  rewrite -(red_popr_hat_fit zp1ok) //= Dx1 Dn2 -Dnf -(canLR faceK Es).
  by rewrite !Dne !arity_face.
case: ifP => [/red_qzt_leaf_fit[] | _].
  case/qzt_getr_fit=> Ef1 <- /qzt_getr_fit[Eh <- _] /(_ (y 3))IHhf1.
  apply/andP=> -[red_f1 red_h]; case: IHhf1 => // [_|_|]; rewrite /zpfit.
  + by rewrite Ezp1 /qstepR /zmove De2 /= Dnf {1}Es !faceK Dnf Dne.
  + by rewrite Ezp /qstepR /zmove faceK Dnf Dn2.
  apply: redpart_no_qzt_fitl; first by rewrite /= !arity_face -(eqP Ds).
    by rewrite /= Dnf -(red_popr_hat_fit zp_ok) // Dpr.
  rewrite -(red_popl_fan1r_fit zp1ok) // ?XEzp1 /pl1 ?Dpr //=.
  by rewrite /zmove Dn2 arity_face Dnf.
case: ifP => [/red_qzt_leaf_fit[] | _].
  case/qzt_getr_fit=> Ef2 <- /qzt_getr_fit[Ef1 <- _] /(_ (y 4))IHf1f2.
  apply/andP=> -[red_f2 red_f1]; case: IHf1f2 => // [_|_|]; rewrite /zpfit.
  + by rewrite Ezp1 /qstepR /zmove /= Dnf {1}Es !faceK -Dn2 Dnf.
  + by rewrite Ezp1 /qstepR /zmove /= Dnf faceK Dnf.
  apply: redpart_no_qzt_fitl => //=; first by rewrite !arity_face -(eqP Ds).
    by rewrite -(red_popl_fan1r_fit zp1ok) // ?XEzp1 /pl1 ?Dpr // /zmove !Dnf.
  rewrite -(red_popl_fan2r_fit zp1ok) // ?XEzp1 /pl1 ?Dpr // /zmove Dn2 !Dnf.
  by rewrite arity_face.
case: ifP => [/red_qzt_leaf_fit[] | _].
  case/qzt_getr_fit=> Ef3 <- /qzt_getr_fit[Ef2 <- _] /(_ (y 5))IHf2f3.
  apply/andP=> -[red_f3 red_f2]; case: IHf2f3 => // [_|_|]; rewrite /zpfit.
  + by rewrite Ezp1 /qstepR /zmove /= Dnf {1}Es !faceK -Dn2 Dnf.
  + by rewrite Ezp1 /qstepR /zmove /= Dnf faceK Dnf.
  apply: redpart_no_qzt_fitl => //=; first by rewrite !arity_face -(eqP Ds).
    by rewrite -(red_popl_fan2r_fit zp1ok) // ?XEzp1 /pl1 ?Dpr // /zmove !Dnf.
  rewrite -(red_popl_fan3r_fit zp1ok) // ?XEzp1 /pl1 ?Dpr // /zmove Dn2 !Dnf.
  by rewrite arity_face.
case: ifP => // /red_qzt_leaf_fit[].
case/qzt_getr_fit=> Ehr <- /qzt_getr_fit[Ef3 <- _] /(_ (y 6))IHf2hr.
apply/andP=> -[red_hr red_f2]; case: IHf2hr => // [_|_|]; rewrite /zpfit.
+ by rewrite Ezp1 [RHS]Dne -Dnf -Es -Dnf.
+ by rewrite Ezp1 /qstepR faceK -Dnf Dnf.
apply: redpart_no_qzt_fitl => //=; first by rewrite !arity_face -(eqP Ds).
  by rewrite -(red_popl_fan3r_fit zp1ok) // ?XEzp1 /pl1 ?Dpr // /zmove !Dnf.
rewrite -(red_popr_hat_fit zp1ok) //= Dx1 Dn2 -Dnf -(canLR faceK Es).
by rewrite !Dne !arity_face.
Qed.

End RedpartRec.

(* The nhub * 12 bound is mostly to keep Coq from unfolding the recursion too *)
(* soon. There's a logic to it, though : each time we recurse, we pop one     *)
(* prange, there are at most 4 open ranges per sector, and the worst case     *)
(* would require a configuration where all but one face is octogonal.         *)
Definition redpart p (nhub := size_part p) (ahub := qarity_of_nat nhub) :=
  let fix loop d p' :=
    if d is d'.+1 then red_zpart ahub (loop d') (rev_part p') p' else false in
  (nhub == ahub) && loop (nhub * 12) p.

Lemma no_fit_redpart p : redpart p -> forall x : G, ~~ exact_fitp x p.
Proof.
case/andP; move: (qarity_of_nat _) (_ * _) => ahub d /eqP-Ep red_p x.
apply: contraL red_p => fit_p; do [have [/eqP<- _] := andP fit_p] in Ep.
by elim: d => //= d /not_red_zpart-IHd in x p Ep fit_p *; apply: IHd Ep.
Qed.

End Redpart.
