(* (c) Copyright 2006-2015 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype path fingraph.
From mathcomp
Require Import bigop ssralg ssrnum ssrint.
From fourcolor
Require Import hypermap geometry part.

(******************************************************************************)
(* Discharging arities to neighbouring faces. We specify how to compute the   *)
(* discharge 'score' of a face, using the 32 rules given by Robertson et al.  *)
(* to move charges across edges, and prove that some face has a positive      *)
(* score (called 'charge' by Robertson et. al). Each rule specifies a score   *)
(* adjustment between neighbouring faces, and is represented here by one or   *)
(* two part objects:                                                          *)
(*  drule1, drule2, ..., drule32 == the part encodings of discharge rules.    *)
(*  base_drules == the list of all discharge rules, with multiplicity. This   *)
(*                 list has 38 items, as drule1 is duplicated (it transfers 2 *)
(*                 points), drule2 and drule3 are specialized by hub arity    *)
(*                 (we use exact_fitp), drule10 and drule31 are specialized   *)
(*                 according to symmetry, and drule3 is specialized to let    *)
(*                 the mirror_part operation return an exact result.          *)
(*   the_drules == the exact list of parts used to adjust the initial scores. *)
(*                 Each part fitting at a dart x tranfers one unit from the   *)
(*                 face of x to that of edge (face^2 x); the two-face shift   *)
(*                 facilitates the use of the converse_part operation.        *)
(*   symmetrize_drules rs == complete the drule sequence by adding all the    *)
(*                 symmetrics of non-symmetrical part, where th symmetry is   *)
(*                 reflection across the third spoke; used to get the_drules. *)
(*     dscore x == the discharge score of the face F of x: 10 * (6 - #|F|),   *)
(*                 plus the adjustments from the_drules.                      *)
(*    dscore1 x == the score transferred from the face of x to that of edge x *)
(*                 (the number of parts in the_drules that fit face^-2 x).    *)
(*    dscore2 x == the total adjustment across the (edge x, x) edge, i.e.,    *)
(*                 dscore1 (edge x) - dscore1 x.                              *)
(* Specialization of drules to a given hub arity, or to a given part.         *)
(* pick_source_drules n rs == the parts in rs with size n, that is, the rules *)
(*                 for taking score units from the hub face.                  *)
(* pick_target_drules n rs == the converse of parts in rs compatible with hub *)
(*                 size n; these are the drules for adding score units to the *)
(*                 hub face.                                                  *)
(*  drule_fork n == a record type for the specializations of the_drules to    *)
(*                 hub size n, with fields cource_drules and target_drules,   *)
(*                 and a witness of the drule_fork_values predicate family    *)
(*                 asserting that these are the result of the pick_..._drules *)
(*                 functions above applied to the_drules.                     *)
(*  sort_drules p rs == a record, of type sort_drules_result, with fields     *)
(*                 nb_forced_drules, the number of rules in rs implied by p   *)
(*                 (whose part representation contains p); and field          *)
(*                 straddling_drules, the rules in rs that ar neither implied *)
(*                 nor excluded by p.                                         *)
(* --> sort_drules is used to compute bounds on scores to prune the           *)
(* combinatorial enumeration of parts. The correctness lemmas for those       *)
(* bounds use the following auxiliary definitions:                            *)
(*  dbound1 rs x == the number of part sectors in rs that fit at x.           *)
(*  dbound2 tr sr x == the number of part sectors in tr that fit at x, minus  *)
(*                 the number of those in sr that fit at x.                   *)
(*    dboundK n == 10 * (6 - n).                                              *)
(*  sort_drules_spec x srs m <-> predicate family, stating: for some m0, rs   *)
(*                 srs = SortDrulesResult m0 rs and m = m0 + dbound1 rs x.    *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition drules := seq part.

Section DischargeRules.

Import PartSyntax.

Definition drule1 := Part $ * $ * $ 6+ $ * $ * $.

Definition drule2  := Part $ * $ 5 $ 7+ $ * $ * $.
Definition drule2' := Part $ * $ 5 $ 7+ $ * $ * $ * $.

Definition drule3  := Part $ 5 $ 6- $ 6+ $ * $ * $.
Definition drule3' := Part $ 5 $ 6- $ 6+ $ * $ * $ * $.

Definition drule4  := Part $ 6- $[5] 5 $ 6+ $ * $ * $ * $.
Definition drule4' := Part $ 6- $[5] 6 $ 6+ $ * $ * $ * $.

Definition drule5 := Part $ 6 $[6- 5] 6 $ 6+ $ * $ * $ * $.

Definition drule6 := Part $ 6 $[6-] 5 $[5] 7+ $ * $ * $ * $.

Definition drule7 := Part $ 6 $[6 6-] 6 $[5] 7+ $ * $ * $ * $.

Definition drule8 := Part $ 5 $ 6- $ 7+ $ * $ * $ * $ * $.

Definition drule9 := Part $ 6- $ 6- $ 7+ $ * $ * $ * $ 5 $.

Definition drule10  := Part $ 5 $ 5 $ 7+ $ 5 $ 6+ $ * $ * $.
Definition drule10' := Part $ 5 $ 5 $ 7+ $ 5 $ 5 $ * $ * $.

Definition drule11 := Part $ 6 $[5] 5 $ 7+ $ 5 $ 6+ $ * $ * $.

Definition drule12 := Part $ 5 $[5] 5 $ 7+ $ 5 $[5] 5 $ * $ * $.

Definition drule13 := Part $ 6 $[5] 5 $[5] 8+ $ 5 $ 5 $ * $ * $.

Definition drule14 := Part $ 5 $[5] 6 $ 7+ $ 5 $ * $ * $ * $.

Definition drule15 := Part $ 5 $ 6 $ 7+ $ 5 $ 7+ $ 5 $ 6 $.

Definition drule16 := Part $ 6 $ 6 $ 7+ $ 5 $ 5 $ 5 $ 6 $.

Definition drule17 := Part $ 5 $[6] 6 $ 7+ $ 5 $ 5 $ 7+ $ 5 $.

Definition drule18 := Part $ 6 $[5] 5 $[5] 7 $ 6+ $ * $ * $ 5 $.

Definition drule19 := Part $ 6 $ 6+ $ 8+ $[5] 5 $[5] 6 $ 5 $ 6 $.

Definition drule20 := Part $ 5 $ 6 $ 7+ $ 6 $ 6 $ 5 $ 5 $.

Definition drule21 := Part $ 6- $ 6 $[5] 7 $ 6+ $ * $ 5 $ 5 $.

Definition drule22 := Part $ 5 $ 6 $[5] 7 $ 6+ $ * $ 5 $ 6 $.

Definition drule23 := Part $ 5 $[5] 7 $ 7+ $ 5 $ * $ * $ * $.

Definition drule24 := Part $ 5 $ 5 $[5] 7 $ 7+ $ 6 $ 6 $ 5 $.

Definition drule25 := Part $ 5 $ 5 $ 7+ $[* * 5] 7 $[6] 5 $ 5 $ * $.

Definition drule26 := Part $ 6 $ 6 $[5] 7 $ 7+ $ 5 $ 5 $ 6 $.

Definition drule27 := Part $ 7+ $ 6 $[6 5 6+] 7 $ 7 $[5] 6- $ * $ * $.

Definition drule28 := Part $ 5 $ 5 $ 7+ $ 5 $ 5 $ * $ * $ 5 $.

Definition drule29 := Part $ 5 $[5] 5 $ 7+ $ 5 $ * $ * $ 5 $ 5 $.

Definition drule30 := Part $ 5 $ 5 $ 7+ $ 5 $[5] 6 $ 5 $ * $ * $.

Definition drule31  := Part $ 5 $[5] 5 $ 7+ $ 5 $[6+] 5 $ 6+ $ * $ 6+ $.
Definition drule31' := Part $ 5 $[5] 5 $ 7+ $ 5 $[5] 5 $ 6+ $ * $ 6+ $.

Definition drule32 := Part $ 5 $ 6 $[5] 7 $ 7+ $ 6 $ 5 $ 5 $ 5 $.

End DischargeRules.

Definition base_drules : drules := seqn _ 38
 drule1  drule1  drule2  drule2' drule3  drule3'  drule4  drule4' drule5
 drule6  drule7  drule8  drule9  drule10 drule10'
 drule11 drule12 drule13 drule14 drule15 drule16 drule17 drule18 drule19
 drule20 drule21 drule22 drule23 drule24 drule25 drule26 drule27 drule28 drule29
 drule30 drule31 drule31' drule32.

Fixpoint symmetrize_drules (r : drules) : drules :=
  if r is p :: r' then
    let p' := iter 5 (rot_part (size_part p).-1) (mirror_part p) in
    let psr := p :: symmetrize_drules r' in
    if cmp_part p p' is Psubset then psr else p' :: psr
  else r.

Definition the_drules := symmetrize_drules base_drules.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Discharge.

Variable G : hypermap.

Definition dscore1 (x : G) : int := count (exact_fitp (inv_face2 x)) the_drules.

Definition dscore2 x : int := dscore1 (edge x) - dscore1 x.

Definition dscore x : int :=
  60%:Z - (10 * arity x)%:Z + \sum_(y in cface x) dscore2 y.

Lemma dscore_cface x y : cface x y -> dscore x = dscore y.
Proof.
by move=> xFy; rewrite /dscore (arity_cface xFy) (eq_bigl _ _ (same_cface xFy)).
Qed.

End Discharge.

Prenex Implicits dscore dscore1 dscore2.

Section DischargePlanar.

Variable G : hypermap.

Hypothesis geoG : planar_plain_cubic_connected G.
Let De2 := plain_eq geoG.
Let Dn3 := cubic_eq geoG.

Lemma sumz_connect (I : finType) (e : rel I) (F : I -> int) :
  connect_sym e -> \sum_(x in roots e) \sum_(y in connect e x) F y = \sum_y F y.
Proof.
move=> sym_e.
rewrite [RHS](partition_big (root e) (roots e)) => /= [|y _]; last first.
  exact: roots_root.
apply: eq_bigr => x /eqP-Dx; apply: eq_bigl => y.
by apply/rootP/eqP; rewrite ?Dx.
Qed.

Lemma dscore_roots : \sum_(x in froots face) @dscore G x = 120.
Proof.
set F := froots face; pose ten : int := 10%:R; rewrite -[RHS]/(ten *+ 12).
transitivity (\sum_(x in F) (ten *+ 6 + \sum_(y in cface x) (dscore2 y - ten))).
  by apply: eq_bigr => x; rewrite sumrB addrA addrAC sumr_const -!mulrnA !natz.
rewrite big_split /= (sumz_connect _ cfaceC) !sumrB !sumr_const !addrA.
apply/eqP; rewrite subr_eq addrAC (reindex_inj edgeI) subrK -mulrnDr -!mulrnA.
have <-: fcard face G = #|F| by apply: eq_card => x; apply: andbT.
by rewrite eqr_nat eqn_mul2l addnC -cubic_Euler; apply: geoG.
Qed.

Lemma posz_dscore : exists x : G, dscore x > 0.
Proof.
apply/existsP; have: ~~ (0 <= - (120 : int)) by []; apply: contraR.
rewrite negb_exists -dscore_roots -sumrN => /forallP-score_le0.
by apply: sumr_ge0 => x _; rewrite oppr_ge0 lerNgt.
Qed.

Lemma dscore_mirror (x : G) : @dscore (mirror G) x = dscore x.
Proof.
rewrite /dscore arity_mirror (eq_bigl _ _ (cface_mirror x)); congr (_ + _).
suffices{x} score1F (x : G): @dscore1 (mirror G) (face x) = dscore1 x.
  rewrite (reindex_inj (@faceI G)) -(eq_bigl _ _ (fun y => cface1r y x)) /=.
  by apply: eq_bigr => y _; rewrite /dscore2 2!{1}score1F (plain_eq' geoG).
rewrite /dscore1 /the_drules; congr _%:Z.
elim: base_drules => [|p r IHp] //; pose n := size_part p.
pose rp i := iter i (rot_part n.-1) (mirror_part p).
have Erp i: size_part (rp i) = n.
  by elim: i => /= *; rewrite ?size_rot_part ?size_mirror_part.
have fit_rp i G1 x1:
  @exact_fitp G1 x1 (rp i) = exact_fitp (iter i face x1) (mirror_part p).
- elim: i {IHp} => //= i IHi in G1 x1 *.
  have [nFx1 | n'x1] := eqVneq (arity (face x1)) n.
    rewrite /= -{1}[x1](finv_f faceI) /finv nFx1 -fitp_rot ?Erp ?leq_pred //.
    by rewrite -iterS iterSr -IHi.
  rewrite /exact_fitp size_rot_part size_mirror_part Erp -/n.
  by rewrite !arity_face arity_iter_face in n'x1 *; rewrite (negPf n'x1).
move Dp1: (rp 5) => p1.
move: Dp1 {fit_rp}(fit_rp 5) {Erp}(Erp 5) => /= -> fit_p1 Ep1.
set x2' := inv_face2 x; pose x3 := face (face (face x)).
have Ex3: x3 = iter 5 face x2' by rewrite /x2' /inv_face2 /= !nodeK.
rewrite /= !(f_finv nodeI) in IHp Ex3 *.
case eq_pp1: (cmp_part p p1); rewrite //= {}IHp -/x2' -/x3;
 try by rewrite !fit_p1 // -Ex3 {1}Ex3 /= ?(finv_f faceI);
     rewrite -?(fitp_mirror geoG) mirror_mirror_part addnCA.
congr ((_ : bool) + _)%N; apply/idP/idP=> /andP[Exp fit_xp].
  have: @exact_fitp (mirror G) x3 p1.
    by rewrite /exact_fitp (fitp_cmp fit_xp) eq_pp1 /= andbT Ep1.
  rewrite fit_p1 Ex3 /= !(finv_f faceI).
  by rewrite -(fitp_mirror geoG) mirror_mirror_part.
rewrite -(fitp_mirror geoG) Ex3 -fit_p1.
by rewrite /exact_fitp (fitp_cmp fit_xp) eq_pp1 andbT Ep1.
Qed.

End DischargePlanar.

Section ScoreBound.

Variable nhub : nat. (* hub size *)

(* Rule selectors, by source or target arity, or by matching a part. The *)
(* "target arity" returns a list of converse rules. The "matching"       *)
(* selector returns a pair of the number of rules that are forced by the *)
(* part, plus the list of rules that straddle the part, discarding the   *)
(* rules that are disjoint from or forced by the part. The matching      *)
(* selector is part of the inner loop of the unavoidability computation. *)

Definition pick_source_drules : drules -> drules :=
  filter (fun p => size_part p == nhub).

Fixpoint pick_target_drules (r : drules) : drules :=
  if r is p :: r' then
    let: (u, p') := converse_part p in
    let tr := pick_target_drules r' in
    if u nhub then p' :: tr else tr
  else r.

Section SortDrules.

Record sort_drules_result := SortDrules {
  nb_forced_drules :> nat;
  straddling_drules :> drules
}.

Variable p : part.

Fixpoint sort_drules_rec n (rs r : drules) : sort_drules_result :=
  if r is p' :: r' then
    match cmp_part p p' with
    | Psubset => sort_drules_rec n.+1 rs r'
    | Pstraddle => sort_drules_rec n (p' :: rs) r'
    | Pdisjoint => sort_drules_rec n rs r'
    end
  else SortDrules n rs.

Definition sort_drules r := sort_drules_rec 0 [::] r.

End SortDrules.

(* A rule fork specializes the full set of discharge rules for a specific *)
(* hub size, so that the source/target arity selection is only performed  *)
(* once. We use a dependent predicate family to specify the computation.  *)

Inductive drule_fork_values : drules -> drules -> Prop :=
    DruleForkValues :
      drule_fork_values (pick_source_drules the_drules)
                        (pick_target_drules the_drules).

Record drule_fork := DruleFork {
   source_drules : drules;
   target_drules : drules;
   _ : drule_fork_values source_drules target_drules
}.

Variable rf : drule_fork.
Let rs : drules := source_drules rf.
Let rt : drules := target_drules rf.

Variable G : hypermap.
Hypothesis geoG : plain_cubic_pentagonal G.
Let pentaG : pentagonal G := geoG.
Let De2 := plain_eq geoG.
Let Dn3 := cubic_eq geoG.

Section BoundDart.

Definition dbound1 (r : drules) (x : G) := count (fitp x) r.

Definition dbound2 r r' x := (dbound1 r x)%:Z - (dbound1 r' x)%:Z.

Definition dboundK := if (nhub - 5)%N is n.+1 then - (n * 10)%:Z else 10%:Z.

Variables (x : G) ( (* hub *) p : part (* for sort_drules *)).
Hypotheses (nFx : arity x = nhub) (Ep : size_part p = nhub) (fit_xp : fitp x p).

Lemma dbound1_eq : dscore1 (face (face x)) = dbound1 rs x.
Proof.
congr _%:Z; rewrite /rs /source_drules; case: rf => _ _ [].
elim: the_drules => //= r dr ->.
by rewrite /exact_fitp /inv_face2 !faceK nFx eq_sym; case: ifP.
Qed.

Lemma sort_dbound1_eq ru:
  let rup := sort_drules p ru in dbound1 ru x = (rup + dbound1 rup x)%N.
Proof.
rewrite /= -[dbound1 _ _]addn0 -[0%N]/(0 + count (fitp x) [::])%N /sort_drules.
elim: ru 0%N [::] => //= r ru IHru m ru'.
rewrite (fitp_cmp fit_xp); case eq_pr: (cmp_part p r); rewrite //= -{}IHru.
  by rewrite -addnA 2!(addnCA (fitp x r)).
by rewrite addnS.
Qed.

Inductive sort_drules_spec (r : drules) : sort_drules_result -> nat -> Set :=
  SortDrulesSpec n r' : sort_drules_spec r (SortDrules n r') (n + dbound1 r' x).

Lemma sort_drulesP r : sort_drules_spec r (sort_drules p r) (dbound1 r x).
Proof. by rewrite sort_dbound1_eq; case: (sort_drules p r). Qed.

Lemma dbound2_leq : dscore2 (face (face x)) <= dbound2 rt rs x.
Proof.
rewrite /dbound2 -dbound1_eq ler_add2r lez_nat.
set y := inv_face2 _; rewrite /rt /target_drules; case: rf => _ _ [].
elim: the_drules => //= r dr IHdr; case Dr': (converse_part r) => [u r'].
case Hyr: (exact_fitp y r).
  move: (fitp_converse geoG Hyr); rewrite Dr' => /andP[].
  by rewrite {1 2}/y /inv_face2 !nodeK De2 !faceK nFx => -> /= ->.
by case: (u nhub) => //=; case: (fitp x r') => //; apply: ltnW.
Qed.

Lemma dboundK_eq : dboundK = 60%:Z - (10 * arity x)%:Z.
Proof.
rewrite -(subnKC (pentaG x)) nFx /dboundK; case: (nhub - 5)%N => // m.
by rewrite -addSnnS mulnDr PoszD opprD addNKr mulnC. 
Qed.

End BoundDart.

Lemma dscore_cap1 (m : nat) :
   (forall y : G, dscore1 y <= m) ->
  forall x : G, 0 < dscore x -> forall d, (59 < (10 - m) * d -> arity x < d)%N.
Proof.
move=> ub_m x pos_x d max_m; apply: contraLR pos_x; rewrite -leqNgt => ledx.
have ltm10: (m < 10)%N by rewrite -subn_gt0; case: (10 - m)%N max_m.
have{max_m}: 60%:Z <= ((10 - m) * arity x)%:Z.
  by rewrite lez_nat (leq_trans max_m) ?leq_mul.
rewrite -lerNgt -ler_subr_addr ler_subl_addl add0r => /ler_trans-> //.
rewrite !PoszM -!mulrzz -![_ *~ _]sumr_const -sumrB ler_sum // => y _.
rewrite -(ler_add2r m%:Z) -PoszD subnK 1?ltnW // addrAC.
by rewrite ler_subr_addr ler_add2l ler_subl_addr ler_paddr.
Qed.

Lemma source_drules_range : ~~ Pr58 nhub -> rs = [::].
Proof.
rewrite /rs /source_drules; case: rf => _ _ [] not_u58.
have Eu: (fun p => size_part p == nhub)
            =1 (fun n => ~~ Pr58 n && (n == nhub)) \o size_part.
- by move=> p; rewrite /= andbC; case: eqP => // ->.
by rewrite /pick_source_drules (eq_filter Eu).
Qed.

Lemma dscore_cap2 (x : G) :
    arity x = nhub -> 0 < dscore x ->
  0 < dboundK + \sum_(y in cface x) dbound2 rt rs y.
Proof.
move=> nFx /ltr_le_trans-> //; rewrite /dscore -dboundK_eq // ler_add2l.
do 2!rewrite (reindex_inj faceI) -(eq_bigl _ _ (fun y => cface1r y x)) /=.
by apply: ler_sum => y xFy; rewrite dbound2_leq // -(arity_cface xFy).
Qed.

End ScoreBound.
