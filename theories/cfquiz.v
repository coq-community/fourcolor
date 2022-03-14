(* (c) Copyright 2006-2015 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype path fingraph.
From fourcolor Require Import hypermap geometry color coloring patch cfmap quiz.

(******************************************************************************)
(* Compile the quiz that tests for the occurrence of a configuration. Since   *)
(* this requires to compute arities, we also check that the arity of ring     *)
(* regions are in the [3,6] range along the way. The procedure here is valid  *)
(* but not complete, e.g., it assumes that skews only occur at articulations. *)
(* The configuration data has been carefully knobbed to meet this constraint. *)
(*   The algorithm walks the map construction program backwards, keeeping     *)
(* track of kernel faces and of arities on the submap ring. During the        *)
(* traversal a list of questions is kept, that covers exactly the kernel      *)
(* faces that are disjoint from the current submap ring.                      *)
(*   Each of these question is rooted at (node (ic x)) for some dart x of the *)
(* submap ring, where ic is the injection from the current submap to the full *)
(* configuration map (crucially, this implies that "node" is computed in the  *)
(* full map). As the ring shrinks, questions are linked to form trees, until  *)
(* we arrive at the initial two-dart graph, where we have just two questions  *)
(* that form a proper quiz.                                                   *)
(*   H-type steps could be somewhat of a problem for this algorithm, but it   *)
(* turns out that (with a little fiddling) in all the programs we consider we *)
(* never need to join trees in an H step, so the code below doesn't handle    *)
(* that case (we'd need to generate more LL and RR questions).                *)
(*  Definitions:                                                              *)
(*    cpradius2 cp <=> the kernel of cpmap cp has radius at most 2.           *)
(*                     We test each for face as a possible hub.               *)
(*          noquiz == an invalid quiz (fails isQuizR).                        *)
(*       cfquiz cf == a valid quiz that tests for embedding of a copy of      *)
(*                    cfmap cf, or noquiz if cfprog cp is not a config_prog,  *)
(*                    has radius > 2, bad ring or kernel face arities, or     *)
(*                    encouters an unhandled case.                            *)
(*  --> We check dynamically that cfquiz cf returns a quiz stisfying isQuizr  *)
(* for each of the 633 configuration programs we use. We show here that this  *)
(* guarantess that cfquiz cf is valid for cfring cf at some dart in cfmap cf, *)
(* and that cfring cf embeddable with a kernel that has radius at most 2.     *)
(*  large_qarity a == the qarity value corresponding to a+2.                  *)
(*  small_qarity a == the qarity value corresponding to a+2 if a+2 \in [5,8], *)
(*                    and some DIFFERENT qarity greater than 8 otherwise.     *)
(* bad_small_arity qa <=> the qarity qa is greater than 8.                    *)
(* bad_ring_arity a <=> a+2 is not in the [3,6] range for ring face arities.  *)
(*   ring_question == record type for the question testing kernel faces from  *)
(*                    a dart on the perimeter ring of an intermediate stage   *)
(*                    of the map construction. It coerces to a question, but  *)
(*                    also to a nat that is the outer arity of the dart       *)
(*                    (number of adjacent faces NOT in the submap), and also  *)
(*                    contains a ring_question_is_kernel flag indicating      *)
(*                    whether the dart is in the kernel of the final map.     *)
(* cfquiz_rec qs cp == recursive configuration quiz generation, from a        *)
(*                    a sequence qs of ring_question's testing for the faces  *)
(*                    created by the start of its cfprog, and cp, the rest of *)
(*                    its cfprog (recall cp is executed first).               *)
(* rqs_Y rq1 rq3 qs q'1 == the ring_question sequence for a [YH] step,        *)
(*                    when the previous seq was [:: rq1, _, rq3 & qs], and    *)
(*                    q'1 is the new question for the first ring face.        *)
(* cfquiz_Y rq1 rq2 kqs == computes the ring question for the first ring face *)
(*                    of a Y step, given the first two ring questions, and    *)
(*                    passes it to kqs (which will be a partly applied rqs_Y) *)
(*                    or fails with nil.                                      *)
(* rqs_H rq1 rq3 qs q'1 q'2, cfquiz_H rq1 rq2 kqs == similar functions for H. *)
(*     rqs_fit h qs p <=> map h p fits the ring_question sequence qs: each    *)
(*                    (h x) in map h p fits the corresponding q in qs, and    *)
(*                    has arity (arity x + q).                                *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* We use a single sequence of records rather that three parallel sequences. *)
Record ring_question := RingQuestion {
  ring_question_is_kernel : bool;
  ring_question_outer_arity :> nat;
  ring_question_node_question :> question
}.

Section ConfigQuiz.

Local Notation isk := ring_question_is_kernel.

Local Notation rqseq := (seq ring_question).

(* We only compile questions for maps with kernel arities between 5 and 11;   *)
(* in fact only the most central face (the one to which the "true" dart of    *)
(* the central submap belongs) can have more that 8 sides. We check and use   *)
(* this fact during the compilation. We also check that the ring arities are  *)
(* in the 3..6 range; this property allows us to lift the preembedding        *)
(* constructed in quiz.v into an actual embedding (see embed.v).              *)
(* All the functions below work with the arities offset by two, because each  *)
(* time a face is detached from the submap, if had at least two neighbors in  *)
(* that submap.                                                               *)

Definition small_qarity a :=
  match a with
  | 3 => Qa5
  | 4 => Qa6
  | 5 => Qa7
  | 6 => Qa8
  | 7 => Qa10
  | _ => Qa9
  end.

Definition bad_small_arity qa :=
  match qa with
  | Qa9 => true
  | Qa10 => true
  | Qa11 => true
  | _ => false
  end.

Lemma small_qarityP a :
  let qa := small_qarity a in bad_small_arity qa = (qa != a.+2 :> nat).
Proof. by move: a; do 8!case=> //. Qed.

Definition large_qarity a :=
  match a with
  | 7 => Qa9
  | 8 => Qa10
  | 9 => Qa11
  | _ => small_qarity a
  end.

Definition bad_ring_arity a :=
  match a with 0 | _.+4.+1 => true | _ => false end.

Lemma not_bad_ring_arity (G : hypermap) (x : G) :
  bad_ring_arity (arity x).-2 = false -> good_ring_arity x.
Proof. by rewrite /good_ring_arity; move: (arity x); do 7!case=> //. Qed.

(* Error value. *)
Let noquiz := Quiz Qask0 Qask0.

(* The quiz construction proper.                                              *)

Definition rqs_Y rq1 rq3 (qs : rqseq) q1' : rqseq :=
  let: RingQuestion k1 a1 _ := rq1 in
  let: RingQuestion k3 a3 q3 := rq3 in
  [:: RingQuestion k1 a1.+1 q1', RingQuestion k3 a3.+1 q3 & qs].

Definition cfquiz_Y rq1 rq2 rqs' : rqseq :=
  let: RingQuestion _ _ q1 := rq1 in
  let: RingQuestion k2 a2 q2 := rq2 in
  if k2 then
    let qa2 := small_qarity a2 in
    if bad_small_arity qa2 then [::] else
    rqs' match q1, q2 with
        | Qask0, Qask0 => Qask1 qa2
        | Qask0, _ => QaskL qa2 q2
        | _, Qask0 => QaskR qa2 q1
        | _, _ => QaskLR qa2 q2 q1
        end
   else
    if bad_ring_arity a2 then [::] else
    match q1, q2 with
    | Qask0, Qask0 => rqs' Qask0
    | QaskR qa1 q1r, Qask0 => rqs' (QaskRR qa1 q1r)
    | Qask0, QaskL qa1 q1l => rqs' (QaskLL qa1 q1l)
    | _, _ => [::]
    end.

Definition rqs_H rq1 rq3 (qs : rqseq) q1' q2' : rqseq :=
  let: RingQuestion k1 a1 _ := rq1 in
  let: RingQuestion k3 a3 q3 := rq3 in
  [:: RingQuestion k1 a1.+1 q1', RingQuestion true 1 q2',
      RingQuestion k3 a3.+1 q3 & qs].

Definition cfquiz_H rq1 rq2 rqs' : rqseq :=
  let: RingQuestion k1 _ q1 := rq1 in
  let: RingQuestion k2 a2 q2 := rq2 in
  if k2 then
    let qa2 := small_qarity (S a2) in
    if bad_small_arity qa2 then [::] else
    match q1, q2, k1 with
    | Qask0, Qask0, true => rqs' (Qask1 qa2) q2
    | Qask0, Qask0, _ => rqs' q1 (Qask1 qa2)
    | Qask0, _, _ => rqs' q1 (QaskL qa2 q2)
    | _, Qask0, _ => rqs' (QaskR qa2 q1) q2
    | _, _, _ => [::]
    end
  else
    if bad_ring_arity a2.+1 then [::] else
    match q1, q2 with
    | Qask0, Qask0 => rqs' q1 q2
    | _, _ => [::]
    end.

Fixpoint cfquiz_rec (qs : rqseq) (cp : cprog) {struct cp} : quiz :=
  match cp, qs with
  | [::], [:: rq1, rq2 & _] =>
    let: RingQuestion k1 a1 q1 := rq1 in
    let: RingQuestion k2 a2 q2 := rq2 in
    if ~~ (k1 && k2) then noquiz else
    let qa1 := large_qarity a1.-1 in
    let qa2 := small_qarity a2.-1 in
    if (qa1 != a1.+1 :> nat) || bad_small_arity qa2 then noquiz else
    Quiz (QaskR qa1 q2) (QaskR qa2 q1)
  | s :: cp', [:: rq1, rq2, rq3 & qs'] =>
    match s with
    | CpR n => cfquiz_rec (rotr n qs) cp'
    | CpY => cfquiz_rec (cfquiz_Y rq1 rq2 (rqs_Y rq1 rq3 qs')) cp'
    | CpH => cfquiz_rec (cfquiz_H rq1 rq2 (rqs_H rq1 rq3 qs')) cp'
    | _ => noquiz
    end
  | _, _ =>
    noquiz
  end.

Section RqsWalk.

Variables (G0 G : pointed_map) (h : G -> G0).

Fixpoint rqs_fit (qs : rqseq) (p : seq G) {struct p} : bool :=
  match qs, p with
  | rqd :: qs', x :: p' =>
    let rq := rqd : ring_question in
    [&& arity (h x) == rq + arity x, fitq (node (h x)) rq & rqs_fit qs' p']
  | [::], [::] => true
  | _, _ => false
  end.

Lemma rqs_fit_cons (rq : ring_question) qs x p :
 rqs_fit (rq :: qs) (x :: p) =
   [&& arity (h x) == rq + arity x, fitq (node (h x)) rq & rqs_fit qs p].
Proof. by []. Qed.

Lemma rqs_fit_size qs p : rqs_fit qs p -> size qs = size p.
Proof.
by elim: qs p => [|rq qs IHrq] [|x p] //= /and3P[*]; congr _.+1; auto.
Qed.

Fixpoint rqs_walk (qs : rqseq) (p : seq G0) {struct p} : seq G0 :=
  match qs, p with
  | rqd :: qs', u :: p' =>
    let rq := rqd : ring_question in
    nseq (isk rq) u ++ walkq (node u) rq ++ rqs_walk qs' p'
  | _, _ => [::]
  end.

Lemma rqs_walk_cons (rq : ring_question) qs u p :
  rqs_walk (rq :: qs) (u :: p) =
    nseq (isk rq) u ++ walkq (node u) rq ++ rqs_walk qs p.
Proof. by []. Qed.

Definition rqs_proper (qs : rqseq) :=
  let r0 := cpring G0 in let r := cpring G in let hr := map h r in
  [/\ rqs_fit qs r,
      {subset [predD r0 & [predU codom h & fband hr]] <= good_ring_arity},
      simple (rqs_walk qs hr ++ r0)
    & fband (rqs_walk qs hr ++ r0) =i [predU [predC codom h] & fband hr]].

End RqsWalk.

(* We check separately the radius of the configuration (the initial face *)
(* of the quiz might not be at the center of the kernel).                *)

Fixpoint cpradius2 (cp : cprog) i :=
  if i isn't i'.+1 then false else
  let cm0 := cfmask1 cp i' in
  let: Cfmask mr1 _ := cm0 in
  let: Cfmask _ mk1 := cpadj cm0 cp in
  let: Cfmask _ mk2 := cpadj (Cfmask mr1 mk1) cp in
  if all id mk2 then true else cpradius2 cp i'.

Variable cf : config.

Let cp : cprog := cfprog cf.

Definition cfquiz : quiz :=
  if cpradius2 cp (cpksize cp) then
    cfquiz_rec (nseq (cprsize cp) (RingQuestion false 0 Qask0)) cp
  else noquiz.

Hypothesis qzR : isQuizR cfquiz.

Let cp_rad2 : cpradius2 cp (cpksize cp).
Proof. by move: qzR; rewrite /cfquiz; case (cpradius2 cp (cpksize cp)). Qed.

Let qs0_notR (cp1 : cprog) : isQuizR (cfquiz_rec [::] cp1) = false.
Proof. by elim: cp1 => //; case. Qed.

Let cp_ok : config_prog cp.
Proof.
have:= qzR; rewrite /cfquiz cp_rad2; set qs := nseq _ _.
have: size qs = cprsize cp by rewrite size_nseq.
have: size cp > 0 by case: cp cp_rad2.
elim: cp qs => // s cp1 IHcp [|rq1 [|rq2 [|rq3 qs]]] //= _.
case: s cp1 IHcp => //= [n||] [|s cp1] // IH Eqs qs_ok; apply: IH (qs_ok) => //.
- by rewrite -Eqs size_rotr.
- move: qs_ok; rewrite /cfquiz_Y -(succn_inj Eqs).
  case: rq1 rq2 rq3 => [k1 a1 q1] [[|] a2 q2] [k3 a3 q3].
    by case: ifP; first by rewrite qs0_notR.
  case: ifP => _; first by rewrite qs0_notR.
  by case: q1; rewrite ?qs0_notR //; case: q2; rewrite ?qs0_notR.
move: qs_ok; rewrite /cfquiz_H -Eqs.
case: rq1 rq2 rq3 => [k1 a1 q1] [[|] a2 q2] [k3 a3 q3].
case: ifP => _; first by rewrite qs0_notR.
  by case: q1; rewrite ?qs0_notR //; case: q2; rewrite ?qs0_notR //; case: k1.
case: ifP => _; first by rewrite qs0_notR.
by case: q1; rewrite ?qs0_notR //; case: q2; rewrite ?qs0_notR.
Qed.

Lemma cpradius2P : radius2 (kernel (cfring cf)).
Proof.
rewrite /cfring /cfmap -/cp.
elim: {-2}(cpksize cp) (leqnn (cpksize cp)) cp_rad2 => //= i IHi lt_cp_i.
move: (proper_cpmask1 cp i) (cpmask1 lt_cp_i cp_ok); set G := cpmap cp.
set cm0 := cfmask1 cp i; set x0 := nth _ _ i => cm0ok Dcm0.
case: (cpadj cm0 cp) (cpadj_proper cm0ok) (cpmask_adj cp_ok cm0ok) => mr1 mk1.
case/andP=> _ Emk1; rewrite {}Dcm0 => Ecm1 /=; set cm1 := Cfmask _ mk1.
have cm1ok: proper_cpmask cp cm1 by rewrite /= size_nseq eqxx.
move: (cpadj_proper cm1ok) (cpmask_adj cp_ok cm1ok).
case: (cpadj cm1 cp) => mr2 mk2 /andP[_ Emk2] Ecm2.
case: ifP => [mk2T _ {IHi} | _]; last by apply: IHi; apply: ltnW.
set kG := kernel _; have DkG: kG =i fband (cpker cp).
  move=> x; move: (cpmap_simple cp_ok) (cpmap_cover cp_ok x).
  rewrite simple_cat fband_cat -/G orbC => /and3P[_ UkG _].
  rewrite 2!inE /= fband_rev; case: (x \in _) / hasP => [[y kGy xFy]|_ /= ->//].
  by rewrite (closed_connect (fbandF _) xFy) (hasPn UkG).
have kGx0: x0 \in kG.
  by rewrite DkG (subsetP (ring_fband _)) ?mem_nth // size_cpker.
apply/radius2P; exists x0 => // x kGx; apply/(at_radius2P (kernelF _)).
have /hasP[y kGy /adjP[z xFz zRy]]: has (adj x) (cpmask cm1 cp).
  rewrite -Ecm2 /= fband_cat; apply/orP; right.
  suffices <-: cpker cp = mask mk2 (cpker cp) by rewrite -DkG.
  have /all_pred1P->: all (pred1 true) mk2 by apply: sub_all mk2T => [[]].
  by rewrite (eqP Emk2) -size_cpker // mask_true.
rewrite /= mask_false /= in kGy.
have: has (adj (edge z)) [:: x0].
  by rewrite -Ecm1 /= fband_cat; apply/orP; right; apply/hasP; exists y.
rewrite has_seq1 adjC; last by apply: cpmap_plain; apply: config_prog_cubic.
case/adjP=> t x0Ft tRz; exists t; exists z; split=> //; rewrite DkG.
by apply/hasP; exists y; [apply (mem_mask kGy) | rewrite (same_cface tRz)].
Qed.

Lemma cfquizP :
     {subset cpring (cpmap cp) <= good_ring_arity}
  /\ (exists x0, valid_quiz (cpring (cpmap cp)) x0 cfquiz).
Proof.
move: qzR; rewrite /cfquiz cp_rad2 -[cpmap cp]/(cpmap (catrev [::] cp)).
set qs := nseq (cprsize cp) _; set cp1 := [::]; set cp2 := cp.
have cp1ok: cubic_prog cp1 by [].
have cp2ok: nilp cp2 || config_prog cp2 by rewrite cp_ok orbT.
have: rqs_proper (@injcp cp1 cp2) qs.
  rewrite /cp2; set G := cpmap cp; set r := cpring G.
  have Dq0: rqs_walk qs r = [::].
    by rewrite /qs -size_ring_cpmap -/G -/r; elim: r.
  have im_d0: codom (@id G) =i G by move=> x; apply/imageP; exists x.
  split; rewrite //= ?map_id -/G -/r ?{}Dq0 /qs //=.
  - by rewrite -size_ring_cpmap -/G -/r; elim: r => //= *; rewrite eqxx.
  - by move=> x; rewrite !inE im_d0.
  - by move: (cpmap_simple cp_ok); rewrite -/G -/r simple_cat => /andP[].
  by move=> x; rewrite !inE im_d0.
elim: cp2 => [|s cp2 IHcp] in cp2ok (cp1) cp1ok (qs) * => [[] | rqs_ok qsR].
  set G := cpmap [::]; rewrite cpring0; set r := [:: ~~ _; _].
  set G0 := cpmap (catrev cp1 [::]); set r0 := cpring G0.
  set h := @injcp cp1 [::] => fit_r nFr Uq Eq.
  have hE: {morph h : x / edge x} by apply: edge_injcp.
  case Dqs: qs fit_r => [|[[] a1 q1] [|[[] a2 q2] qs2]] //= /and5P[].
  case: qs2 => // in Dqs *; rewrite !order_id !addn1 small_qarityP -negb_and.
  case: andP => // [[/eqP <-]]; case: a2 => // a2 in Dqs * => /eqP <-.
  set qa1 := large_qarity _; set qa2 := small_qarity a2; set qz := Quiz _ _.
  move=> /eqP Eqa1 fit_q1 /eqP Eqa2 fit_q2 _; split=> [u r0u |].
    apply: nFr; rewrite !inE r0u andbT orbC unfold_in -/G0 -/G.
    case rFu: (has (cface u) (map h r)).
      move: Uq; rewrite simple_cat => /and3P[_ /hasP[]].
      exists u; rewrite // Dqs /= !(fband_cons, fband_cat).
      by have [_ /mapP[[] _ ->] ->] := hasP rFu; rewrite ?orbT.
    apply/imageP => [] [x _ Du]; case/hasP: rFu; exists u => //.
    by rewrite {}Du map_f //; case: x. 
  have Eqz: fband (walkqz (h false) qz) =i fband (rqs_walk qs (map h r)).
    move=> u; rewrite /qz Dqs /= /qstepR -!hE.
    by rewrite !(fband_cons, fband_cat) orbF; do !bool_congr.
  exists (h false); do !split.
  - rewrite /fitqz /qz /= eqseq_cons fitq_cat /qstepR -!hE /= eqseq_cons.
    by rewrite Eqa1 Eqa2 !eqxx fit_q2.
  - rewrite (eq_simple Eqz).
      by move: Uq; rewrite simple_cat => /and3P[].
    by rewrite Dqs /= cats0 !size_cat /= !addnS addnC /qstepR -!hE.
  move=> u; rewrite Eqz; apply/idP/idP => [qFu | /negPf/= r0F'u].
    move: Uq; rewrite simple_cat => /and3P[_ Uq _].
    apply: contra Uq => /hasP[v r0v uFv]; apply/hasP; exists v => //=.
    by rewrite -(closed_connect (fbandF _) uFv).
  move: (Eq u); rewrite fband_cat r0F'u orbF !inE => ->.
  by case: imageP => // [[[] _ ->]]; rewrite (subsetP (ring_fband _)) ?map_f.
have scp2ok: config_prog (s :: cp2) by [].
have{cp2ok} [cp2ok]: nilp cp2 || config_prog cp2 /\ cubic_prog (s :: cp1).
  by case: (s) cp2ok qsR => //=; case: (cp2).
move/(IHcp cp2ok) => {}IHcp; rewrite /= in IHcp; move: IHcp rqs_ok qsR.
case Dqs: qs => [|rq1 [|rq2 [|rq3 qs3]]] //; rewrite -Dqs.
set G := cpmap cp2; set r := cpring G; set h := @injcp cp1 _.
have Ih: injective h by apply: injcp_inj.
have hE: {morph h : x / edge x} by apply: edge_injcp.
have hN: {in [predC cpring _], {morph h : x / node x}} := node_injcp cp1ok.
have{cp1ok} hF: {mono h : x y / cface x y} by apply: cface_injcp.
move: (cpmap (catrev cp1 _)) h Ih hE hN hF => G0; set r0 := cpring G0.
have{cp2ok} Ur: simple r.
  rewrite /r /G; case/orP: cp2ok => [/nilP->|cp_ok2].
    by rewrite cpring0 simple_cons fband_cons /= fconnect_id.
  by move: (cpmap_simple cp_ok2); rewrite simple_cat => /and3P[].
pose simq q q' (u : G0) := flatq q = flatq q' /\ walkq u q = walkq u q'.
pose selq q q' q'' : question := if q is Qask0 then q' else q''.
case: s scp2ok (config_prog_cubic scp2ok) => // [n||] cp2ok cp2Q;
  rewrite [cpmap _]/= -/G -/r => h Ih hE hN hF IHcp [].
- rewrite cpring_ecpR -/r -/r0 /= !map_rot; simpl in h; set hr := map h r.
  rewrite Dqs -Dqs => q_r nFr0 Uq Eq; apply: IHcp.
  pose r1 := take n r; pose r2 := drop n r.
  rewrite /rotr (rqs_fit_size q_r) size_rot -size_drop /= -/r2 /rot.
  set qs1 := drop _ qs; set qs2 := take _ qs.
  have{q_r}/andP[q_r1 q_r2]: rqs_fit [eta h] qs1 r1 && rqs_fit [eta h] qs2 r2.
    move: {Uq Eq qs3 Dqs}q_r; rewrite /rot -/r1 -/r2 {}/qs1 {}/qs2 andbC.
    elim: r2 qs => [|x r2 IHr2] [|rq qs]; rewrite // ?cats0 //=.
    by case/and3P=> -> -> /IHr2->.
  pose pq2 := rqs_walk qs2 (map h r2); pose m2 := size pq2.
  pose pq1 := rqs_walk qs1 (map h r1); pose qs12 := cat qs1 qs2.
  have Dpq: rqs_walk qs12 hr = rot m2 (rqs_walk qs (rot n hr)).
    transitivity (pq1 ++ pq2).
      rewrite /hr -(cat_take_drop n r) -/r1 -/r2 {}/qs12 {}/pq1.
      elim: r1 qs1 q_r1 => [|x r1 IHr1] [|rq qs1] //= => /and3P[_ _ /IHr1->].
      by rewrite !catA.
    rewrite -rot_size_cat {q_r1 qs12 qs3 Dqs Uq Eq}/m2; congr (rot _ _).
    move: q_r2; rewrite /hr -map_rot /rot {}/pq1 {}/pq2 {}/qs1 {}/qs2 -/r1 -/r2.
    by elim: r2 qs => [|x r2 IHr2] [|rq qs3] //= /and3P[*]; rewrite -IHr2 ?catA.
  have Ehr: map [eta h] r = hr by apply: eq_map.
  split; rewrite // -/r -/r0 ?Ehr -/qs12.
  + rewrite -(cat_take_drop n r) -/r1 -/r2 /qs12.
    elim: (r1) (qs1) q_r1 => [|x r1' IHr1] [|rq qs1'] //=.
    by case/and3P=> -> -> /IHr1.
  + move=> u nFu; apply: nFr0; congr (_ && _): nFu.
    by rewrite //= !inE fband_rot.
  + by rewrite Dpq {1}/rot -catA simple_catCA catA cat_take_drop.
  by move=> u; rewrite fband_cat Dpq fband_rot -fband_cat Eq inE /= fband_rot.
- rewrite /= in cp2Q; have ntG: proper_cpring G := cpmap_proper cp2Q.
  have plainG := cpmap_plain cp2Q; have plainG1 := plain_ecpY G plainG.
  rewrite -/r0; set rY := map h _; set pY := _ ++ r0.
  set u0 : ecpY G := ecpY G; set nu0 := node u0.
  have nu0FnG: cface nu0 (icpY G (node G)) by apply: cface_node_ecpY.
  pose h1 := h \o icpY G; pose rY1 := map h1 r.
  have ErY: fband rY =i fband (h u0 :: rY1).
    move=> u; rewrite /rY1 /r head_cpring /rY cpring_ecpY -/u0 -/nu0 /=.
    rewrite -map_comp !fband_cons orbCA; congr [|| _, _ | _].
    by apply: (same_connect_r cfaceC); rewrite hF.
  rewrite -/r; pose r1 := drop 2 r; pose au0 := [:: node G; G : G].
  have nFu0: arity u0 = 2 by apply: (@order_cycle _ _ (traject face u0 2)).
  have nFiG x: arity (icpY G x) = (x \in fband au0) + arity x.
    pose bu0 := map edge (orbit face u0).
    have Ebu0: fband bu0 =i fband (map (icpY G) au0).
      move=> u; rewrite /au0 -adj_ecpY // /bu0 unfold_in has_map.
      by apply: eq_has => v; apply: cfaceC.
    rewrite /order -(cardID (mem bu0)); congr (_ + _).
      rewrite predI_cface_simple.
        by rewrite Ebu0 unfold_in has_map (eq_has (cface_icpY _ _)).
      rewrite (eq_simple Ebu0); last by rewrite /bu0 !size_map size_orbit.
      rewrite (simple_map (cface_icpY G)).
      rewrite /r (head_proper_cpring ntG) (@simple_cat _ au0) in Ur.
      by case/andP: Ur.
    rewrite -(card_image (@icpY_inj _ G)); apply: eq_card => u.
    apply/andP/imageP=> [[bu0'u xFu] | [y xFy ->{u}]]; last first.
      by rewrite !inE cface_icpY /bu0 /orbit -/(arity u0) nFu0.
    have: ~~ cface u0 u by rewrite cfaceC -(same_cface xFu) cfaceC cface_ecpY.
    move: bu0'u; rewrite cface_ecpY -/u0 /bu0 /orbit -/(arity u0) nFu0 !inE.
    by case: u xFu => [] // [||y] //; rewrite !inE cface_icpY; exists y.
  rewrite Dqs => q_r nFr0 UpY EpY /=.
  move DcqY: (rqs_Y _ _ _) => cqY; move DqsY: (cfquiz_Y _ _ _) => qsY.
  case: rq1 rq2 rq3 => [k1 a1 q1] [k2 a2 q2] [k3 a3 q3] in DcqY DqsY Dqs q_r.
  move=> qsY_R; apply: IHcp => //.
  move: q_r; rewrite cpring_ecpY (head_proper_cpring ntG) map_cons -/u0 -/nu0.
  rewrite !rqs_fit_cons nFu0 (arity_cface nu0FnG).
  rewrite -hF in nu0FnG; rewrite (arity_cface nu0FnG) !nFiG !fband_cons /=.
  rewrite !connect0 orbT -/r -/r1 !add1n addn2 !addnS => /and5P[].
  set v1 := icpY G (node G) => Ea1 q1nG Ea2 q2nu0 /and3P[Ea3 q3iG q_r1].
  have{} q_r1: rqs_fit h1 qs3 r1.
    move Dea: (fun x => arity (icpY G x) == arity x) => ea.
    have ea_r1: all ea r1.
      apply/allP=> x r1x; rewrite -Dea nFiG [_ \in _]negbTE //.
      move: Ur; rewrite /r (head_proper_cpring ntG) (@simple_cat _ au0) -/r1.
      by case/and3P=> _ /hasPn->.
    elim: r1 (qs3) ea_r1 q_r1 {Dqs nFr0} => [|x r1 IHr1] [|rq qs4] //=.
    case/andP=> eax ea_r1 /and3P[Ea rq_nx qs4r]; rewrite -Dea /= in eax.
    by rewrite -(eqP eax) Ea rq_nx IHr1.
  have Uv1: v1 \notin cpring u0.
    rewrite cpring_ecpY !inE /= (mem_map (@icpY_inj _ _)).
    by have:= simple_uniq Ur; rewrite {1}[r]head_cpring => /andP[].
  have en_v1: edge (node (h v1)) = h nu0 by rewrite -(hN _ Uv1) -hE /= eqxx.
  have enn_v1: edge (node (node (h v1))) = h u0.
    by rewrite -!hN // -?hE ?cpring_ecpY /= ?inE ?eqxx //=; apply/mapP=> [][].
  have EpY1: fband pY =i [predU [predC codom h1] & fband rY1].
    have outY1F: fclosed face [predU [predC codom h1] & fband rY1].
      apply: (intro_closed cfaceC) => u _ /eqP<-; apply: contraLR => /norP[].
      rewrite !inE (fclosed1 (fbandF _) u) !negbK => /imageP[x _ Dfu] ry1F'fu.
      case: imageP => // [][]; exists (edge (node x)) => //.
      rewrite /h1 /= icpY_edge icpY_node; last first.
        apply: contra ry1F'fu => /= rY1u; rewrite (subsetP (ring_fband _)) //.
        by rewrite Dfu map_f // [r]head_proper_cpring // (mem_cat _ au0) rY1u.
      apply: faceI; rewrite hE hN ?nodeK // cpring_ecpY !inE /= -/r -behead_map.
      apply: contra ry1F'fu => /mem_behead r_x.
      by rewrite Dfu (subsetP (ring_fband _)) // /rY1 map_comp (map_f h).
    move=> u; rewrite EpY inE /= !inE ErY /=.
    have [[x _ ->] /= | ] := imageP; last first.
      by case: imageP => // [[x _ ->]] []; exists (icpY G x).
    have [[y xFy] | XFx] := fband_icpY (x : ecpY G).
      rewrite -hF in xFy; rewrite [_ || _](closed_connect outY1F xFy).
      rewrite (closed_connect (fbandF _) xFy) !inE fband_cons hF cfaceC.
      by rewrite cface_ecpY (codom_f h1).
    rewrite -hF in XFx; rewrite fband_cons cfaceC XFx; congr (_ || _).
    by apply/esym/(contraL _ XFx) => /imageP[z _ ->]; rewrite hF cface_ecpY.
  pose inY1 := [predU codom h1 & fband rY1].
  have nFr0_Y1: {subset [predD r0 & inY1] <= good_ring_arity}.
    move=> u /andP[/norP[/= h1'u rY1F'u] r0u].
    case u0Fu: (cface (h u0) u).
      rewrite unfold_in -(arity_cface u0Fu); apply: not_bad_ring_arity.
      move: UpY; rewrite (eqP Ea2) simple_cat andbA andbAC => /andP[_].
      apply: contraNF => a2bad; apply/hasP; exists u => //=.
      apply/hasP; exists (h u0); last by rewrite cfaceC.
      rewrite {}Dqs /rY cpring_ecpY -/u0 -/nu0 /= !mem_cat.
      case: k2 DqsY qsY_R => [_ _ | <- /=]; last by rewrite /= a2bad qs0_notR.
      by rewrite mem_head !orbT.
    apply: nFr0; have: u \in fband pY by rewrite EpY1 !inE h1'u.
    by rewrite EpY !inE ErY fband_cons cfaceC u0Fu (negPf rY1F'u) !orbF => ->.
  move: qsY_R; rewrite -[fun x => _]/h1 -{qsY}DqsY.
  case Dk2: k2 => /=.
    rewrite small_qarityP -{Ea2}(eqP Ea2) if_neg; set qa2 := small_qarity a2.
    case: ifP => [Ea2 _ | _]; last by rewrite qs0_notR.
    set q11 := QaskLR qa2 q2 q1.
    pose q12 := selq q1 (selq q2 (Qask1 qa2) (QaskL qa2 q2))
                        (selq q2 (QaskR qa2 q1) q11).
    change (rqs_proper h1 (cqY q12)).
    have [Eq1 Eq1v1]: simq q12 q11 (node (h v1)).
      by rewrite /q12 /q11 /simq; case q1; case q2 => //= *; rewrite !cats0.
    rewrite /= /qstepR /qstepL enn_v1 en_v1 in Eq1v1.
    have Eq12F: fband (rqs_walk (cqY q12) rY1 ++ r0) =i fband pY.
      rewrite /rY1 /pY /rY cpring_ecpY /r /behead head_proper_cpring // -/r.
      rewrite -/r1 !map_cons -DcqY -/u0 -/nu0 Dqs Dk2 /rqs_Y.
      rewrite !rqs_walk_cons {1 2}/h1 -/v1 -map_comp !catA => u.
      rewrite !fband_cat; do 4!congr (_ || _).
      rewrite (fband_nseq nu0FnG) -!orbA; congr (_ || _).
      rewrite Eq1v1 fband_cons fband_cat orbA orbC; do 2!congr (_ || _).
      by rewrite (cface1r (h u0)) -enn_v1 nodeK.
    split=> [|||u]; rewrite // -/r -/rY1 -/r0; last by rewrite Eq12F EpY1.
      rewrite /r head_proper_cpring // -/r -DcqY /= Ea1 Ea3 q3iG q_r1 !andbT.
      rewrite /h1 /= -/v1 /fitq Eq1 Eq1v1 /= eqseq_cons fitq_cat.
      by rewrite -arity_face -enn_v1 nodeK in Ea2; rewrite Ea2 q2nu0.
    rewrite (eq_simple Eq12F) // /rY1 /pY /rY cpring_ecpY.
    rewrite /r /behead head_proper_cpring // -/r -/r1 !map_cons.
    rewrite -DcqY -/u0 -/nu0 Dqs Dk2 /rqs_Y !rqs_walk_cons {1 2}/h1 -/v1.
    rewrite -map_comp !size_cat Eq1v1 /= !size_cat !addnA; do 4!congr (_ + _).
    by rewrite !size_nseq addn1 !addnS addnA addnAC.
  case: ifP => _; first by rewrite qs0_notR.
  case: (q1) Dqs q1nG q2nu0; rewrite ?qs0_notR //.
    do [case q2; rewrite ?qs0_notR //] => [Dqs _ _ _ | qa2l q2l Dqs _ q2nu0 _].
      have EqsF: fband (rqs_walk (cqY Qask0) rY1 ++ r0) =i fband pY.
        rewrite /rY1 /pY /rY cpring_ecpY /r /behead head_proper_cpring // -/r.
        rewrite -/r1 !map_cons -DcqY -/u0 -/nu0 Dqs Dk2 /rqs_Y.
        rewrite !rqs_walk_cons {1 2}/h1 -/v1 -map_comp !catA => u.
        rewrite !fband_cat !orbF; do 4!congr (_ || _).
        by rewrite (fband_nseq nu0FnG).
      split=> [|||u]; rewrite // -/r -/rY1 -/r0; last by rewrite EqsF EpY1.
        by rewrite /r head_proper_cpring // -/r -DcqY /=; apply/and4P.
      rewrite (eq_simple EqsF) // /rY1 /pY /rY cpring_ecpY.
      rewrite /r /behead head_proper_cpring // -/r -/r1 !map_cons.
      rewrite -DcqY -/u0 -/nu0 Dqs Dk2 /rqs_Y !rqs_walk_cons {1 2}/h1 /= -/v1.
      by rewrite -map_comp !size_cat /= !addnA !size_nseq.
    have EqsF: fband (rqs_walk (cqY (QaskLL qa2l q2l)) rY1 ++ r0) =i fband pY.
      rewrite /rY1 /pY /rY cpring_ecpY /r /behead head_proper_cpring // -/r.
      rewrite -/r1 !map_cons -DcqY -/u0 -/nu0 Dqs Dk2 /rqs_Y.
      rewrite !rqs_walk_cons {1 2}/h1 -/v1 -map_comp !catA => u.
      rewrite !fband_cat !orbF; do 4!congr (_ || _).
      rewrite (fband_nseq nu0FnG); congr (_ || _) => /=.
      by rewrite /qstepL enn_v1 fband_cons cface1r nodeK.
    split=> [|||u]; rewrite // -/r -/rY1 -/r0; last by rewrite EqsF EpY1.
      rewrite /r head_proper_cpring // -/r -DcqY /=; apply/and5P; split=> //.
      move: q2nu0; rewrite /fitq /= !eqseq_cons /h1 /= -/v1 /qstepL enn_v1.
      by rewrite -{1}[node (h u0)]nodeK arity_face.
    rewrite (eq_simple EqsF) // /rY1 /pY /rY cpring_ecpY.
    rewrite /r /behead head_proper_cpring // -/r -/r1 !map_cons.
    rewrite -DcqY -/u0 -/nu0 Dqs Dk2 /rqs_Y !rqs_walk_cons {1 2}/h1 -/v1.
    rewrite -map_comp !size_cat /= !addnA; do 4!congr (_ + _).
    by rewrite !size_nseq !addn0 /qstepL enn_v1.
  case q2; rewrite ?qs0_notR // => qa1r q1r Dqs q1nu0 _ _.
  have EqsF: fband (rqs_walk (cqY (QaskRR qa1r q1r)) rY1 ++ r0) =i fband pY.
    rewrite /rY1 /pY /rY cpring_ecpY /r /behead head_proper_cpring // -/r -/r1.
    rewrite !map_cons -DcqY -/u0 -/nu0 Dqs Dk2 /rqs_Y.
    rewrite !rqs_walk_cons {1 2}/h1 -/v1 -map_comp !catA => u.
    rewrite !fband_cat !orbF; do 4!congr (_ || _).
    by rewrite (fband_nseq nu0FnG); congr (_ || _); rewrite /= /qstepR en_v1.
  split=> [|||u]; rewrite // -/r -/rY1 -/r0; last by rewrite EqsF EpY1.
    rewrite /r head_proper_cpring // -/r -DcqY /=; apply/and5P; split=> //.
    by move: q1nu0; rewrite /fitq /= !eqseq_cons /qstepR en_v1.
  rewrite (eq_simple EqsF) // /rY1 /pY /rY cpring_ecpY.
  rewrite /r /behead head_proper_cpring // -/r -/r1 !map_cons.
  rewrite -DcqY -/u0 -/nu0 Dqs Dk2 /rqs_Y !rqs_walk_cons.
  rewrite -map_comp !size_cat /= !addnA; do 4!congr (_ + _).
  by rewrite !size_nseq !addn0 /qstepR en_v1.
rewrite /= in cp2Q cp2ok; have ntG: proper_cpring G := cpmap_proper cp2Q.
have longG: long_cpring G := cfmap_long cp2ok.
have plainG: plain G := cpmap_plain cp2Q; have plainG1 := plain_ecpH G plainG.
rewrite -/r0; set rH := map h (cpring (ecpH G)); set pH := cat _ r0.
set u0 : ecpH G := ecpH G; set nu0 := node u0.
pose v1 := icpH G (node G); pose v2 := icpH G G.
pose v3 := icpH G (face (edge G)).
have nu0Fv1: cface nu0 v1 by apply: cface_node_ecpH.
pose h1 := h \o icpH G; pose rH1 := map h1 r.
pose r1 := drop 3 r; pose au0 := [:: node G; G : G; face (edge G)].
have Dr: r = au0 ++ r1 by rewrite /r head_long_cpring.
have DrH: rH = [:: h nu0, h u0, h v3 & map h1 r1].
  by rewrite /rH cpring_ecpH // -/r -/u0 -/nu0 Dr /= -map_comp.
have DrH1: rH1 = [:: h v1, h v2, h v3 & map h1 r1] by rewrite /rH1 Dr.
have ErH: fband (h v2 :: rH) =i fband (h u0 :: rH1).
  move=> u; rewrite DrH DrH1 !fband_cons; bool_congr.
  rewrite orbCA; bool_congr; congr (_ || _).
  by rewrite !(cfaceC u); apply: same_cface; rewrite hF.
have nFu0: arity u0 = 3.
  have f3u0: face (face (face u0)) = u0 by rewrite /= nodeK (negPf ntG).
  apply: (@order_cycle _ _ (traject face u0 3)) => //.
  by rewrite (cycle_path u0) /= andbT [lhs in lhs == u0]f3u0.
have nFiG x: arity (icpH G x) = (x \in fband au0) + arity x.
  pose bu0 := map edge (orbit face u0).
  have Ebu0: fband bu0 =i fband (map (icpH G) au0).
    move=> u; rewrite -adj_ecpH // unfold_in has_map.
    by apply: eq_has => v; rewrite inE cfaceC.
  rewrite /order -(cardID (mem bu0)); congr (_ + _).
    rewrite predI_cface_simple.
      by rewrite Ebu0 unfold_in has_map (eq_has (cface_icpH _ _)).
    rewrite (eq_simple Ebu0); last by rewrite !size_map size_orbit.
    by move: Ur; rewrite (simple_map (cface_icpH G)) Dr simple_cat => /and3P[].
  rewrite -(card_image (@icpH_inj G G)); apply: eq_card => u.
  rewrite /bu0 /orbit nFu0 !inE andbC.
  apply/andP/imageP=> [[xFu]|[y xFy ->]]; last by  rewrite cface_icpH.
  have: ~~ cface u0 u by rewrite cfaceC -(same_cface xFu) cfaceC cface_ecpH.
  rewrite cface_ecpH //; case: u xFu => [||[||[||y]]] //; rewrite cface_icpH.
  by exists y.
rewrite Dqs => q_r nFr0 UpH EpH /=.
move DcqH: (rqs_H _ _ _) => cqH; move DqsH: (cfquiz_H _ _ _) => qsH.
case: rq1 rq2 rq3 => [k1 a1 q1] [k2 a2 q2] [k3 a3 q3] in DcqH DqsH q_r Dqs *.
move=> qsR; apply: IHcp => //.
rewrite cpring_ecpH -/u0 -/nu0 // -/r Dr !cat_cons /cat /drop in q_r.
rewrite map_cons -/v3 !rqs_fit_cons nFu0 (arity_cface nu0Fv1) in q_r.
rewrite -hF in nu0Fv1; rewrite (arity_cface nu0Fv1) in q_r.
rewrite !{1}nFiG /= !fband_cons !connect0 !orbT !addnS addn0 in q_r.
case/and5P: q_r => Ea1 q1nu0 Ea2 q2u0 /and3P[Ea3 q3v3 q_r1].
have{} q_r1: rqs_fit h1 qs3 r1.
  move Dea: (fun x => arity (icpH G x) == arity x) => ea.
  have: all ea r1.
    apply/allP=> x r1x; rewrite -Dea nFiG // [x \in _]negbTE //=.
    by move: Ur; rewrite Dr simple_cat => /and3P[_ /hasPn->].
  elim: (r1) (qs3) q_r1 => [|x r2 IHr2] [|rq qs4] //= /and3P[nFr2 -> q_r2].
  case/andP=> eax ear2; rewrite -Dea /= in eax.
  by rewrite -(eqP eax) nFr2 IHr2.
have UrH x: (icpH G x \in cpring u0) = (x \in drop 2 r).
  rewrite /u0 cpring_ecpH //= !inE (mem_map (@icpH_inj _ G)).
  by rewrite /long_cpring /= nodeK (negPf ntG).
have [Uv1 Uv2]: v1 \notin cpring u0 /\ v2 \notin cpring u0.
  have:= simple_uniq Ur.
  by rewrite {1}[r]head_proper_cpring // !UrH => /and3P[/norP[]].
have en_v1: edge (node (h v1)) = h nu0.
  rewrite -hN // -hE; congr (h _); apply: faceI; rewrite nodeK.
  by rewrite /nu0 /= /long_cpring /= nodeK (negPf ntG) /= nodeK (negPf ntG).
have nv1Fu0: cface (node (h v1)) (h u0).
  by rewrite -hN // hF cfaceC /u0 cface_ecpH //= !eqxx /= !inE eqxx !orbT.
have enn_v2: edge (node (node (h v2))) = h u0.
  have n_v2: node v2 = face u0 by rewrite /v2 /= (negPf ntG) /= 2!eqxx.
  rewrite -hN // n_v2 -hN; [by rewrite -hE faceK | rewrite cpring_ecpH //].
  rewrite !inE orFb; apply/norP; split; last by apply/mapP; case.
  by rewrite /= /long_cpring /= nodeK (negPf ntG).
have EpH1: fband (h v2 :: pH) =i [predU [predC codom h1] & fband rH1].
  have rH1F: fclosed face [predU [predC codom h1] & fband rH1].
    apply: (intro_closed cfaceC)=> u _ /eqP <-; apply: contraLR.
    rewrite !inE (fclosed1 (fbandF _) u) orbC => /norP[rH1F'fu].
    rewrite negb_or !negbK rH1F'fu andbT => /imageP[x _ Dfu]; apply/imageP.
    exists (edge (node x)) => //; rewrite /h1 /= icpH_edge icpH_node.
      rewrite hE hN; first by rewrite -[h _]Dfu faceK.
      rewrite !inE UrH; apply: contra rH1F'fu => /mem_drop r_x.
      by rewrite Dfu (subsetP (ring_fband _)) // map_f.
    apply: contra rH1F'fu => /= au0_x; rewrite Dfu (subsetP (ring_fband _)) //.
    by rewrite map_f // Dr mem_cat au0_x.
  move=> u; rewrite fband_cons EpH !inE orbCA -fband_cons ErH.
  have [[x _ ->] /= | ] := imageP; last first.
    by have [[x _ ->] [] | // ] := imageP; exists (icpH G x).
  have [[y xFy] | u0Fx] := fband_icpH x.
    rewrite -hF in xFy; rewrite [_ || _](closed_connect rH1F xFy) !inE.
    rewrite fband_cons (codom_f h1) (same_cface xFy) cfaceC hF cface_ecpH //=.
    by rewrite (closed_connect (fbandF _) xFy).
  rewrite fband_cons hF cfaceC u0Fx; case: imageP => // [[y _ /Ih Dx]] /=.
  by rewrite Dx cface_ecpH in u0Fx.
pose inH1 := [predU codom h1 & fband rH1].
have nFr0_H1: {subset [predD r0 & inH1] <= good_ring_arity}.
  move=> u => /andP[/norP[/= h1'u rH1F'u] r0u].
  case u0Fu: (cface (h u0) u).
    rewrite unfold_in -(arity_cface u0Fu); apply: not_bad_ring_arity.
    rewrite (eqP Ea2) [_.-2]/=; apply: contraTF UpH => /= a2bad.
    rewrite simple_cat andbCA; case: hasP => // [] []; exists u => //=.
    apply/hasP; exists (h u0); last by rewrite cfaceC.
    rewrite Dqs DrH !rqs_walk_cons !mem_cat orbC orbCA /=.
    by case: (k2) DqsH qsR => [_ _ | <-]; rewrite ?mem_head //= a2bad qs0_notR.
  apply: nFr0; rewrite !inE r0u andbT.
  have pH1Fu: u \in fband (h v2 :: pH) by rewrite EpH1 !inE h1'u.
  have{rH1F'u} rHF'u: u \notin fband (h v2 :: rH).
    by rewrite ErH fband_cons cfaceC u0Fu.
  rewrite fband_cons EpH !inE orbCA -fband_cons (negPf rHF'u) orbF in pH1Fu.
  by move: rHF'u; rewrite fband_cons !negb_or pH1Fu => /andP[].
have rHF'v2: h v2 \notin fband rH.
  rewrite DrH !fband_cons cfaceC (same_cface nu0Fv1) cfaceC !hF unfold_in.
  rewrite map_comp has_map (eq_has (hF v2)) orbCA cfaceC cface_ecpH // orFb.
  rewrite !cface_icpH has_map (eq_has (cface_icpH G G)).
  by move: Ur; rewrite Dr (simple_catCA [:: _] [:: _]) simple_cons => /andP[].
have pHF'v2: h v2 \notin fband pH by rewrite EpH !inE codom_f.
have Uv2pH: simple (h v2 :: pH) by rewrite simple_cons pHF'v2.
have nFv2: arity (h v2) = (arity G).+1.
  transitivity (arity v2); last by rewrite nFiG !fband_cons connect0 orbT.
  rewrite /order -(card_image Ih); apply: eq_card => u; rewrite inE.
  apply/idP/imageP => [v2Fu | [x v2Fx ->]]; last by rewrite hF.
  have:= pHF'v2; rewrite (closed_connect (fbandF pH) v2Fu) EpH !inE orbC.
  rewrite -(closed_connect (fbandF rH) v2Fu) (negPf rHF'v2) negbK.
  by case/imageP=> x _ Du; exists x => //; rewrite inE -hF -Du.
move: qsR; rewrite -DqsH; case Dk2: k2.
  rewrite /cfquiz_H small_qarityP -{Ea2}(eqP Ea2); set qa2 := small_qarity _.
  rewrite if_neg; case: ifP => [Eqa2 | _]; last by rewrite qs0_notR.
  set q11 := QaskR qa2 q1; set q21 := QaskL qa2 q2.
  have q11ok q:
    q2 = Qask0 -> simq q q11 (node (h v1)) -> rqs_proper h1 (cqH q q2).
  - move=> Dq2 [Eq Eqv1]; rewrite /= /qstepR en_v1 in Eqv1.
    have EqsF: fband (rqs_walk (cqH q q2) rH1 ++ r0) =i fband (h v2 :: pH).
      move=> u; rewrite /pH Dqs Dk2 DrH1 DrH -DcqH Dq2 /= Eqv1.
      rewrite !(fband_cat, fband_cons) !orbA; do 4!congr (_ || _).
      rewrite (fband_nseq nu0Fv1) -!orbA !(cfaceC u) (same_cface nv1Fu0).
      by do !bool_congr.
    split=> [|||u]; rewrite // -/r -/r0 -/rH1; last by rewrite EqsF EpH1.
      rewrite Dr -DcqH Dq2 /= Ea1 Ea3 q3v3 nFv2 eqxx q_r1 !andbT.
      by rewrite /fitq Eq Eqv1 /= eqseq_cons (arity_cface nv1Fu0) Eqa2.
    rewrite (eq_simple EqsF) // DrH1 /pH DrH Dqs Dq2 Dk2 -DcqH /=.
    rewrite !size_cat /= !size_cat !size_nseq Eqv1 /=.
    by nat_norm; do !nat_congr.
  have q21ok q:
    q1 = Qask0 -> simq q q21 (node (h v2)) -> rqs_proper h1 (cqH q1 q).
  - move=> Dq1 [Eq Eqv2]; rewrite /= /qstepL enn_v2 in Eqv2.
    have EqsF: fband (rqs_walk (cqH q1 q) rH1 ++ r0) =i fband (h v2 :: pH).
      move=> u; rewrite /pH Dqs Dk2 DrH1 DrH -DcqH Dq1 /= Eqv2.
      rewrite !(fband_cat, fband_cons) !orbA; do 5!congr (_ || _).
      rewrite (fband_nseq nu0Fv1) -!orbA orbCA; do 2!congr (_ || _).
      by rewrite (cface1r (h u0)) -enn_v2 nodeK.
    split=> [|||u]; rewrite // -/r -/r0 -/rH1; last by rewrite EqsF EpH1.
      rewrite Dr -DcqH Dq1 /= q3v3 Ea1 Ea3 nFv2 eqxx q_r1 !andbT.
      rewrite /fitq Eq Eqv2 /= eqseq_cons -[node (h v2)]nodeK enn_v2.
      by rewrite arity_face Eqa2.
    rewrite (eq_simple EqsF) // DrH1 /pH DrH Dqs Dq1 Dk2 -DcqH /=.
    rewrite !size_cat /= !size_cat !size_nseq Eqv2 /=.
    by nat_norm; do !nat_congr.
  have simq_id q (u : G0): simq q q u by [].
  case Dq1: q1 q11ok q21ok; case Dq2: q2; auto; rewrite ?qs0_notR //.
  by rewrite {}/q11 {}/q21 {}Dq1 {}Dq2; case k1 => [qok _|_ qok] _; apply: qok.
rewrite /cfquiz_H; case: ifP => _; first by rewrite qs0_notR.
case Dq1: q1; rewrite ?qs0_notR //; case Dq2: q2; rewrite ?qs0_notR //.
have EqsF: fband (rqs_walk (cqH Qask0 Qask0) rH1 ++ r0) =i fband (h v2 :: pH).
  move=> u; rewrite /pH Dqs Dk2 DrH1 DrH -DcqH Dq1 Dq2 /=.
  rewrite !(fband_cat, fband_cons) !orbA; do 4!congr (_ || _).
  by rewrite (fband_nseq nu0Fv1) orbC.
split=> [|||u]; rewrite // -/r -/r0 -/rH1; last by rewrite EqsF EpH1.
  by rewrite Dr -DcqH /= Ea1 Ea3 q3v3 nFv2 eqxx.
rewrite (eq_simple EqsF) // DrH1 /pH DrH Dqs Dq1 Dq2 Dk2 -DcqH /=.
by rewrite !size_cat /= !size_cat !size_nseq /=; nat_norm; do !nat_congr.
Qed.

Lemma embeddable_cfquiz : embeddable (cfring cf).
Proof.
split; try exact: cpradius2P; last first.
  by apply/allP=> x; rewrite mem_rev => r_x; case: cfquizP => /(_ x r_x).
have cpQ := config_prog_cubic cp_ok; do !split.
- exact: cpmap_plain.
- exact: cpmap_cubic.
- exact: ucycle_rev_cpring.
- exact: cpmap_connected.
- by move: (cpmap_simple cp_ok); rewrite simple_cat -simple_rev => /and3P[].
- exact: cpmap_planar.
exact: cpmap_bridgeless.
Qed.

Lemma valid_cfquiz : exists u, valid_quiz (cfring cf) u cfquiz.
Proof.
case: cfquizP => _ [u [qz_ok qz_u Uqz Eqz]]; exists u; split; auto => v.
by rewrite Eqz !inE -fband_rev.
Qed.

End ConfigQuiz.

Unset Implicit Arguments.
