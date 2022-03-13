(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype path fingraph bigop ssralg ssrnum ssrint.
From fourcolor Require Import hypermap geometry patch coloring birkhoff embed.
From fourcolor Require Import quiz quiztree part redpart discharge hubcap.
From fourcolor Require Import cfmap cfcontract cfreducible configurations.

(******************************************************************************)
(*   This file defines the properties and the specialized scripting language  *)
(* used to prove the seven 'presentation' lemmas (for hub sizes 5 to 11) in   *)
(* files presentN.v. This requires most the elements of graph theory that     *)
(* have been developped so far.                                               *)
(*   We implement Robertson et al.'s presentations directly as Coq scripts,   *)
(* using lemmas and bespoke tactic notation to handle concisely the four      *)
(* types of steps that make up presentations (split, symmetry, reducibility   *)
(* and hubcap), as well as general setup for a particular hub size            *)
(* (generating the quiz tree and the discharge rule fork).                    *)
(*   Definitions:                                                             *)
(*    reducibility <=> all configurations in the_configs are C-reducible.     *)
(*     valid_hub x <-> x is a dart of a minimal_counterexample G with         *)
(*                     positive dscore.                                       *)
(*  excluded_arity n <-> assuming reducibility, no valid_hub has arity n.     *)
(*    successful p <-> no valid_hub fits (exactly) part p.                    *)
(*  forced_part p0 p <-> any valid_hub that fits p0 must also fit p.          *)
(*  succeeds_in p0 p <-> forced_part p0 p implies successful p.               *)
(*   the_quiz_tree == fully evaluated quiz_tree for the_configs.              *)
(*  the_drule_fork n == drule fork for hub size n, precomputed for all n < 12 *)
(*                      (the_drule_fork n is the non-computed version).       *)
(* The presentation scripting language uses the notation for parts, part      *)
(* sublocations and hubcaps; this file exports the relevant XxSyntax modules. *)
(* It comprises the following notation:                                       *)
(*   Check <part>   ::= succeeds_in (Part <part>_0) (Part <part>);            *)
(*      in <part>_0     this is the general form of subgoals.                 *)
(*  Presentation red :: start a presentation proof; turns excluded_arity n in *)
(*                    red : reducibility                                      *)
(*                    ================================                        *)
(*                    Check $ * $ .. $ * $ (n times o)                        *)
(*                       in $ * $ .. $ * $                                    *)
(*    Reducibility :: close Check p in p0 by checking redpart p.              *)
(*  Hubcap <hubcap> :: close Check p in p0 by checking hubcap_cover <hubcap>  *)
(*                     and hubcap_fit p <hubcap>.                             *)
(*   <assumption> ::= <id>[<nat>] <= <nat> | <id>[<nat>] > <nat>              *)
(*                    where <id> is one of the sublocations s, h, or f[1-3].  *)
(*                    This denotes an arity assumption, e.g., s[2] <= 6       *)
(*                    stands for the assumption that the arity of the second  *)
(*                    spoke is less than 6, while s[2] > 6 denotes the        *)
(*                    complementary assumption.                               *)
(*  Pcase <id>: <assumption> :: split Check p   into two subgoals:            *)
(*  Pcase: <assumption>                  in p0                                *)
(*                                         <id> : sucessful p3                *)
(*                       ===========  and  ====================               *)
(*                       Check p1          Check p2                           *)
(*                          in p3             in p0                           *)
(*                    where p1, p2 are p with <assumtion> and its complement, *)
(*                    respectively, and p3 is p0 with <assumption>. If <id>   *)
(*                    is omitted then the context of the second subgoal is    *)
(*                    not extended.                                           *)
(* --> It is an invariant of presentation scripts that p0 is more general     *)
(* than p, and strictly so in the second subgoal of a Pcase. In the latter    *)
(* case p3 can be strictly more general than p1, hence the new second subgoal *)
(* assumption can be strictly stronger than 'successful p1'.                  *)
(*  Similar to <id>[<nat>] :: close Check p in p0 using <id> : sucessful p1   *)
(*  Similar to *<id>[<nat>]   by checking that p1 (or p1 reflected in the '*' *)
(*                            variant) and rotated by j implies p.            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition reducibility := reducible_in_range 0 (size the_configs) the_configs.

Definition valid_hub G x := minimal_counter_example G /\ (0 < @dscore G x)%R.

Definition excluded_arity n :=
  reducibility -> forall G x, @valid_hub G x -> (arity x == n) = false.

Definition successful p := forall G x, @valid_hub G x -> ~~ exact_fitp x p.

Definition forced_part p0 p :=
  forall G x, @valid_hub G x -> exact_fitp x p0 -> exact_fitp x p.

Definition succeeds_in p0 p := forced_part p0 p -> successful p.

(* Presentation. *)
Lemma exclude_arity n :
  (reducibility -> succeeds_in (pcons_ n) (pcons_ n)) -> excluded_arity n.
Proof.
move=> succ_p0_n red G x x_ok; have [cexG _] := x_ok.
by apply: contraTF (exact_fitp_pcons_ cexG x) => /eqP->; apply: succ_p0_n.
Qed.

Section Succeed.

(* Tactic parameters come first. *)

(* Parameters for Pcase and Similar. *)
Variables (i : subpart_loc) (j k : nat) (mir lo : bool).

(* Parameter for Hubcap. *)
Variable hc : hubcap.

(* Implicit parameter and explicit assumption for Similar. *)
Variable ps : part.
Hypothesis ps_ok : successful ps.

(* Implicit goal parameters. *)
Variable p0 p : part.

(* Pcase Ln_m: i[j] <= k. or Pcase Ln_m: i[j] > k. *)
Lemma succeed_by_split :
  let pl := split_part i j k lo p in
  let pr := split_part i j k (~~ lo) p in
  let p0l := if good_split i j k p0 then split_part i j k lo p0 else pl in
    good_split i j k p -> succeeds_in p0l pl ->
  (successful p0l -> succeeds_in p0 pr) -> succeeds_in p0 p.
Proof.
move=> pl pr p0l p_ijk pl_ok pr_ok p0p.
have fitp_split x (x_ok : valid_hub x) := fitp_split (proj1 x_ok) _ _ x.
have p0lpl: forced_part p0l pl.
  rewrite /p0l; case: ifP => [p0ijk | _] G x x_ok //.
  by rewrite !fitp_split // => /andP[-> /p0p->].
have {}pl_ok: successful pl by apply: pl_ok.
have{p0lpl}{}pr_ok: successful pr.
  apply: pr_ok => G x x_ok => [|p0x]; have:= pl_ok G x x_ok.
    exact/contra/p0lpl.
  by rewrite !fitp_split // p0p ?andbT ?addNb.
move=> G x x_ok; have []:= (pl_ok G x x_ok, pr_ok G x x_ok).
by rewrite !fitp_split // addNb; case: (_ (+) _).
Qed.

(* Similar to Ln_m[j]. or Similar to *Ln_m[j]. *)
Lemma succeed_by_similarity :
  let p1 := if mir then mirror_part p else p in
  let p2 := rot_part j p1 in
  size_part ps = size_part p2 /\ cmp_part p2 ps = Psubset -> succeeds_in p0 p.
Proof.
move=> p1 p2 [Eps2 eq_p2ps] _ G x x_ok; apply/negP => fit_p.
pose G1 := if mir then mirror G else G.
have [x1 x1ok Exp1]: exists2 x1 : G1, valid_hub x1 & exact_fitp x1 p1.
  have [cexG pos_x] := x_ok; rewrite /G1 /p1.
  case mir; last by exists x.
  exists x; last by rewrite -(fitp_mirror cexG) mirror_mirror_part.
  split; first exact: minimal_counter_example_mirror.
  by rewrite (dscore_mirror cexG).
suffices [x2 x2ok Exp2]: exists2 x2 : G1, valid_hub x2 & exact_fitp x2 p2.
  have [Ep2 fit_p2] := andP Exp2; case/negP: (ps_ok x2ok); rewrite /exact_fitp.
  by rewrite Eps2 Ep2 (fitp_cmp fit_p2 ps) eq_p2ps.
have [ltnj | lejn] := ltnP (size_part p1) j.
  exists x1 => //; rewrite /exact_fitp size_rot_part; congr (_ && _): Exp1.
  rewrite -[in LHS](cat_take_drop_part j p1) !fitp_cat andbC.
  set p3 := drop_part j p1; suffices: size_part p3 == 0 by case: p3.
  by rewrite size_drop_part subn_eq0 ltnW.
have [cexG1 fit_x1] := x1ok.
exists (iter j face x1); last by rewrite /p2 -fitp_rot.
by rewrite /valid_hub -(@dscore_cface _ x1) // fconnect_iter.
Qed.

(* Implicit assumption for Reducible and Similar. *)
Hypothesis red_check : reducibility.

Definition the_quiz_tree := Eval vm_compute in cfquiz_tree the_configs.

Let the_redpart := redpart the_quiz_tree.

Lemma no_fit_the_redpart G :
    minimal_counter_example G ->
  forall (x : G) p', the_redpart p' -> ~~ exact_fitp x p'.
Proof.
move=> cexG x p1 redp1; apply: (no_fit_redpart cexG) p1 redp1 x => x.
move Dq: the_quiz_tree => q.
have{q Dq} <-: cfquiz_tree the_configs = q by exact <: Dq.
have:= red_check; rewrite /reducibility; move Dcfs: the_configs => cfs red_cfs.
apply/negP; case/(qzt_fit_cfquiz cexG)=> [cf ltcf [qz fit_qz [cf_ok [u qz_u]]]].
wlog{x fit_qz} [x fit_qz]: G cexG / exists x : G, fitqz x qz.
  move=> IH; case: fit_qz; apply: IH; first exact: cexG.
  exact: minimal_counter_example_mirror.
have red_cf: cfreducible (nth cf000 cfs cf).
  by have:= red_check (leq0n cf); rewrite Dcfs => /(_ ltcf).
have embedG := quiz_preembedding cexG cf_ok qz_u fit_qz.
exact: not_embed_reducible cexG cf_ok embedG red_cf.
Qed.

(* Reducible. *)
Lemma succeed_by_reducibility : the_redpart p -> succeeds_in p0 p.
Proof. by move=> Hp _ G x [cexG nFx]; apply: no_fit_the_redpart. Qed.

(* Hubcap T[j1,j2]<=b1 ... [] *)

Definition the_drule_fork_template n : drule_fork n.
do 12![case: n => [|n]; first exact: DruleFork (DruleForkValues _)].
abstract exact: DruleFork (DruleForkValues _).
Defined.

Definition the_drule_fork := Eval vm_compute in the_drule_fork_template.

Lemma succeed_by_hubcap :
  let n := size_part p in
    hubcap_cover n hc && hubcap_fit the_redpart (the_drule_fork n) p hc ->
  succeeds_in p0 p.
Proof.
move=> n fit_hc _ G x [cexG pos_x].
exact: (hubcap_fit_bound cexG (no_fit_the_redpart cexG)) fit_hc.
Qed.

End Succeed.

Arguments succeed_by_split i j k lo {p0 p} _ _ _ _ {G x}.
Arguments succeed_by_similarity j mir {ps} ps_ok {p0 p} _ _ {G x}.
Arguments succeed_by_reducibility {p0 p} red_check _ _ {G x}.
Arguments succeed_by_hubcap hc {p0 p} red_check _ _ {G x}.

(* Tactic extensions for the presentations. *)

Export PartSyntax.

Arguments succeeds_in (p0 p)%part_scope.
Arguments successful p%part_scope.

Notation "'Check' p1 'in' p0" := (succeeds_in p0 p1)
  (at level 10, p1, p0 at level 9,
   format "'[v' 'Check'  p1 '/'    'in'  p0 ']'").

Tactic Notation "Presentation" ident(red) := apply: exclude_arity => /= red.

Ltac Reducible := by apply succeed_by_reducibility; last exact <: isT.

Export HubcapSyntax.

Ltac Hubcap hc := by apply (succeed_by_hubcap hc); last exact <: isT.

Tactic Notation "Similar" "to" "*" ident(lab) "[" constr(n) "]" :=
  apply (succeed_by_similarity n true lab); compute; do 2!split.
Tactic Notation "Similar" "to" ident(lab) "[" constr(n) "]" :=
  apply (succeed_by_similarity n false lab); compute; do 2!split.

Export SublocSyntax.

Tactic Notation
  "Pcase" ident(label) " : " constr(i) "[" constr(j) "]" "<=" constr(k) :=
  apply (succeed_by_split i j.-1 k true) => //= [|label].
Tactic Notation
  "Pcase" ident(label) " : " constr(i) "[" constr(j) "]" ">" constr(k) :=
  apply (succeed_by_split i j.-1 k false) => //= [|label].
Tactic Notation
  "Pcase" " : " constr(i) "[" constr(j) "]" "<=" constr(k) :=
  apply (succeed_by_split i j.-1 k true) => //= [|_].
Tactic Notation
  "Pcase" " : " constr(i) "[" constr(j) "]" ">" constr(k) :=
  apply (succeed_by_split i j.-1 k false) => //= [|_].
