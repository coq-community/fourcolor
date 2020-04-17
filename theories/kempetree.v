(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype path fingraph.
From fourcolor
Require Import hypermap geometry color chromogram coloring cfmap cfcolor.
From fourcolor
Require Import dyck ctree initctree gtree initgtree gtreerestrict ctreerestrict.

(******************************************************************************)
(*   Here we put all the reducibility steps together, to compute the Kempe    *)
(* closure tree of a configuration, which we can use to test directly for     *)
(* D-reducibility. A bit more work will be required for C-reducibility.       *)
(* Definitions:                                                               *)
(*  Kempe_tree cp == a ctree containing exactly the even ring trace colorings *)
(*                  in the Kempe co-closure of the ring traces induced by     *)
(*                  colorings of cfmap cp.                                    *)
(*  Kempe_tree_closure d ctu ctr gtu == computes the largest subset of the    *)
(*                  set of traces/chromograms represented by ctu/gtu, that is *)
(*                  disjoint from ctr : ctree; more precisely, returns a pair *)
(*                  of a ctree that is a subset of ctu : ctree, and a gtree   *)
(*                  pair that represents a partition of gtu : gtree. Here d   *)
(*                  is the heigth of the trees involved. Kempe_tree is        *)
(*                  computed by taking ctu/gtu to be the initial ctree/gtree, *)
(*                  and ctr to be cpcolor cp.                                 *)
(*  ktc_step ktc0 kr == inner loop closure functional for Kempe_tree_closure. *)
(*                  Improves an approximation kr of the result of             *)
(*                  Kempe_tree_closure by restricting the ctree part of kr by *)
(*                  the deleted chromograms in it gtree partition part, then  *)
(*                  calling an approximation ktc0 of Kempe_tree_closure with  *)
(*                  the resulting ctree, deleting the permutation closure of  *)
(*                  the colorings deleted by the ctree restriction.           *)
(* ktc_dostep2c ktc0 == improve an approximation ktc0 of Kempe_tree_closure   *)
(*                  by running ktc0, then running ktc_step ktc0 twice on its  *)
(*                  result. Kempe_tree_closure is obtained by running this d  *)
(*                  times on the simple approximation that justs restricts    *)
(*                  gtu by ctr: the improved approximation will do up to 3^d  *)
(*                  restriction cycles, which guarantees convergence.         *)
(* Kempe_valid h P ctu ctr gtu gtr <-> ctu, ctr : ctree and gtu, gtr : gtree  *)
(*                  is a valid intermediate Kempe_tree_closure state:         *)
(*                  the pairs are respectively partitions of subset of the    *)
(*                  initial (full) [cg]tree for ring size h+2, ctu contains   *)
(*                  exactly the even traces matching chromograms in the union *)
(*                  of gtu and gtr, with the correct multiplicities, and the  *)
(*                  removed colorings/chomograms in ctr/gtr are in the Kempe  *)
(*                  co-closure of the predicate P.                            *)
(*  ctree_size t == the number of different colorings stored in t : ctree.    *)
(* Kempe_complete P sz ctu ctr gtu gtr <-> ctu/ctr, gtu/gtr are a complete    *)
(*                  Kempe_tree_closure state, up to size sz: either ctu has   *)
(*                  size < sz, or both ctr and gtr are empty; any trace with  *)
(*                  a permutation not in ctu or whose completion satisfies P  *)
(*                  either has a Color2-3 permutation in ctr, or does not     *)
(*                  match any chromogram in gtu.                              *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Fixpoint ctree_size (t : ctree) : nat :=
  match t with
  | CtreeNode t1 t2 t3 => ctree_size t1 + (ctree_size t2 + ctree_size t3)
  | CtreeLeaf _ => 1
  | CtreeEmpty => 0
  end.

Lemma ctree_size_partition t t' t'' :
    ctree_partition t (CtreePair t' t'') ->
  ctree_size t = ctree_size t' + ctree_size t''.
Proof.
have Esz0 t0: (forall et, ctree_mem t0 et = false) -> ctree_size t0 = 0.
  elim: t0 => [t1 IHt1 t2 IHt2 t3 IHt3 /(_ (_ :: _))nomem | ? _ /(_ [::])|] //=.
  by rewrite (IHt1 (nomem Color1)) (IHt2 (nomem Color2)) (IHt3 (nomem Color3)).
rewrite /=; elim: t => [t1 IHt1 t2 IHt2 t3 IHt3|lf IHlf|] in t' t'' * => Pt.
- have:= Pt (_ :: _); case: t' {Pt}(Pt [::]) => // [t1' t2' t3'|].
    case: t'' => [t1'' t2'' t3''|lf|] //= _ Pte.
      rewrite /= (IHt1 _ _ (Pte Color1)) (IHt2 _ _ (Pte Color2)).
      by rewrite (IHt3 _ _ (Pte Color3)) -!addnA; do !nat_congr.
    rewrite /= (IHt1 _ CtreeEmpty (Pte Color1)).
    rewrite (IHt2 _ CtreeEmpty (Pte Color2)).
    by rewrite (IHt3 _ CtreeEmpty (Pte Color3)) /= !addn0.
  case: t'' => [t1'' t2'' t3''|lf|] // _ Pte.
    rewrite /= (IHt1 CtreeEmpty _ (Pte Color1)).
    rewrite (IHt2 CtreeEmpty _ (Pte Color2)).
    by rewrite (IHt3 CtreeEmpty _ (Pte Color3)).
  rewrite /= (IHt1 CtreeEmpty CtreeEmpty (Pte Color1)).
  rewrite (IHt2 CtreeEmpty CtreeEmpty (Pte Color2)).
  by rewrite (IHt3 CtreeEmpty CtreeEmpty (Pte Color3)).
- case Dt': t' Pt (Pt [::]) => [t1' t2' t3'|lf'|]; last by case: t''.
    case: t'' => // lf'' Pt _; rewrite -Dt' /= Dt' Esz0 // => et.
    by case: et (Pt et) => //= e et; rewrite orbF.
  by move=> Pt _; rewrite /= Esz0 // => et; case: et (Pt et).
by move: Pt => /(_ _)/norP/=/all_and2[]; do 2!move=> /(_ _)/negPf/=/Esz0->.
Qed.

Lemma ctree_size_proper h t :
  ctree_proper h t -> ctree_size t = 0 -> t = CtreeEmpty.
Proof.
elim: h t => [|h IHh] [] //= t1 t2 t3 [t_ne t1ok t2ok t3ok] szt_0.
by move/eqP: szt_0 t_ne; rewrite !addn_eq0 => /and3P[]; do 3?move/eqP/IHh->.
Qed.

Lemma ctree_max_size_proper h t : ctree_proper h t -> ctree_size t <= 3 ^ h.
Proof.
elim: h t => [|h IHh] [t1 t2 t3|lf|] //= [_ t1ok t2ok t3ok].
by rewrite expnS 2!mulSn mul1n !leq_add ?IHh.
Qed.

Section KempeTreeClosure.

Variable h : nat.

Let ktc_fun := ctree -> ctree -> gtree -> ctree * gtree_pair.

Definition ktc_step closure kr :=
  let: (ctu, gtp) := kr in
  if ctree_empty ctu then kr else
  let: GtreePair gtr gtu := gtp in
  if gtree_empty gtr then kr else
  if gtree_empty gtu then (CtreeEmpty, empty_gtree_pair) else
  let: CtreePair ctu' ctr :=
    ctree_restrict h ctu (CtrCons Bstack0 gtr CtrNil) in
  closure ctu' (ctree_rotlr ctr) gtu.

Definition ktc_step2c step (closure : ktc_fun) ctu ctr gtu :=
  step (step (closure ctu ctr gtu)).

Definition ktc_dostep2c closure := ktc_step2c (ktc_step closure) closure.

Fixpoint Kempe_tree_closure d : ktc_fun :=
  if d is d'.+1 then ktc_dostep2c (Kempe_tree_closure d') else
  fun ctu ctr gtu => (ctu, gtree_restrict gtu (GtrCons Bstack0 ctr GtrNil)).

Variable P : colseq -> Prop.

Local Notation sub_gt gt et := (gtree_sub gt Bstack0 et).
Local Notation even_fun et E := (fun et => if ~~ even_trace et then 0 else E).

Definition Kempe_valid ctu ctr gtr gtu :=
 [/\ ctree_proper h.+1 ctu
     /\ ctree_sub ctu =1 even_fun et (sub_gt gtr et + sub_gt gtu et),
     forall et, ctree_mem ctr et ->
       Kempe_coclosure P (ctrace et) /\ size et = h.+1,
     forall w, gtree_mem gtr w -> ~ gtree_mem gtu w /\ init_gtree_spec h.+1 w,
     forall w, gtree_mem gtu w -> init_gtree_spec h.+1 w
   & forall w, ~ gtree_mem gtu w -> init_gtree_spec h.+1 w ->
        exists2 et, Kempe_coclosure P (ctrace et) & matchpg Bstack0 et w].

Definition Kempe_complete sz ctu ctr gtr gtu :=
  [/\ ctree_size ctu < sz \/ ctr = CtreeEmpty /\ (forall w, ~ gtree_mem gtr w)
    & forall et, let norm_et e := permt (edge_rot e) (etrace et) in
        P (ctrace et) \/ (exists e, ~ ctree_mem ctu (norm_et e)) ->
      ctree_mem ctr (etrace et) \/ gtree_sub gtu Bstack0 et = 0].

Let ktr_prop ktr Q : Prop :=
  let: (ctu, GtreePair gtr gtu) := ktr in Q (ctu : ctree) CtreeEmpty gtr gtu.

Theorem Kempe_tree_closure_correct d ctu ctr gtu :
    let ktr0 Q := Q ctu ctr GtreeEmpty gtu in
    let ktrp := ktr_prop (Kempe_tree_closure d ctu ctr gtu) in
    ktr0 Kempe_valid ->
 [/\ ktrp Kempe_valid
   & forall sz, ktr0 (Kempe_complete (3 ^ d + sz)) ->
     ktrp (Kempe_complete sz.+1)].
Proof.
elim: d => [|d IHd] /= in ctu ctr gtu *.
  move Dctrr: (GtrCons _ ctr _) => ctrr [[ctu_ok Dctu] Dctr Dgtr Dgtu closedP].
  move: (gtree_restrict_partition gtu ctrr) (gtree_mem0_restrict gtu ctrr).
  case: (gtree_restrict gtu ctrr) => gtr gtu' /= Pgt Pgtr.
  split=> [|sz [ctu_lt_sz ctr_closed]].
    split=> // [|w gt_w | w gt_w | w gt'w Dw]; first split=> // et.
    - by rewrite Dctu gtree_sub_empty -(match_count_partition Pgt).
    - move: gt_w (Pgtr w) (Pgt w) => -> /esym/andP[gt_w _] /idP.
      by rewrite gt_w; split=> //; apply: Dgtu.
    - by apply: Dgtu; apply: contraFT (Pgt w) => /negPf->; rewrite gt_w orbT.
    case: (@idP (gtree_mem gtu w)) (Pgt w) => [_ | ? _]; last exact: closedP.
    rewrite Pgtr andbC; case gt_w: (gtr_mem _ w) => [] => [_ | /negbFE//].
    by move: gt_w; rewrite -Dctrr /= orbF => /has_matchP[et /Dctr[]]; exists et.
  split=> [|et /= Pet].
    case: ctu_lt_sz => [|[{Dctr}Dctr _]]; [by left | right; split=> // w].
    by rewrite Pgtr -Dctrr Dctr /= andbC; case: has_matchP => // [] [].
  right; apply/eqP/match_countP=> [[w gt_w wMet]]; case/negP: (Pgt w).
  rewrite gt_w; case gtu_w: (gtree_mem gtu w); last by rewrite orbT.
  case/ctr_closed: Pet => [ct_et | /eqP/match_countP[]]; last by exists w.
  rewrite /eqb addbT negbK Pgtr gtu_w -Dctrr /= orbF.
  by apply/has_matchP; exists (etrace et); rewrite ?matchpg_etrace.
move: (Kempe_tree_closure d) IHd ctu ctr gtu => ktc' IHktc'.
suffices IHstep ktr:
    let ktrp := ktr_prop ktr in let ktrp' := ktr_prop (ktc_step ktc' ktr) in
    ktrp Kempe_valid ->
  [/\ ktrp' Kempe_valid
    & forall sz, ktrp (Kempe_complete (3 ^ d + sz.+1)) ->
      ktrp' (Kempe_complete sz.+1)].
- move=> ctu ctr gtu /IHktc'[/IHstep[/IHstep[valid full3] full2] full1].
  split=> // sz; rewrite expnS -!addnA => /full1.
  by rewrite -addnS => /full2; rewrite -addnS => /full3.
move Dktr': (ktc_step _ ktr) => ktr'; case: ktr => ctu [gtr gtu] /= in Dktr' *.
case=> [[ctu_ok Dctu] _ Dgtr Dgtu closedP].
case: ifP Dktr' => [/ctree_empty_eq ctu0 <- //= | _].
  by split=> // sz [_ ctr_closed]; split=> //; left; rewrite ctu0. 
case: gtree_emptyP => [gtr0 <- //= | _].
  split=> // sz [_ ctr_closed]; split=> //; right; split=> // w.
  by rewrite gtr0 gtree_mem_empty.
case gtree_emptyP => [gtu0 | _] <- {ktr'}/=.
  split; last by split; [left | right; rewrite gtree_sub_empty].
  split=> //; do [by case | by rewrite -gtu0 | split=> // et].
  by rewrite gtree_sub_empty if_same.
have{ctu_ok}:= ctree_restrict_correct (CtrCons Bstack0 gtr CtrNil) ctu_ok.
case: (ctree_restrict _ _ _) => ctu' ctr /= [ct_ok Pctu Dctu'].
have{ct_ok} [/= ctr_ok ctu'_ok] := (ct_ok true, ct_ok false). 
suffices{IHktc'} [gt_valid gt_full]:
  [/\ Kempe_valid ctu' (ctree_rotlr ctr) GtreeEmpty gtu
    & forall sz, Kempe_complete sz.+1 ctu CtreeEmpty gtr gtu ->
      Kempe_complete sz ctu' (ctree_rotlr ctr) GtreeEmpty gtu].
- by case/IHktc': gt_valid; split=> // sz; rewrite addnS => /gt_full; move: sz.
have{Dctu'} Dctu': ctree_sub ctu' =1 even_fun et (sub_gt gtu et).
  by move=> et; rewrite Dctu' Dctu addn0; case: ifP; rewrite ?addKn.
split=> [|sz [ctu_lt_sz ctr_closed]].
  split=> // [|et0 ct_et0 | [] //].
    by split=> // et; rewrite gtree_sub_empty Dctu'.
  have{ct_et0} [g ct_et]: exists g, ctree_mem ctr (permt g et0).
    move: ct_et0; rewrite (ctree_mem_rotlr _ ctr_ok).
    by case/orP; [exists Eperm312 | exists Eperm231].
  set et := permt g et0 in ct_et.
  have{ct_et}[gtr_et gtu'et]: sub_gt gtr et != 0 /\ sub_gt gtu et == 0.
    case: ifP (Pctu et); rewrite ct_et ?orbT // -eqE eqb_id /ctree_mem.
    by rewrite Dctu Dctu' addnC; case: ifP => //; case: (sub_gt gtu et).
  have{gtr_et} sz_et: size et == h.+1.
    by case/match_countP: gtr_et => w /Dgtr[_ /andP[sz_w _]] /matchpg_size <-.
  split=> [P1 closedP1 P1et0|]; last by rewrite -(eqP sz_et) size_map.
  have{P1et0}-/closedP1[_ [w etMw wP1]]: P1 (ctrace et).
    by rewrite ctrace_permt; case/closedP1: P1et0.
  have w_bal: gram_balanced 0 false w.
    by have [_] := matchg_balanced etMw; rewrite sumt_ctrace.
  have Dw := matchg_cgram etMw; move: (take _ _) => w1 in Dw.
  have{etMw} etMw1: matchpg Bstack0 et w1 by rewrite -matchg_pg -Dw.
  have [gt_w1||et1 closedPet1 et1Mw1] := closedP w1.
  - by case/match_countP: gtu'et; exists w1.
  - by rewrite /init_gtree_spec (matchpg_size etMw1) sz_et -Dw.
  by apply: closedPet1 => //; apply: wP1; rewrite Dw matchg_pg -?Dw.
split=> [|et /=].
  have{ctu_lt_sz} [| [_ gtr0]] := ctu_lt_sz.
    rewrite (ctree_size_partition Pctu) addnC -ltn_subRL.
    case ctr0: (ctree_size ctr) => [|m]; last first.
      by move/leq_trans->; [left | rewrite subSS leq_subr].
    by right; split=> [|[]] //; rewrite (ctree_size_proper ctr_ok ctr0).
  right; split => [|[]] //; rewrite (_ : ctr = CtreeEmpty) //.
  apply/(ctree_size_proper ctr_ok)/(@addnI (ctree_size ctu')).
  rewrite -(ctree_size_partition Pctu).
  rewrite (@ctree_size_partition ctu ctu' CtreeEmpty) // => et.
  case: ifP (Pctu et) => [|_ /norP[/negPf->] //].
  rewrite /ctree_mem Dctu Dctu'; case: ifP => // _.
  by rewrite /gtree_sub match_count_0 => [-> // | w]; apply/negP.
case=> [Pet | [e]]; first by case: (ctr_closed et) => //; [left | right].
set et1 := permt _ _ => /negP ctu'et1.
case ctu'et: (ctree_mem ctu' (etrace et)); last first.
  right; apply: contraFeq ctu'et => /match_countP[w gt_w etMw].
  rewrite /ctree_mem Dctu' even_etrace; apply/match_countP.
  by exists w; rewrite ?matchpg_etrace.
case ctu_et1: (ctree_mem ctu et1); last first.
  by case: (ctr_closed et) => //; right=> //; exists e; rewrite ctu_et1.
left; case: ifP (Pctu (etrace et)); rewrite ctu'et // /eqb /= => _ ctr_et.
have:= Pctu et1; rewrite ctu_et1 (negPf ctu'et1) => /negbFE.
rewrite (ctree_mem_rotlr _ ctr_ok) /= /et1 /edge_rot.
by case: (e) ctr_et; by [rewrite permt_id => -> | move=> _ ->; rewrite ?orbT].
Qed.

Lemma Kempe_validP ctu ctr gtr gtu :
    Kempe_valid ctu ctr gtr gtu -> forall et, size et = h.+1 ->
    ~~ ctree_mem ctu (etrace et) ->
  Kempe_coclosure P (ctrace et).
Proof.
move=> [[_ Dctu] _ _ _ closedP] et0 sz_et0 ct'et0.
pose et := ctrace (etrace et0) => P1 closedP1 P1et0.
have{P1et0} P1et: P1 et by rewrite [et]ctrace_permt; case/closedP1: P1et0.
have [_ [w0 etMw0 w0P1]] := closedP1 _ P1et.
move: (take _ w0) (matchg_cgram etMw0) => w Dw0.
have w0bal: gram_balanced 0 false w0.
  by have [_] := matchg_balanced etMw0; rewrite sumt_ctrace.
have{etMw0} et0Mw: matchpg Bstack0 (etrace et0) w by rewrite -matchg_pg -Dw0.
have [gt_w||et1 closedPet1 et1Mw] := closedP w.
- case/negP: ct'et0; rewrite /ctree_mem Dctu even_etrace /= addn_eq0.
  by apply/nandP; right; apply/match_countP; exists w.
- by apply/andP; rewrite (matchpg_size et0Mw) size_map sz_et0 -Dw0.
by apply/closedPet1/w0P1; rewrite // Dw0 matchg_pg // -Dw0.
Qed.

Lemma Kempe_completeP ctu ctr gtr gtu :
    Kempe_valid ctu ctr gtr gtu -> Kempe_complete 1 ctu ctr gtr gtu ->
    forall et, size et = h.+1 ->
  reflect (Kempe_coclosure P (ctrace et)) (~~ ctree_mem ctu (etrace et)).
Proof.
move=> valid_gt [ctu0 closed_et0] et0 sz_et0.
apply: (iffP idP) => [|clPet0]; first exact: (Kempe_validP valid_gt).
have{valid_gt} [[ctu_ok Dctu] _ Dgtr Dgtu closedP] := valid_gt.
have{ctu0} [|[ctr0 /(_ _)/idP-gtr0]] := ctu0.
  by rewrite ltnS leqn0 => /eqP/(ctree_size_proper ctu_ok)->.
have ctu0 et: sub_gt gtu et = 0 -> ~ ctree_mem ctu et.
  by rewrite /ctree_mem Dctu => ->; rewrite /gtree_sub match_count_0 ?if_same.
have gtu132 et: sub_gt gtu et = 0 -> sub_gt gtu (permt Eperm132 et) = 0.
  apply: contra_eq => /match_countP[w]; rewrite matchpg_flip => gtu_w et_w.
  by apply/match_countP; exists w.
have ctu132 et:
  ctree_mem ctu (permt Eperm132 (etrace et)) -> ctree_mem ctu (etrace et).
- rewrite {2}/ctree_mem Dctu even_etrace {1}/gtree_sub match_count_0 //=.
  by apply: contraNneq => /gtu132/ctu0/idP.
have Pctue et: ctree_mem ctu (etrace et)
                     = ctree_mem ctu et || ctree_mem ctu (permt Eperm132 et).
- have /orb_idl := ctu132 et; rewrite /etrace /etrace_perm.
  by case: ifP => _; rewrite ?permt_id ?etrace_id // orbC.
pose tr_ctu cet := exists2 et, cet = ctrace et & ctree_mem ctu (etrace et).
move Dcet0: (ctrace et0) => cet0 in clPet0; apply/negP=> ctu_et0.
have [cet [et -> ct_et2] | | et Pet []] := clPet0 tr_ctu; try by exists et0.
  set et2 := etrace et in ct_et2; split=> [g|].
    exists (permt g et); first by rewrite ctrace_permt.
    have [g2 <-]: exists g2, permt g2 et2 = permt g et.
      have [g2 Dg2] := compose_permt g (etrace_perm et) et2.
      exists g2; rewrite Dg2 /et2 /etrace /etrace_perm.
      by case: ifP; rewrite ?permt_id ?etrace_id.
    apply: contraLR ct_et2; rewrite !Pctue {2}/permt -map_comp => ct'et2.
    have [||gt'et] := closed_et0 et; rewrite ?ctr0 //.
      right; exists (inv_eperm g2 Color1); apply/negP; case/norP: ct'et2.
      by case: g2 => // _; congr (~~ ctree_mem _ _ = _); apply: eq_map => [] [].
    by apply/norP; split; apply/negP; apply: ctu0 => //; apply: gtu132.
  have /match_countP[w gt_w wMet2]: sub_gt gtu et2 != 0 by apply/eqP=> /ctu0.
  have /andP[sz_w bal_w] := Dgtu _ gt_w.
  exists (cgram 0 false w); first by rewrite matchpg_etrace -matchg_pg in wMet2.
  move=> cet1 cet1Mw; have [et1 Det1]: exists et1, cet1 = ctrace et1.
    have:= balanced_sumt0 bal_w cet1Mw.
    case/lastP: cet1 cet1Mw => [|et1 e _]; first by case w.
    rewrite -{1}cats1 /sumt foldr_cat /= addc0 => sum_et1_0.
    exists et1; congr rcons; rewrite -[e]add0c -{}sum_et1_0.
    by elim: et1 e => /= [|e1 et1 IHet] e; rewrite ?addcc // -addcA IHet.
  exists et1 => //; rewrite Det1 matchg_pg // in cet1Mw.
  rewrite /ctree_mem Dctu even_etrace addn_eq0; apply/nandP; right.
  by apply/match_countP; exists w; rewrite ?matchpg_etrace.
move=> cet Dcet ct_cet.
case: (closed_et0 cet); rewrite ?ctr0 -?Dcet //; first by left.
move=> gt'_cet; case/negP: ct_cet; rewrite Dctu even_etrace.
have ->: sub_gt gtu (etrace cet) = 0.
  by rewrite /etrace /etrace_perm; case: ifP => _; rewrite (permt_id, gtu132).
by rewrite addn0; apply/match_countP=> -[w1 /idPn[]].
Qed.

Lemma Kempe_valid_restrict ctr ctu gtu gtr :
    (forall et, ctree_mem ctr et -> P (ctrace et) /\ size et = h.+1) ->
  Kempe_valid ctu CtreeEmpty gtr gtu -> Kempe_valid ctu ctr gtr gtu.
Proof.
move=> Dctr [[Hctu Ectu] ? Dgtr Dgtu closedP]; split=> // et ct_et.
by case/Dctr: ct_et; split; first by exists (ctrace et).
Qed.

Lemma Kempe_valid_init :
  let ctu := ctree_init_tree h.+1 in let gtu := gtree_init_tree h.+1 in
  Kempe_valid ctu CtreeEmpty GtreeEmpty gtu.
Proof.
move: (ctree_init_tree_proper h.+1) (ctree_sub_init_tree h.+1).
move: (ctree_init_tree _) => ctu ctu_ok Dctu.
move: (gtree_init_tree _) (gtree_mem_init_tree h.+1) => gtu Dgtu.
split=> // [|[]//|w|w]; rewrite ?Dgtu //; split=> // et.
rewrite Dctu andbA andbC; case: (even_trace et) => //=.
by rewrite -match_count_balanced -(match_count_eq Dgtu) gtree_sub_empty.
Qed.

Lemma Kempe_complete_init ctr :
    (forall et, P (ctrace et) -> ctree_mem ctr (etrace et)) ->
    let ctu := ctree_init_tree h.+1 in let gtu := gtree_init_tree h.+1 in
  forall gtr, Kempe_complete (3 ^ h.+2) ctu ctr gtr gtu.
Proof.
move=> Pctr; split=> [|et norm [/Pctr | [e /negP init'e]]]; try by left.
  left; apply: (@leq_ltn_trans (3 ^ h.+1)); last by rewrite ltn_exp2l.
  by apply: ctree_max_size_proper; apply: ctree_init_tree_proper.
right; apply: contraNeq init'e => /match_countP[w].
rewrite gtree_mem_init_tree => /andP[sz_w bal_w] etMw.
rewrite /ctree_mem ctree_sub_init_tree !size_map -(matchpg_size etMw) sz_w.
rewrite -matchg_pg // {}/norm in etMw *; set pre := permt _.
rewrite !ctrace_permt !memc0_permt (matchg_memc0 etMw).
have -> /=: even_trace (pre (etrace et)).
  apply: etrans (even_etrace et); rewrite /even_trace /ttail proper_permt.
  case: (etrace et) => [|[] ett] //=; rewrite /permt -map_comp;
    by apply: (congr1 even_tail (eq_map _ _)); case e => [] [].
rewrite -[n in dyck n]odd_double_half -lt0n.
have -> et': odd (count_cbit1 et') = cbit1 (sumt et').
  by elim: et' => //= c et' IHet'; rewrite oddD IHet' cbit1_addc; case c.
by rewrite !sumt_permt sumt_ctrace !permc0 even_dyck_pos.
Qed.

End KempeTreeClosure.

Definition Kempe_tree (cp : cprog) : ctree :=
  if cprsize cp is h.+2 then
    let ctu := ctree_init_tree h.+1 in
    let gtu := gtree_init_tree h.+1 in
    let ctr := cpcolor cp in
    fst (Kempe_tree_closure h h.+2 ctu ctr gtu)
  else CtreeEmpty.

Theorem Kempe_treeP cp et :
   size et = (cprsize cp).-1 ->
 reflect (Kempe_coclosure (ring_trace (rot 1 (cpring (cpmap cp)))) (ctrace et))
         (~~ ctree_mem (Kempe_tree cp) (etrace et)).
Proof.
set Pcol := ring_trace _; rewrite /Kempe_tree.
move: (cpcolor cp) (ctree_mem_cpcolor cp) => ctr Dctr.
case Dh: (cprsize cp) => [|[|h]].
- by rewrite -size_ring_cpmap head_cpring in Dh.
- by case: et => // _; left=> P1 closedP1 /closedP1[_ [[] ]].
set ctu := ctree_init_tree _; set gtu := gtree_init_tree _.
have [] := @Kempe_tree_closure_correct h Pcol h.+2 ctu ctr gtu.
  apply: (Kempe_valid_restrict _ (Kempe_valid_init _ _)) => et1 /Dctr.
  case=> even_et1 [k gt_k Det1]; split.
    by rewrite /Pcol /ctrace -rot1_cons Det1 -trace_rot -map_rot; exists k.
  rewrite [LHS](canRL succnK (congr1 size Det1)) size_trace size_map.
  by rewrite size_ring_cpmap Dh.
case: (Kempe_tree_closure h _ _ _ gtu) => [ctu' [gtr gtu']] Pcol_valid Pcol_sz.
apply: (Kempe_completeP Pcol_valid (Pcol_sz _ _)); rewrite addn0.
apply: Kempe_complete_init => et1 [k col_k Det1]; apply/Dctr.
rewrite even_etrace /etrace; set g := etrace_perm et1.
split=> //; exists (g \o k); first exact: coloring_inj (@permc_inj g) col_k.
rewrite map_comp trace_permt sumt_permt.
by rewrite -[trace _](rotK 1) -trace_rot -map_rot -Det1 rotr1_rcons.
Qed.
