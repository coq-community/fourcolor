(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype path fingraph.
From fourcolor
Require Import hypermap geometry color coloring cfmap ctree.

(******************************************************************************)
(*   Compute the set of colorings of a configuration ring, directly from the  *)
(* contruction program. The algorithm handles the six kinds of steps, as it   *)
(* is also used to color contracts and explicit configurations.               *)
(* Main definitions:                                                          *)
(*    cpbranch et == given a (full) edge trace et, the ctree that contains    *)
(*                   exactly etail (behead et), the normalised, even tail of  *)
(*                   the (partial) trace behead et.                           *)
(*     cpcolor cp == the ctree storing all the even, partial ring traces of   *)
(*                   colorings of cpmap cp.                                   *)
(* cpcolor1 sp f et == the basic functional for computing cpcolor; computes   *)
(*                   the union of all the ctrees returned by f on ring traces *)
(*                   of the map constructed by applying sp : cpstep to some   *)
(*                   pointed map G, that are induced by a coloring that also  *)
(*                   induces ring trace et on G - this set of traces does not *)
(*                   actually depend on G.                                    *)
(*      cpcolor0 cp == the ctree that contains all the normalised, even tails *)
(*                   of traces of ring colorings of cpmap cp. This is equal   *)
(*                   to foldl cpcolor1 cpbranch [:: Color1; Color1] but       *)
(*                   incorporates additional symmetry reductions.             *)
(* cp_extcol et0 cp1 f k <-> for et := trace (map k (cpring (cpmap cp2)))),   *)
(*                   the trace induced by a coloring k of cpmap cp2, f et is  *)
(*                   a (proper) tree, which contains ttail et0 (the semi-     *)
(*                   normalised tail of et0) and only if ttail et0 is the     *)
(*                   standardised tail of the partial ring trace of an        *)
(*                   coloring extension of k to cpmap (catrev cp1 cp2).       *)
(*      cpexpand cp == cp with all the H an Y stpes replaced by equivalent    *)
(*                   sequences of U, K, R and R' steps.                       *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* First, the optimized all-in-one production of a tree branch, directly from *)
(* a ring trace.                                                              *)

Section Cpbranch2.

Variable h : color -> ctree -> ctree.

Fixpoint cfcbr2 (et : colseq) : ctree :=
  if et is e :: et' then h e (cfcbr2 et') else ctree_simple_leaf.

End Cpbranch2.

Definition ctree_cons_perm g :=
  let cte c := ctree_cons_e (g c) in
  palette (cte Color0) (cte Color1) (cte Color2) (cte Color3).

Section Cpbranch1.

Variable g : color -> color.

Fixpoint cfcbr1 (et : colseq) : ctree :=
  if et is e :: et' then match g e with
  | Color0 => CtreeEmpty
  | Color1 => ctree_cons1 (cfcbr1 et')
  | Color2 => ctree_cons2 (cfcbr2 (ctree_cons_perm g) et')
  | Color3 => ctree_cons2 (cfcbr2 (ctree_cons_perm (Eperm132 \o g)) et')
  end else ctree_simple_leaf.

End Cpbranch1.

Definition cpbranch (et : colseq) : ctree :=
  if et is [:: _,  e & et'] then
    if e == Color0 then CtreeEmpty else cfcbr1 (edge_rot e) et'
  else CtreeEmpty.

(* The coloring procedure uses higher-order programming : we first create a  *)
(* generic iterator over all equivalence classes of colorings of a map given *)
(* by a construction program, then apply it to cpbranch. The iterator is     *)
(* specialized to ctrees, and computes the union of all the trees returned   *)
(* by the function.                                                          *)

Definition cpcolor1 s (f : colseq -> ctree) (et : colseq) :=
  let f2 c et' := f [:: c, c & et'] in
  match s, et with
  | CpR n, _ =>
    f (rot n et)
  | CpR', _ =>
    if size et <= 1 then CtreeEmpty else f (rotr 1 et)
  | CpU, _ =>
    ctree_union (f2 Color1 et) (ctree_union (f2 Color2 et) (f2 Color3 et))
  | CpK, [:: e1, e2 & et'] =>
    if e1 == e2 then CtreeEmpty else f (e1 +c e2 :: et')
  | CpY, e1 :: et' =>
    let e2 := Eperm231 e1 in let e3 := Eperm312 e1 in
    ctree_union (f [:: e2, e3 & et']) (f [:: e3, e2 & et'])
  | CpH, [:: e1, e2 & et'] =>
    if e1 == e2 then ctree_union (f2 (Eperm231 e1) et') (f2 (Eperm312 e1) et')
    else f [:: e2, e1 & et']
  | CpA, [:: e1, e2 & et'] =>
    if e1 == e2 then f (if et' is [::] then et else et') else CtreeEmpty
  | _, _ => CtreeEmpty
  end.

(* For the very first steps, we can examine fewer colorings. *)

Fixpoint cpcolor0 (cp : cprog) : ctree :=
  let cpcol := foldr cpcolor1 cpbranch in
  match cp with
  | CpR _ :: cp' => cpcolor0 cp'
  | CpY :: cp' => cpcol cp' [:: Color1; Color2; Color3]
  | CpU :: cp' =>
      ctree_union (cpcol cp' [:: Color1; Color1; Color2; Color2])
                  (cpcol cp' [:: Color1; Color1; Color1; Color1])
  | _ => cpcol cp [:: Color1; Color1]
  end.

Definition cpcolor (cp : cprog) := ctree_cons_rot (cpcolor0 (rev cp)).

(* Basic correctness lemmatas first. *)

Lemma cpbranch_spec et : cpbranch et = ctree_of_ttail (etail (behead et)).
Proof.
case: et => [|e0 [|e1 et]] //= {e0}.
rewrite /etail /etrace_perm /even_trace /ttail /proper_trace /=.
case: ifP => //= _; move/edge_rot: e1 => g; elim: et => //= e et IHet.
case/g: e; by [ rewrite -IHet; case: ifP
              | congr (ctree_cons2 _); elim: et {IHet} => //= [[] et <-]].
Qed.

(* The main coloring invariant. *)

Section CprogColoringCorrectness.

Variable et0 : colseq.

Section CpcolInvariant.

Variables (cp1 cp2 : cprog) (f : colseq -> ctree) (k : cpmap cp2 -> color).

Definition cp_ht0 := (cprsize (catrev cp1 cp2)).-2.

Definition cp_tr0 k0 :=
  ttail et0 = eptrace (rot 1 (map k0 (cpring (cpmap (catrev cp1 cp2))))).

Inductive cp_extcol :=
  CpExtcol (et := trace (map k (cpring (cpmap cp2)))) of
    ctree_proper cp_ht0 (f et)
  & reflect (exists2 k0, coloring k0 /\ cp_tr0 k0 & k0 \o (@injcp cp1 cp2) =1 k)
            (ctree_mem (f et) (ttail et0)).

End CpcolInvariant.

Section GlobalColoring.

Variables (cp1 cp2 : cprog) (k0 : cpmap (catrev cp1 cp2) -> color).

Lemma gcol_perm :
    coloring k0 /\ cp_tr0 k0 ->
  forall c (h : edge_perm), let k x := c +c h (k0 x) in coloring k /\ cp_tr0 k.
Proof.
move=> [k0col tr_k0] c h k; split.
  suffices inj_ch: injective (addc c \o h) by apply: coloring_inj inj_ch k0col.
  by apply: inj_comp; [apply: addcI | apply: permc_inj].
rewrite /cp_tr0 /eptrace (map_comp (addc c)) (map_comp h).
by rewrite -2!map_rot ptrace_addc -/(permt h) ptrace_permt etail_permt.
Qed.

Lemma gcol_cface :
    coloring k0 -> let k z := k0 (@injcp cp1 cp2 z) in 
  forall x y, cface x y -> k x = k y.
Proof.
move=> [_ k0F] k x y xFy; apply: (fconnect_invariant k0F).
exact: sub_cface_injcp.
Qed.

Lemma gcol_adj :
    coloring k0 -> let k x := k0 (@injcp cp1 cp2 x) in
  forall x p,
   (forall y, adj x y = (y \in fband p)) -> all (fun y => k y != k x) p.
Proof.
move=> [k0E k0F] /= x p Dp /=; apply/allP => y py; apply/negPf.
have{Dp py} xAy: adj x y by rewrite Dp (subsetP (ring_fband p)).
have{xAy} /adjP[u xFu uRy] := sub_adj_injcp cp1 xAy.
rewrite (fconnect_invariant k0F xFu) -(fconnect_invariant k0F uRy).
exact: k0E.
Qed.

End GlobalColoring.

Section TraceCpring.

Variables (G : hypermap) (x0 : G) (k : G -> color).
Hypothesis col_k : coloring k.
Let et : colseq := trace (map k (cpring x0)).

Lemma memc0_trace_cpring : (Color0 \in et) = false.
Proof.
have [kE kF] := col_k; rewrite -mem_rev -(mem_rot 1) /et -trace_rev.
rewrite -map_rev -urtrace_trace urtrace_rot mem_rot.
case: (rev _) (cycle_rev_cpring x0) => // x p.
rewrite (cycle_path x) [path]lock /urtrace {2}[map]lock /= last_map -!lock.
elim: {x p}(x :: p) (last x p) => //= _ p IHp x //= /andP[/eqP<- nxNp].
by rewrite inE IHp // eq_sym addc_eq0 -{1}[x]nodeK (eqcP (kF _)) [_ == _]kE.
Qed.

Lemma coloring_proper_cpring : proper_cpring x0.
Proof.
move: memc0_trace_cpring; rewrite /et size_proper_cpring ltnNge head_cpring.
by case (behead (cpring x0)).
Qed.

Let e1 := k (node x0) +c k x0.
Let e2 := k x0 +c k (face (edge x0)).
Let et'' := ptrace (map k (rcons (drop 2 (cpring x0)) (node x0))).

Lemma trace_cpring_eq : et = [:: e1, e2 & et''].
Proof.
have:= size_long_cpring x0.
rewrite /et (head_proper_cpring coloring_proper_cpring) ltnNge.
rewrite -urtrace_trace /= rot1_cons /urtrace last_rcons /= /et''.
case Dcp: {1}(drop 2 _) => [|z p]; first by rewrite Dcp /e1 /e2 /= => /eqP <-.
by rewrite -map_rcons => /head_long_cpring->.
Qed.

Lemma proper_trace_cpring : proper_trace (behead et).
Proof.
have:= memc0_trace_cpring; rewrite trace_cpring_eq !inE -(eq_sym e2).
by case/norP=> _ /norP[].
Qed.

End TraceCpring.

Section Cpcol1Inv.

Variable cp1 cp2 : cprog.
Let G2 := cpmap cp2.
Variable k : G2 -> color.
Hypothesis col_k : coloring k.
Let et := trace (map k (cpring G2)).

Let et'0 : (Color0 \in et) = false. Proof. exact: memc0_trace_cpring. Qed.

Let G2gt1 : proper_cpring G2. Proof. exact: coloring_proper_cpring col_k. Qed.

Let e1 := k (node G2) +c k G2.
Let e2 := k G2 +c k (face (edge G2)).
Let et2 := ptrace (map k (rcons (drop 2 (cpring G2)) (node G2))).
Let et1 := e2 :: et2.

Let Det : et = e1 :: et1. Proof. exact: trace_cpring_eq. Qed.

Let et1ok : proper_trace et1.
Proof. by have:= proper_trace_cpring G2 col_k; rewrite -/et Det. Qed.

Lemma cpbranch_correct : cp_extcol [::] cpbranch k.
Proof.
split; rewrite /cp_ht0 /cp_tr0 /= -/G2 -/et cpbranch_spec.
  rewrite -size_ring_cpmap -/G2 -(size_map k) -size_trace -/et Det /=.
  apply: ctree_of_ttail_proper; have [g Eg] := etail_perm et1ok.
  by move: (congr1 size Eg); rewrite /permt size_map /= => [] [<-].
have eet'0: Color0 \notin etail (behead et).
  have [g Eg] := etail_perm et1ok.
  by move: et'0; rewrite Det inE -(memc0_permt g et1) Eg => /norP[].
apply: (iffP (ctree_of_ttail_mem _ eet'0)) => [Det0 | [k0 [_ Det0] Dk]].
  exists k => //; split; rewrite // /eptrace {}Det0; congr (etail _).
  by rewrite /et (head_proper_cpring G2gt1) -urtrace_trace.
rewrite {}Det0 /eptrace /et {k0 Dk}(eq_map (Dk : k0 =1 _)).
by rewrite (head_proper_cpring G2gt1) -urtrace_trace.
Qed.

Lemma cpcolor1U_correct f :
    (forall k', coloring k' -> @cp_extcol cp1 (CpU :: cp2) f k') ->
  cp_extcol (CpU :: cp1) (cpcolor1 CpU f) k.
Proof.
rewrite /cpmap -/cpmap -/G2; have [kE kF] := col_k.
pose k' e u := oapp k (e +c k (node G2)) [pick x | cface u (icpU G2 x)].
have k'F e: invariant face (k' e) =1 ecpU G2.
  move=> u; apply/eqP; congr (oapp k _ _).
  by apply: eq_pick => v; rewrite -cface1.
have{kF} k'G2 e x: k' e (icpU G2 x) = k x.
  rewrite /k' -(@eq_pick _ (cface x)) => [|y]; last by rewrite cface_icpU.
  by case: pickP => [y /fconnect_invariant-> | /(_ x)/idP].
have k'X e: k' e (ecpU G2) = e +c k (node G2).
  by rewrite /k'; case: pickP => // x; rewrite cface_ecpU.
have k'Xe e: k' e (edge (ecpU G2)) = k (node G2).
  by rewrite -(k'G2 e) -(eqcP (k'F e _)).
have{kE} k'col e: e != Color0 -> coloring (k' e).
  move=> nz_e; have k'EX: invariant edge (k' e) (ecpU G2) = false.
    by rewrite /= k'X k'Xe addcC -addc_eq0 addKc (negPf nz_e).
  split=> // [] [||x] //=; first by rewrite eq_sym.
  by rewrite (k'G2 _ (edge _)) k'G2; apply: kE.
have Dk' e: trace (map (k' e) (cpring (ecpU G2))) = [:: e, e & et].
  rewrite cpring_ecpU !map_cons k'X k'Xe addcC -map_comp (eq_map (k'G2 e)).
  by rewrite /= addKc /et head_cpring /= addcC /ctrace /= !addKc.
move/(_ _ (k'col _ _))=> f_col.
have []/= := f_col Color3; have []//:= f_col Color2; have []// := f_col Color1.
rewrite !Dk' /= -/G2; set h := cp_ht0 _ _ => t1ok t1P t2ok t2P t3ok t3P.
split; first by do !apply: ctree_union_proper.
rewrite !(@ctree_mem_union h) //; last exact: ctree_union_proper.
apply: (iffP or3P) => [|[k0 k0ccol Dk]].
  by case=> [/t1P|/t2P|/t3P] [k0 ? Dk0]; exists k0 => // x; rewrite [_ x]Dk0.
have [k0col _] := k0ccol; pose ic2 := @injcp cp1 (CpU :: cp2).
pose e0 := k0 (ic2 (ecpU G2)) +c k (node G2).
have k0G: k0 \o ic2 =1 k' e0.
  rewrite /= -/G2 => u /=; have [[x xFu] | XFu] := @fband_icpU _ G2 u.
    by rewrite (fconnect_invariant (k'F e0) xFu) k'G2 -Dk; apply: gcol_cface.
  rewrite -(fconnect_invariant (k'F e0) XFu) k'X -addcA addcc addc0.
  exact/esym/gcol_cface.
case De0: e0 in k0G; [ idtac
 | by constructor 1; apply/t1P; exists k0
 | by constructor 2; apply/t2P; exists k0
 | by constructor 3; apply/t3P; exists k0 ].
case/andP: (@gcol_adj _ (CpU :: cp2) _ k0col _ _ (@adj_ecpU G2 G2)) => /eqP[].
by rewrite ![k0 _]k0G k'G2 k'X add0c.
Qed.

Lemma cpcolor1K_correct f :
   (forall k', coloring k' -> @cp_extcol cp1 (CpK :: cp2) f k') ->
  cp_extcol (CpK :: cp1) (cpcolor1 CpK f) k.
Proof.
rewrite /cpmap -/cpmap -/G2; have [kE kF] := col_k.
pose k' u := oapp k Color0  [pick x | cface u (icpK G2 x)].
have k'F: invariant face k' =1 ecpK G2.
  move=> u; apply/eqP; congr (oapp _ _).
  by apply: eq_pick => v; rewrite -cface1.
have k'G2 x: k' (icpK G2 x) = k x.
  rewrite /k' -(@eq_pick _ (cface x)) => [|y]; last by rewrite cface_icpK.
  by case: pickP => [y /fconnect_invariant-> | /(_ x)/idP].
pose ic2 := @injcp cp1 (CpK :: cp2).
case eq_e12: (e1 == e2).
  split; rewrite /= -/et Det /et1 eq_e12 //; right=> [] [k0 [[k0E k0F] _] Dk].
  rewrite /e1 /e2 addcC (inj_eq (addcI _)) in eq_e12.
  have nGAfeG: adj (ic2 (icpK G2 (node G2))) (ic2 (icpK G2 (face (edge G2)))).
    by apply: sub_adj_injcp; rewrite (adj_icpK G2) fconnect1 connect0 !orbT.
  have [u nGFu uRfeG] := adjP nGAfeG; case/eqcP: (k0E u).
  rewrite -(fconnect_invariant k0F nGFu) (fconnect_invariant k0F uRfeG).
  by rewrite ![k0 _]Dk (eqP eq_e12).
have k'col: coloring k'.
  rewrite /e1 /e2 addcC (inj_eq (addcI _)) (eqcP (kF (edge G2))) in eq_e12.
  split=> // u /=.
  have [[x uFx] [y euFy]] :=(fband_icpK u, fband_icpK (edge u)). 
  rewrite (fconnect_invariant k'F uFx) (fconnect_invariant k'F euFy) !k'G2.
  have xAy: adj (icpK G2 x) (icpK G2 y).
    by apply/adjP; exists u; first by rewrite cfaceC.
  rewrite adj_icpK in xAy; case/or3P: xAy.
  - case/adjP=> z xFz zRy; rewrite (fconnect_invariant kF xFz).
    by rewrite -(fconnect_invariant kF zRy); apply: kE.
  - case/andP=> eGFx nGFy; rewrite -(fconnect_invariant kF eGFx).
    by rewrite -(fconnect_invariant kF nGFy).
  case/andP=> eGFy nGFx; rewrite -(fconnect_invariant kF nGFx).
  by rewrite -(fconnect_invariant kF eGFy) eq_sym.
case/(_ _ k'col); rewrite /cpmap -/cpmap -/G2.
have <-: e1 +c e2 :: et2 = trace (map k' (cpring (ecpK G2))).
  rewrite cpring_ecpK !map_cons -map_comp (eq_map k'G2).
  rewrite (fconnect_invariant k'F (cface_node_ecpK G2)) k'G2.
  move/esym: Det; rewrite /et drop_behead (head_proper_cpring G2gt1).
  rewrite map_cons -!urtrace_trace /urtrace !rot1_cons !last_rcons /=.
  by rewrite headI /= /et1 => [] [De2 <-]; rewrite /e1 De2 -addcA addKc.
move=> t_ok tP; split; rewrite /cpcolor1 -/G2 -/et Det /et1 eq_e12 {t_ok}//.
apply: (iffP tP) => {tP} [] [k0 k0ccol Dk]; have [k0col _] := k0ccol.
  by exists k0 => // x; rewrite [_ x]Dk k'G2.
exists k0 => // u; have [x uFx] := fband_icpK u.
by rewrite /= (fconnect_invariant k'F uFx) k'G2 -Dk; apply: gcol_cface.
Qed.

Lemma cpcolor1A_correct f :
    (forall k', coloring k' -> @cp_extcol cp1 (CpA :: cp2) f k') ->
  cp_extcol (CpA :: cp1) (cpcolor1 CpA f) k.
Proof.
rewrite /cpmap -/cpmap -/G2; have [De12 | neq_e12] := eqVneq e1 e2; last first.
  split; rewrite /cpcolor1 -/G2 -/et Det /et1 (negPf neq_e12) //.
  right; move=> [k0 [[_ k0F] _] Dk]; case/eqP: neq_e12.
  rewrite /e1 addcC; congr addc; rewrite -!Dk; apply: (fconnect_invariant k0F).
  apply: (sub_cface_injcp cp1); rewrite (cface_icpA G2) /=.
  by rewrite !unfold_in /= !connect0 !orbT.
pose k' : ecpA G2 -> color := k; have [kE kF] := col_k.
have:= De12; rewrite [e1]addcC => /addcI KnG.
have k'F: invariant face k' =1 ecpA G2.
  move=> x; apply/eqP; move: (fconnect1 face x); rewrite cface_icpA /k'.
  case/orP=> [/fconnect_invariant <-// | /allP kFx].
  have{kFx} kFx y: y \in [:: x; face x] -> k y = k (node G2).
    move/kFx; rewrite /= unfold_in => /hasP[z Dz /fconnect_invariant-> //].
    by move: Dz; rewrite !inE => /pred2P[]->.
  by rewrite /= kFx ?(kFx x) // ?inE ?eqxx ?orbT.
have k'col: coloring k'.
  split=> // x; rewrite /= /ecpA_edge if_neg.
  case: ifP => eGFnG; last exact: kE.
  case: (x =P _) => [-> | _].
    rewrite /k' -(eqcP (kF _)) nodeK eq_sym -{1}(nodeK G2) (eqcP (kF _)).
    exact: kE.
  case: (x =P _) => [Dx|_]; last by apply: kE.
  rewrite -(canLR (@nodeK G2) Dx) -cface1r in eGFnG.
  by rewrite /k' (fconnect_invariant kF eGFnG); apply: kE.
case/(_ _ k'col); rewrite /cpmap -/cpmap -/G2.
suffices ->: trace (map k' (cpring (ecpA G2))) = if et2 is nil then et else et2.
  by move=> t_ok tP; split; rewrite /= /k' -/et Det /et1 -/et1 -Det De12 eqxx.
rewrite /k' cpring_ecpA; case: ifP => G2gt2.
  rewrite -urtrace_trace /et2 (head_long_cpring G2gt2) /= rot1_cons -KnG.
  by rewrite /urtrace last_rcons -map_rcons headI.
by rewrite -/et /et2 drop_oversize // leqNgt -size_long_cpring G2gt2.
Qed.

Lemma cpcolor1R_correct n f :
   (forall k', coloring k' -> @cp_extcol cp1 (CpR n :: cp2) f k') ->
  cp_extcol (CpR n :: cp1) (cpcolor1 (CpR n) f) k.
Proof. by case/(_ k col_k); rewrite cpring_ecpR map_rot trace_rot. Qed.

Lemma cpcolor1R'_correct f :
   (forall k', coloring k' -> @cp_extcol cp1 (CpR' :: cp2) f k') ->
 cp_extcol (CpR' :: cp1) (cpcolor1 CpR' f) k.
Proof.
case/(_ k col_k); rewrite cpring_ecpR -/cpmap -/G2 -subn1 -size_cpring.
rewrite map_rotr -(rotK 1 (trace _)) -trace_rot rotrK.
by split; rewrite /= size_trace size_map leqNgt -size_proper_cpring G2gt1.
Qed.

End Cpcol1Inv.

Definition cpexpand1 (s : cpstep) : cprog :=
  match s with
  | CpY => [:: CpR'; CpK; CpR 1; CpU]
  | CpH => [:: CpR'; CpK; CpK; CpR 1; CpU]
  | _ => [:: s]
  end.

Fixpoint cpexpand (cp : cprog) : cprog :=
  if cp is s :: cp' then cpexpand1 s ++ cpexpand cp' else [::].

Lemma cpexpand_rcons (cp : cprog) s :
 cpexpand (rcons cp s) = cpexpand cp ++ cpexpand [:: s].
Proof. by elim: cp s => [|s' cp IHcp] s //=; rewrite IHcp -catA. Qed.

Lemma cpcolor1_cpexpand_rev (cp : cprog) f (et : colseq) :
    Color0 \notin et ->
  foldr cpcolor1 f (rev cp) et =
    foldr cpcolor1 f (rev (cpexpand cp)) et :> ctree.
Proof.
have EctE ct: (if ct is CtreeEmpty then CtreeEmpty else ct) = ct by case: ct.
elim/last_ind: cp f et => [|cp s IHcp] // f et et'0.
rewrite cpexpand_rcons -cats1 !rev_cat !foldr_cat; case Ds: s => [n||||||].
- by rewrite /= -IHcp // mem_rot.
- by rewrite /= -IHcp // mem_rotr.
- case: et et'0 => [|[] et] //= et'0; rewrite -?IHcp ?ctree_union_Nl ?EctE //;
  rewrite !cats1 -!rcons_cons !rotr1_rcons //; do !rewrite headI //=.
  by rewrite ctree_union_sym.
- case: et et'0 => [|e1 [|e2 et]] //=; first by rewrite !if_same.
  rewrite !cats1 -!rcons_cons !rotr1_rcons -!rot1_cons !size_rot /=.
  have [<- | ] := altP (e1 =P e2).
    case: e1 => //= et'0; rewrite -?IHcp ?ctree_union_Nl ?EctE //.
    by rewrite ctree_union_sym.
  by case: e1 e2 => [] // [] //= _ et'0; rewrite -!IHcp ?ctree_union_Nl ?EctE.
- by rewrite /= -!IHcp.
- case: et et'0 => [|e1 [|e2 et]] //=.
  case: ifPn; rewrite // !inE !negb_or -addc_eq0 => e12_nz /and3P[_ _ et'0].
  by apply: IHcp; rewrite inE eq_sym (negPf e12_nz).
case: et et'0 => [|e1 [|e2 et]] //= et'0; rewrite -!IHcp//.
by case: et et'0 => [|e3 et] // /norP[_ /norP[]].
Qed.

Inductive pmap_eqdep A (G : pointed_map) (h : A -> G)
                   : forall G' : pointed_map, (A -> G') -> Prop :=
    PmapEqdepRefl : pmap_eqdep h h.

Lemma pmap_eqdep_sym A G G' h h' : @pmap_eqdep A G h G' h' -> pmap_eqdep h' h.
Proof. by case. Qed.

Lemma pmap_eqdep_comp A B f G G' h h' :
 @pmap_eqdep B G [eta h] G' [eta h'] -> @pmap_eqdep A G (h \o f) G' (h' \o f).
Proof. by rewrite -[h' \o f]/([eta h'] \o f); case. Qed.

Lemma pmap_eqdep_split A (G G' : pointed_map) h (h' : _ -> G') :
  @pmap_eqdep A G h (PointedMap G' G') h' -> pmap_eqdep h h'.
Proof. by case: G' h'. Qed.

Lemma injcp_cons s (cp1 cp2 : cprog) :
 pmap_eqdep (fun x => @injcp cp1 (s :: cp2) (injcp [:: s] x))
            (@injcp (s :: cp1) cp2).
Proof. by []. Qed.

Lemma injcp_cat (cp1 cp2 cp3 : cprog) :
  pmap_eqdep (@injcp cp2 _ \o @injcp cp1 _) (@injcp (cp1 ++ cp2) cp3).
Proof.
elim: cp1 cp3 => [|s' cp1 IHcp] cp3; first by case cp2.
rewrite cat_cons; case (injcp_cons s' (cp1 ++ cp2) cp3).
by case: (IHcp (s' :: cp3)).
Qed.

Lemma eqdep_injcpRR' cp :
  pmap_eqdep [eta icpU (cpmap cp)] (@injcp (rev [:: CpR'; CpR 1; CpU]) cp).
Proof.
rewrite /rev /catrev /injcp -/injcp /cpmap -/cpmap.
by apply pmap_eqdep_split; rewrite ecpR1_eq ecpR'_eq edgeK; case: (cpmap cp).
Qed.

Lemma eqdep_injcpRK cp dcp (G : pointed_map) (h : cpmap cp -> G) :
    pmap_eqdep [eta h] (@injcp (rev (CpR' :: dcp)) cp) ->
  pmap_eqdep (icpN G \o h) (@injcp (rev [:: CpR', CpK & dcp]) cp).
Proof.
rewrite -[_ \o _]/(_ \o [eta h]) => /pmap_eqdep_sym[] {G h}.
rewrite !rev_cons -!cats1 -catA cat1s; do 2!case: injcp_cat.
move: {cp}(cpmap cp) {dcp}(catrev _ cp) (@injcp _ cp) => A cp'.
rewrite /catrev /injcp /cpmap -/cpmap; case/cpmap: cp' => G' x f.
by apply pmap_eqdep_split; rewrite /icpK /ecpK !ecpR1_eq !ecpR'_eq edgeK.
Qed.

Lemma injcp_expand cp1 cp2 :
  pmap_eqdep (@injcp (rev cp1) cp2) (@injcp (rev (cpexpand cp1)) cp2).
Proof.
elim: cp1 => [|s cp1 IHcp] //=; rewrite rev_cons -cats1 rev_cat.
do 2!case: injcp_cat => /=; case/pmap_eqdep_sym: IHcp.
move: {cp1}(rev _) => rcp.
move: {cp2}(cpmap cp2) {rcp}(catrev _ cp2) (@injcp _ cp2) => A cp ic.
move Dcps: (rev (cpexpand1 s)) => cps.
case: s Dcps => [n||||||] //= <-{cps} //; apply: {A ic}(pmap_eqdep_comp ic);
  by do !apply: eqdep_injcpRK; apply: eqdep_injcpRR'.
Qed.

Lemma cpcolor1_correct cp1 cp2 k :
  coloring k -> @cp_extcol cp1 cp2 (foldr cpcolor1 cpbranch cp1) k.
Proof.
move=> col_k; rewrite -(revK cp1); move/rev: cp1 => cp1.
pose ecp1 := rev (cpexpand cp1).
suffices []: cp_extcol ecp1 (foldr cpcolor1 cpbranch ecp1) k.
  rewrite {}/ecp1 -cpcolor1_cpexpand_rev ?memc0_trace_cpring // => t_ok tP.
  split; last by move: tP; rewrite /cp_tr0; case: (injcp_expand cp1 cp2).
  by move: t_ok; rewrite /cp_ht0 -!size_ring_cpmap; case: injcp_expand.
rewrite {}/ecp1; elim/last_ind: cp1 cp2 k col_k => [|cp1 s IHcp] cp2 k col_k.
  by apply: cpbranch_correct.
rewrite cpexpand_rcons rev_cat; case: s => [n||||||] /=.
- by apply: cpcolor1R_correct => //; apply: IHcp.
- by apply: cpcolor1R'_correct => //; apply: IHcp.
- apply: cpcolor1U_correct => // k1 k1col.
  apply: cpcolor1R_correct => // k2 k2col.
  apply: cpcolor1K_correct => // k3 k3col.
  by apply: cpcolor1R'_correct => //; apply: IHcp.
- apply: cpcolor1U_correct => // k1 k1col.
  apply: cpcolor1R_correct => // k2 k2col.
  apply: cpcolor1K_correct => // k3 k3col.
  apply: cpcolor1K_correct => // k4 k4col.
  by apply: cpcolor1R'_correct => //; apply: IHcp.
- by apply: cpcolor1U_correct => //; apply: IHcp.
- by apply: cpcolor1K_correct => //; apply: IHcp.
by apply: cpcolor1A_correct => //; apply: IHcp.
Qed.

Lemma cpcolor0_correct cp :
  @cp_extcol cp [::] (fun _ => cpcolor0 cp) (ccons true).
Proof.
set cp2 := [::]; set G := cpmap cp2; set k : G -> color := ccons true.
have dG: cpmap [::] = G :> hypermap by [].
have tr_k: trace (map k (cpring G)) = [:: Color1; Color1] by rewrite cpring0.
have col_k: coloring k by split; case.
elim: cp => [|s cp1 IHcp] in (cp2) G (k) col_k tr_k dG *.
  by case: (cpcolor1_correct [::] col_k); rewrite tr_k.
case: (cpcolor1_correct (s :: cp1) col_k); rewrite tr_k.
have ringG: cpring G = [:: node G; G : G].
  by case: _ / dG (G : G) => b; apply: cpring0.
have k_nG: k (node G) = Color1 +c (k G).
  by move: tr_k; rewrite ringG => [] [<-]; rewrite addcK.
have GF'nG: cface (node G) G = false.
  by case: _ / dG (G : G); case; rewrite fconnect_id.
have G'nG: (node G == G :> G) = false by case: _ / dG (G : G); case.
have GnG x: x = G :> G \/ x = node G.
  by apply/pred2P; case: _ / dG (G : G) x; do 2!case.
case: s => // [n||].
- have [] // := IHcp (CpR n :: cp2) k.
  by rewrite cpring_ecpR map_rot trace_rot tr_k; case: n => [|[|[]]].
- pose k' u := if cface u (ecpY G) then Color2 else
               if cface u (icpY G G) then Color0 else Color3.
  have dF (u v : ecpY G): cface u v = (v \in [:: u; face u]).
    apply: fconnect_cycle (mem_head u _) v.
    by case: _ / dG (G : G) u; do 4?case.
  have /= <-: trace (map k' (cpring (ecpY G))) = [:: Color1; Color2; Color3].
    by rewrite cpring_ecpY ringG /= /k' !dF; case: _ / dG (G : G); do 3?case.
  have k'F: invariant face k' =1 ecpY G.
    by move=> u; apply/eqP; rewrite /k' -!cface1.
  have k'col: coloring k'.
    by split=> // u; rewrite /= /k' !dF; case: _ / dG (G : G) u; do 6?case.
  have [et et_ok etP] := @cpcolor1_correct cp1 (CpY :: cp2) _ k'col.
  rewrite [cpmap _ ]/= -/G in et et_ok etP; split=> {et_ok}//.
  apply: {etP}(iffP etP) => [] [k0 k0ccol /(_ _)/=Dk0].
    pose h0 := locked Eperm231.
    exists (fun x => k G +c h0 (k0 x)) => [|x]; first exact: gcol_perm.
    rewrite /= Dk0 /k' cfaceC dF cface_icpY /= addcC; unlock h0.
    by have [-> | ->] := GnG x; [rewrite connect0 add0c | rewrite GF'nG].
  pose e0 := k G +c k0 (@injcp cp1 (CpY :: cp2) (ecpY G)).
  pose h0 := if e0 == Color2 then Eperm321 else Eperm312.
  exists (fun x => h0 (k G) +c h0 (k0 x)) => [|u]; first exact: gcol_perm.
  have [/= k0col _] := k0ccol; rewrite -permc_addc /k'.
  have [[x uFx] | XFu] := @fband_icpY G G u.
    rewrite !(same_cface uFx) cfaceC dF (gcol_cface k0col uFx) Dk0 cface_icpY.
    have [-> | ->] := GnG x; first by rewrite addcc permc0 connect0.
    by rewrite GF'nG k_nG addcC addcK /h0; case: ifP.
  rewrite cfaceC XFu -(gcol_cface k0col XFu) -/e0 {}/h0.
  have /(gcol_adj k0col)/and3P[]:= adj_ecpY (coloring_proper_cpring G col_k).
  by rewrite !Dk0 -!(addc_eq0 (k _)) k_nG -addcA -/e0; case: e0.
pose k' e u :=
  if u == ecpU G :> ecpU G then Color1 else if u == icpU G G then e else Color0.
have k'F e: invariant face (k' e) =1 ecpU G.
  by rewrite /k'; case: _ / dG e (G : G); do 4?case.
have k'col e: e != Color0 -> coloring (k' e).
  by case: e; split=> //; rewrite /k'; case: _ / dG (G : G); do 3?case.
have Ek' e: trace (map (k' e) (cpring (ecpU G))) = [:: Color1; Color1; e; e].
  by rewrite cpring_ecpU ringG /= /k'; case: _ / dG e (G : G); do 3?case.
have [] := @cpcolor1_correct cp1 (CpU :: cp2) _ (k'col Color2 isT).
have{k'col} [] := @cpcolor1_correct cp1 (CpU :: cp2) _ (k'col Color1 isT).
rewrite [cpmap _]/= -/G /cpcolor0 !{}Ek' => t1ok t1P t2ok t2P.
split; first exact: ctree_union_proper.
rewrite {t1ok t2ok}(ctree_mem_union (ttail et0) t2ok t1ok); apply: (iffP orP).
  case=> [/t2P | /t1P] [k0 k0ccol /(_ _)/=Dk0].
    exists (fun x => k (node G) +c Eperm213 (k0 x)); first exact: gcol_perm.
    move=> x; rewrite /= Dk0 /k' /= (inj_eq (@ecp_inj _)) addcC.
    by have [-> | ->] := GnG x; [rewrite eqxx k_nG addKc | rewrite G'nG add0c].
  exists (fun x => k (node G) +c Eperm123 (k0 x)); first exact: gcol_perm.
  move=> x; rewrite /= Dk0 /k' /= (inj_eq (@ecp_inj _)) addcC.
  by have [-> | ->] := GnG x; [rewrite eqxx k_nG addKc | rewrite G'nG add0c].
case=> k0 k0ccol /(_ _)/=Dk0; rewrite -/G in k0 k0ccol Dk0.
have [/=k0col _] := k0ccol.
pose e0 := k (node G) +c k0 (@injcp cp1 (CpU :: cp2) (ecpU G)).
have nz_e0: e0 != Color0.
  by rewrite addc_eq0 -Dk0; case/andP: (gcol_adj k0col (@adj_ecpU _ _)).
have [e01 | n1_e0] := eqVneq e0 Color1.
  right; apply/t1P; exists (fun w => k (node G) +c Eperm123 (k0 w)) => [|u].
    exact: gcol_perm.
  have [[x uFx] | XFu] := fband_icpU u.
    rewrite (fconnect_invariant (k'F _) uFx) /= (gcol_cface k0col uFx) Dk0.
    rewrite /k' (inj_eq (@ecp_inj _)) /=.
    by have [-> | ->] := GnG x; [rewrite eqxx k_nG addcK | rewrite G'nG addcc].
  rewrite -(fconnect_invariant (k'F _) XFu) /= -(gcol_cface k0col XFu) /k'.
  by rewrite eqxx.
left; apply/t2P; pose h0 := if e0 == Color2 then Eperm213 else Eperm231.
exists (fun w => h0 (k (node G)) +c h0 (k0 w)); first exact: gcol_perm.
move=> u; rewrite /= -permc_addc; have [[x uFx] | XFu] := fband_icpU u.
  rewrite (fconnect_invariant (k'F _) uFx) /= (gcol_cface k0col uFx) Dk0.
  rewrite /k' (inj_eq (@ecp_inj _)) /=.
  have [-> | ->] := GnG x; last by rewrite G'nG addcc permc0.
  by rewrite eqxx k_nG addcK /h0; case: ifP.
rewrite -(fconnect_invariant (k'F _) XFu) /= -(gcol_cface k0col XFu) /k' -/e0.
by rewrite {}/h0; case: e0 nz_e0 n1_e0.
Qed.

End CprogColoringCorrectness.

Theorem cpcolor_proper cp : ctree_proper (cprsize cp).-1 (cpcolor cp).
Proof.
rewrite /cpcolor; case Dh: (cprsize cp).-1 => [|h]; last first.
  have [/= et_ok _] := cpcolor0_correct [::] (rev cp).
  rewrite /cp_ht0 -/(rev (rev cp)) revK Dh in et_ok.
  exact: ctree_cons_rot_proper.
have [/= et_ok /(_ _)etP] := cpcolor0_correct [:: Color1] (rev cp).
move: etP et_ok; rewrite /cp_ht0 -/(rev (rev cp)).
case: (cpcolor0 (rev cp)) => // [t1 t2 t3 _| lf]; first by rewrite revK Dh.
case=> // [k0 [k0col _] _] _; rewrite revK in k0 k0col.
have:= coloring_proper_cpring (cpmap cp) k0col.
by rewrite size_proper_cpring size_ring_cpmap -subn_gt0 subn1 Dh.
Qed.

Theorem ctree_mem_cpcolor cp et :
  reflect (even_trace et /\ ring_trace (cpring (cpmap cp)) (sumt et :: et))
          (ctree_mem (cpcolor cp) et).
Proof.
rewrite ctree_mem_cons_rot -[in _ /\ _](revK cp); set G := cpmap _.
have [/= _] := cpcolor0_correct et (rev cp); rewrite /cp_tr0 -/G => etP.
apply: {etP}(iffP etP) => [[k [col_k tr_k] _] | [et_even [k col_k tr_k]]].
  set rc := rot 1 _ in tr_k.
  have [rc_ok et_ok]: proper_trace (ptrace rc) /\ proper_trace et.
    move: (memc0_trace_cpring G col_k) (proper_trace_cpring G col_k) tr_k.
    rewrite -urtrace_trace -/rc; case: rc => // y rc.
    rewrite /urtrace /ptrace /= /ttail /eptrace inE => /norP[_].
    case: ifP => // _ rc'0 rc_ok /esym/(congr1 (has (pred1 Color0))).
    by rewrite has_pred1 memc0_permt memc0_ttail rc_ok (negPf rc'0).
  have [[h2 Eh2] [h1]] := (etail_perm rc_ok, etail_perm et_ok).
  rewrite /etail /etrace_perm /even_trace {}tr_k even_etail permt_id -{}Eh2.
  pose h1' := inv_eperm h1; pose h12 := h1' \o h2.
  move=> eq_h12; split=> //; exists (h12 \o k).
    by apply: coloring_inj col_k; apply: inj_comp; apply: permc_inj.
  rewrite 2!map_comp !trace_permt; apply: canRL (mapK (inv_permc h1)) _.
  rewrite /= -sumt_permt -/(permt h1) {}eq_h12 sumt_permt -map_cons.
  congr (map _ _); apply: (can_inj (@rotK 1 _)).
  by rewrite rot1_cons -trace_rot -/rc; case: rc rc_ok.
set ic0 := @injcp _ _; pose e0 := k (ic0 true) +c k (ic0 false).
have et_ok: proper_trace et.
  by have:= proper_trace_cpring G col_k; rewrite -tr_k.
have e0ok: proper_trace [:: e0].
  rewrite /proper_trace /= addc_eq0.
  have [] // := andP ((gcol_adj col_k) false [:: true] _).
  by move=> b; rewrite unfold_in /adj orbit_id /= /rlink !fconnect_id eq_sym.
have [h0 [he0 _]] := etail_perm e0ok.
exists (fun w => Color2 +c h0 (k (ic0 false)) +c h0 (k w)) => [|x].
  apply: gcol_perm; split; rewrite // /cp_tr0 -/G /eptrace.
  move: tr_k; rewrite -urtrace_trace /urtrace; case: (rot 1 _) => //= x p [_].
  by move <-; rewrite /etail /etrace_perm et_even permt_id.
rewrite [Color2]lock /= -lock; case: x; last by rewrite addcK.
by rewrite -addcA -permc_addc (addcC (k _)) he0.
Qed.

