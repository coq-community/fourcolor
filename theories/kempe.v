(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype path fingraph.
From fourcolor Require Import hypermap walkup jordan geometry color chromogram.
From fourcolor Require Import coloring.

(******************************************************************************)
(*   The proof of the Kempe closure property of the set of trace colorings of *)
(* the border ring of a planar plain quasicubic hypermap.                     *)
(*   This is the main link between the reflected combinatorial reducibility   *)
(* proofs, and the mathematical theory of planar graphs developed in the rest *)
(* of the proof. The result is also reused to validate the reduction to       *)
(* internally 5-connected triangulations.                                     *)
(*   We start by defining three small functions on chromograms that modify    *)
(* chromograms by flipping brackets in various ways:                          *)
(*  gram_neg w == negate (invert) the parity bit of the first Gpop of w not   *)
(*                matching an earlier Gpush.                                  *)
(* gram_flip w == change the first unmatched Gpop of w into a Gpush, setting  *)
(*                the parity bit of the next unmatched Gpop so that the       *)
(*                overall parity of the resulting chromogram is inverted.     *)
(* --> This operation turns a chromogram with exactly two unbalanced Gpop     *)
(*     into a balanced one.                                                   *)
(*  gram_rot w == if w is balanced (all Gpush and Gpop are matched), return   *)
(*                the chromogram that matches the left rotation of the edge   *)
(*                colorings matched by w: gram_rot w matches rot 1 et exactly *)
(*                when w matches et.                                          *)
(* These functions are used to match changes in the perimeter as edges are    *)
(* removed in the main theorem, which proceeds by induction on the graph      *)
(* size, much as the proof of the Euler formula planarity property; indeed,   *)
(* the proof uses the `Euler_tree' lemma from that proof to select edges.     *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section KempeMap.

(* Negate the bit of the first unmatched Gpop. *)
Fixpoint gram_neg_rec n (w : chromogram) {struct w} : chromogram :=
  match w, n with
  | Gpush :: w', _    => Gpush :: gram_neg_rec n.+1 w'
  | Gskip :: w', _    => Gskip :: gram_neg_rec n w'
  |     s :: w', n.+1 =>     s :: gram_neg_rec n w'
  | Gpop0 :: w', 0    => Gpop1 :: w'
  | Gpop1 :: w', 0    => Gpop0 :: w'
  |      [::],   _    => w
  end.
Definition gram_neg := gram_neg_rec 0.

Lemma match_gram_neg b0 et w :
   matchg [:: b0] et (gram_neg w) = matchg [:: ~~ b0] et w.
Proof.
set sb := [::]; rewrite /gram_neg -[0]/(size sb) -![_ :: _]/(rcons sb _).
elim: w et sb => [|s w IHw] et lb; first by case lb.
case: s; (case: et => [|e et]; first by case lb);
 by [ have:= IHw et (_ :: lb); case: e => /=
    | case: e; case: lb => [|b lb]; rewrite /= ?if_neg ?IHw ].
Qed.

(* Change the next unmatched Gpop into a Gpush, and adjust the bit of the     *)
(* next Gpop so that the total parity is inverted.                            *)
Fixpoint gram_flip_rec (n : nat) (w : chromogram) {struct w} : chromogram :=
  match w, n with
  | Gpush :: w',  _   => Gpush :: gram_flip_rec n.+1 w'
  | Gskip :: w',  _   => Gskip :: gram_flip_rec n w'
  |     s :: w', n.+1 =>     s :: gram_flip_rec n w'
  | Gpop0 :: w', 0    => Gpush :: gram_neg w'
  | Gpop1 :: w', 0    => Gpush :: w'
  |      [::],   _    => Gpush :: w
  end.
Definition gram_flip := gram_flip_rec 0.

Lemma match_gram_flip et w :
  matchg [::] et (gram_flip w) =
    matchg [:: true; false] et w || matchg [:: false; true] et w.
Proof.
set lb0 := [:: true; false]; set lb0' := [:: false; true]; set sb := [::].
rewrite /gram_flip -(cat0s lb0) -(cat0s lb0') -/sb -[0]/(size sb).
elim: w et sb => [|s w IHw]; first by case=> [|[|||] [|e et]] [|b lb].
by case: s => [] [|[] et] [|[] lb] //=; rewrite !(orbF, IHw, match_gram_neg).
Qed.

(*   Rotate a chromogram by moving the first symbol to the end, changing it   *)
(* to a Gpop if it's a Gpush, as well as flipping the matching Gpop.          *)
(*   We check for imbalanced chromograms first, to ensure that matchg is      *)
(* always preserved.                                                          *)
Definition gram_rot w :=
  if [exists b, gram_balanced 0 b w] then
    match w with
    | Gpush :: w' => gram_flip (rcons w' Gpop1)
    | Gskip :: w' => rcons w' Gskip
    |        _    => w
    end
  else w.

Lemma match_gram_rot et w :
  matchg [::] (rot 1 et) (gram_rot w) = matchg [::] et w.
Proof. 
rewrite /gram_rot; case: ifPn => [/existsP[/= b0]| ]; last first.
  rewrite negb_exists => /forallP/(_ _)/negPf /= bal'w.
  by apply/idP/idP=> /matchg_balanced[_]; rewrite bal'w.
case: et w => [|e et]; first by do 4!case=> //.
rewrite rot1_cons => [[|[] w]] /= bal_w; try by case: e et; do 2?case.
  suffices{bal_w} IHw b lb:
      gram_balanced (size lb) b0 w ->
    matchg (b :: lb) (rcons et e) (rcons w Gpop1) =
      (e == ccons true (~~ last b lb)) && matchg (belast b lb) et w.
  - by rewrite match_gram_flip !{}IHw //; case: e; rewrite ?orbF.
  rewrite andbC; elim: w lb b b0 et => [|s w IHw] lb b b0 et.
    by case: lb => // [] _; case: b; (case: et; [case: e | do 2?case]).
  case: et => [|e' et]; first by case: s; case: e {IHw} => //; case: b; case: w.
  case: s; case: e' => //=;
   by [ apply: IHw | apply: (IHw (b :: lb))
      | case: b; case: lb => [|b' lb] //=; apply: IHw].
elim: w [::] et {b0 bal_w} => [|s w IHw] lb et.
  by case e; case: et; do 2?case.
case: et => [|e' et]; first by case e; case: s lb => [|||] [|[|] lb] //; case w.
by case: s; case: e' => //=; case: lb => [|[|] lb'] //=; case e.
Qed.

(******************************************************************************)
(*   The main theorem, which we prove (by induction) in a single piece rather *)
(* than going through the face to edge coloring equivalence, 23-path ring     *)
(* dart outerplanar pairings, and bracket encoding chain of equivalences      *)
(* sketched in paper proofs. While perhaps more intuively revealing, this     *)
(* approach would have used planar induction twice, and seq induction with a  *)
(* complicated semantic parsing invariant. We avoid most of this by proving   *)
(* the closure property directly for chromograms, and using "without loss"    *)
(* and the chromogram permutation functions above to consider only the first  *)
(* few colors and gram symbols.                                               *)
(*  More precisely, we prove Kempe closure by induction on the size of a      *)
(* planar remainder map, using a double Walkup-N transform to contract one of *)
(* the edges incident to the perimeter N-cycle r (r need not be simple, i.e., *)
(* r need not be a ring). We assume k is a coloring of G, and need to find a  *)
(* chromogram matching k on r, and whose matching colorings all extend to     *)
(* colorings of G. This is trivial if r = nil; otherwise r is an E-cycle in   *)
(* in permN G so the Euler_tree then gives us a dart z in r whose edge either *)
(*   (a) loops back to the perimeter, enclosing a single face: face z = z.    *)
(*   (b) is incident to an inner (hence cubic) node: edge z isn't in r.       *)
(* Using the gram_rot operator defined above, we can assume without loss that *)
(* z is the second dart in r, more precisely, that rot 1 r = z :: p. As k is  *)
(* a coloring, k z != k (node z), so p != nil. Contracting [:: z; edge z]     *)
(* yields a remainder map H with a projection h onto G \ [:: z; edge z], and  *)
(* a perimeter N-cycle s which h maps to either p1 = behead p in case (a), or *)
(* node (edge z) :: face z :: p in case (b). Provided its trace on rotr 1 s   *)
(* starts with distinct colors in case (b), a coloring k1 of H lifts to a     *)
(* coloring k0 of G; in case (a) we can also set the head of trace k0 r.      *)
(*   Applying induction to the coloring k \o h of H yields a chromogram w.    *)
(* In case (a) the required chromogram is Gskip :: Gskip :: w if trace k r    *)
(* starts with Color1, otherwise it is Gpush :: Gpop0 :: w. In case (b) we    *)
(* first show w = s1 :: s2 :: w1 where either {s1, s2} = {Gskip, Gpush},      *)
(* s1 = s2 = Gpush, or w = Gpush :: Gpop0 :: w1. The required chomogram is    *)
(* then Gpush :: gram_neg w1, Gskip :: kempe_flip w1, or Gskip :: w1, in      *)
(* each of these three cases, respectively.                                   *)
(******************************************************************************)

Theorem Kempe_map (G : hypermap) (r : seq G) :
  ucycle_planar_plain_quasicubic r -> Kempe_closed (ring_trace r).
Proof.
move: {-1}_.+1 (ltnSn #|G|) => n leGn geoGr _ [k [kE kF] ->]; split=> [g|].
  exists (g \o k); last by rewrite map_comp trace_permt.
  by split=> x; rewrite (invariant_inj _ k (@permc_inj g)).
elim: n => // n IHn in G leGn r geoGr k kE kF *; rewrite ltnS in leGn.
have [[ee nf_e] e'id] := (plain_eq geoGr, plain_eq' geoGr, plain_neq geoGr).
have [planG cubGr] := (geoGr : planar G, geoGr : quasicubic r).
have{geoGr} /andP[cycNr Ur]: ufcycle _ r := geoGr; have /=eq_kF := eqcP (kF _).
have n'id x: (node x == x :> G) = false.
  by apply: contraFF (kE (node x)); rewrite /= -eq_kF nodeK => /eqP->.
without loss [z r_z Dfz]: / {z | z \in r & (face z == z) || (face z \notin r)}.
  case Dr: r => [|x p] in cycNr *; first by exists [::] => [|[]] //; exists k.
  apply; have /planarP-JordanGn: planar (permN G) by rewrite planar_permN.
  have /exists_inP/sig2W[/= z xNz Dfz] := Euler_tree (x : permN G) JordanGn.
  have r_z: z \in x :: p by rewrite -(fconnect_cycle cycNr (mem_head x p)).
  rewrite inE (sameP clinkP pred2P) /= e'id orbF eq_sym in Dfz.
  by exists z; rewrite -?(fconnect_cycle cycNr r_z).
without loss [p Dr]: r r_z Dfz cycNr Ur cubGr / {p | rot 1 r = z :: p}.
  have /rot_to[i p Dr]: z \in rot 1 r by rewrite mem_rot.
  pose ri := rot i r => /(_ ri); rewrite !mem_rot rot_uniq rot_cycle rot_rot.
  case=> //; first 2 [by exists p].
    by congr eq: cubGr; apply/eq_subset=> x /=; rewrite !inE mem_rot.
  have{Dr} [j lejr <-]: {j | j <= size ri & rot j ri = r}.
    by exists (size ri - i); rewrite ?leq_subr ?[LHS]rotK.
  have{lejr} <-: iter j (rot 1) ri = rot j ri.
    by elim: j => [|j IHj] in lejr *; rewrite ?rot0 //= IHj -?rotS // ltnW.
  elim: j ri => [|j IHj] r1 w WMr wGr; first by exists w.
  rewrite iterSr; apply: IHj (gram_rot w) _ _ => [|et'].
    by rewrite map_rot trace_rot match_gram_rot.
  rewrite -(rotrK 1 et') match_gram_rot => /wGr[k' col_k' ->].
  by rewrite -trace_rot -map_rot; exists k'.
rewrite -(rotK 1 r) rot_uniq rot_cycle mem_rot Dr in cycNr Ur Dfz.
have{Ur} [p'z Up]: z \notin p /\ uniq p by apply/andP.
have defNz y: cnode z y = (y \in z :: p) by apply/fconnect_cycle/mem_head.
case Dp: p cycNr => [|nz p1]; first by rewrite /= n'id.
rewrite (cycle_path z) /= => /and3P[/eqP/(canRL nodeK)-Lp1 /eqP-Dnz nzNp1].
set fz := face z in Dfz; set ez := edge z in Lp1; pose nez := node ez.
pose ez' : WalkupN z := Sub ez (negbT (e'id _)).
have eez': edge ez' = ez' by apply: val_inj; rewrite /= ee eqxx.
pose H := WalkupE ez'; pose h (u : H) : G := sval (sval u).
have{n leGn} {}/IHn-IH_H: #|H| < n by rewrite ltnW // -!card_S_Walkup.
have invh x: x != z -> x != ez -> {u | h u = x}.
  by move=> z'x ez'x; apply: exist (Sub (Sub x _ : WalkupN z) _) _.
have h_eqE u v: (h u == h v) = (u == v) by [].
have Ih: injective h by move=> u v /val_inj/val_inj.
have z'h u: (h u == z) = false by apply/negbTE/(valP (val u)).
have ez'h u: (h u == ez) = false by apply/negbTE/(valP u).
have hE: {morph h : x / edge x}.
  move=> u /=; rewrite glink_fp_skip_edge; last by rewrite -{2}eez' glinkE.
  by rewrite [h _]fun_if -val_eqE /= (canF_eq ee) ez'h (inj_eq edgeI) z'h.
have hN u: h (node u) = [eta id with z |-> nez, ez |-> nz] (node (h u)).
  rewrite [h _]fun_if -val_eqE /= n'id -/nez (canF_eq ee) -/fz -/ez.
  have [Dnu | ez'nu] := altP (node (h u) =P ez).
    by rewrite Dnu e'id ifN_eqC // -Dnu (inj_eq nodeI) z'h.
  have [Dnu | _] := altP (node (h u) =P z); last by rewrite ifN.
  by rewrite nf_e eqxx (canF_eq ee) n'id ifN_eqC // -Dnu (inj_eq nodeI) ez'h.
have planH: planar H; [exact/planar_WalkupE/planar_WalkupN | clearbody h H].
have plainH: plain H.
  by apply/plainP; split; [apply Ih; rewrite !hE ee | rewrite -h_eqE hE e'id].
pose invh_r1 := [fun s => map h s = if fz == z then p1 else [:: nez, fz & p]].
have [s cycNs {invh_r1}/= h_s]: exists2 s, fcycle node s & invh_r1 s.
  have invh_p q: ~~ has (pred2 z ez) q -> exists s, map h s = q.
    elim: q => [|x q IHq /norP[/norP[z'x ez'x]]] /=; first by exists [::].
    by have [u <-] := invh x z'x ez'x => /IHq[s <-]; exists (u :: s).
  have invhNp u s: fpath node (h u) (map h s) -> fpath node u s.
    elim: s => //= v s IHs in u * => /andP[/eqP-Dnu /IHs{IHs}->].
    by rewrite andbT -h_eqE hN Dnu /= z'h ez'h.
  do [rewrite {invh_r1}/=; have /altP[fzz | z'fz] := fz =P z] in Dfz *.
    have ez_nz: ez = nz by rewrite -Dnz -fzz nf_e.
    have [|s Ds] := invh_p p1; last exists s => //.
      rewrite has_predU !has_pred1 negb_or.
      by move: p'z Up; rewrite Dp -ez_nz => /norP[_ ->] /andP[->].
    rewrite -{}Ds /= -ez_nz in Lp1 nzNp1.
    case: s nzNp1 => //= u s1 /andP[/eqP-Du uNs1] in Lp1 *.
    by rewrite rcons_path invhNp //= -h_eqE hN -last_map Lp1 edgeK /= -Du !eqxx.
  have [|Dn3fz _] := cubicP cubGr fz; first by rewrite -Dr mem_rot in Dfz.
  have [|s Ds] := invh_p [:: nez, fz & p]; last exists s => //.
    rewrite /= has_predU !has_pred1 !negb_or p'z n'id z'fz /=.
    rewrite -(canF_eq ee) (canF_eq edgeK) andbCA eq_sym n'id /=.
    rewrite -defNz 2!cnode1r nf_e -/nez in Dfz.
    rewrite (contraNneq _ Dfz) => [|->] //=.
    by apply: contra Dfz; rewrite -cnode1r defNz inE e'id.
  rewrite Dp in Ds; case: s Ds => [|u [|v [|w s1]]] //= [Du Dv Dw Ds1].
  rewrite rcons_path /= -!h_eqE !hN -last_map Du Dv invhNp Dw Ds1 //= Lp1 !nf_e.
  by rewrite ee e'id /nez -[ez in y in node y]nf_e Dn3fz -Dv z'h ez'h !eqxx.
have cubHs: quasicubic (rotr 1 s).
  apply/cubicP=> u; rewrite !inE mem_rot -(mem_map Ih) h_s; set x := h u => s'x.
  have zN'x: ~~ cnode z x.
    rewrite defNz inE z'h /=; apply: contra s'x => p_x.
    case: eqP => [fzz | _ ]; last by rewrite !inE p_x !orbT.
    by rewrite Dp -Dnz -fzz nf_e inE ez'h in p_x.
  have [|Dn3x _] := cubicP cubGr x; first by rewrite defNz -Dr mem_rot in zN'x.
  have z'nx: node x != z by apply: contraNneq zN'x; rewrite cnode1r => ->.
  have h_nu: h (node u) = node x.
    rewrite hN -/x /= !ifN // (canF_eq nodeK) ee -/fz.
    by apply: contraNneq s'x => <-; rewrite z'h inE mem_head orbT.
  split; [apply: Ih; rewrite hN | by rewrite -h_eqE h_nu n'id].
  suffices ->: h (node (node u)) = node (node x) by rewrite Dn3x /= z'h ez'h.
  rewrite hN h_nu /=.
  rewrite !ifN //; last by apply: contraNneq zN'x => <-; rewrite -!cnode1.
  apply: contraNneq s'x => Dn2x; rewrite /nez -Dn2x Dn3x ifN ?mem_head //.
  by rewrite /fz -[z in face z]ee -[edge z]Dn2x nodeK.
have{planH plainH cycNs cubHs} geoH: ucycle_planar_plain_quasicubic (rotr 1 s).
  repeat split=> //; apply/andP; split; first by rewrite rot_cycle.
  rewrite rot_uniq -(map_inj_uniq Ih) h_s.
  case: (fz == z) in Dfz *; first by have:= Up; rewrite Dp => /andP[].
  have [|Dn3fz _] := cubicP cubGr fz; first by rewrite -Dr mem_rot in Dfz.
  rewrite /= -Dn3fz /nez -[ez]nf_e inE eq_sym n'id Dn3fz /=.
  rewrite !(contra _ Dfz) //=; first by rewrite inE orbC => ->.
  by rewrite -defNz 2!cnode1r defNz inE orbC => ->.
have invh_col_s k1 e1 (et1 := urtrace (map k1 s)) :
    coloring k1 -> uniq (if fz == z then [:: e1; Color0] else take 2 et1) ->
  {k0 | coloring k0 & k1 =1 k0 \o h /\ (fz == z -> k0 z +c k0 nz = e1)}.
- have [k0 Dk0]: {k0 | k1 =1 k0 \o h}.
    exists (fun x => oapp k1 e1 [pick u | h u == x]) => u /=.
    by case: pickP => [_ /eqP/Ih-> | /(_ u)/eqP].
  pose e2 := k0 (face ez); pose e3 := [eta k0 with z |-> e1 +c e2] fz.
  case=> k1E k1F Uet1; have{Uet1} e2'3: e3 != e2.
    apply: contraLR Uet1; rewrite /et1 /e3 /= (eq_map Dk0) map_comp h_s Dp.
    case: (fz == z) => /= [|De2]; first by rewrite -addc_eq0 addcK inE andbT.
    by rewrite andbT inE last_map Lp1 -/e2 addcC (can_eq (addKc _)) eq_sym.
  exists [eta k0 with z |-> e3, ez |-> e2]; last first.
    split=> [x | fzz] /=; first by rewrite z'h ez'h Dk0.
    by rewrite eqxx -Dnz n'id (canF_eq nodeK) ee (eq_sym z) /e3 /= fzz addcK.
  split=> x /=; [apply/idPn | apply/eqP].
    rewrite !(canF_eq ee) ee -/ez.
    have /altP[-> | ez'x] := x =P ez; first by rewrite e'id.
    have [_ | z'x] := ifPn; first by rewrite eq_sym.
    by have [u <-] := invh x z'x ez'x; rewrite -hE -![k0 _]Dk0 [_ == _]k1E.
  have /altP[-> | z'x] := x =P z.
    by rewrite -[ez]nf_e [_ == node _]eq_sym n'id /e3 /=; case: (fz == z).
  have /altP[-> | ez'x] := x =P ez.
    by rewrite eq_sym -(canF_eq nodeK) n'id if_same.
  have [u <-] := invh x z'x ez'x; rewrite -[RHS]Dk0 -(eqcP (k1F _)) Dk0.
  rewrite -[in LHS](faceK u) hE hN /= !(canF_eq nodeK) ee -/fz -/ez /e3.
  have [-> | _] := h (face u) =P face ez; first by rewrite nodeK e'id eqxx.
  by have [<- | _] := h _ =P fz; rewrite -?Dnz nodeK ?ez'h /= z'h ?eqxx.
have [khE khF]: coloring (k \o h).
  split=> u /=; first by rewrite hE [_== _]kE.
  rewrite -[in h u](faceK u) hE hN /=; move: {u}(h (face u)) => y.
  apply/eqP; rewrite -[y in LHS]nodeK eq_kF.
  have [-> | _] := node y =P z; first by rewrite -[edge z]nodeK eq_kF.
  by have [-> | _ //] := node y =P ez; rewrite ee -[z]nodeK Dnz eq_kF.
have{geoH IH_H} [w] := IH_H _ geoH _ khE khF.
rewrite -urtrace_trace -map_rot rotrK map_comp h_s Dp => kMw sMw.
do [have /altP[fzz | z'fz] := fz =P z] in invh_col_s h_s kMw.
  have trace_r k0: coloring k0 ->
    {e1 | e1 != Color0 & trace (map k0 r) = [:: e1, e1 & urtrace (map k0 p1)]}.
  - case=> k0E k0F; pose e1 := k0 z +c k0 nz; exists e1.
      rewrite addc_eq0; apply: contraFneq (k0E nz) => /= <-.
      by rewrite -Dnz -[in node z]fzz faceK.
    rewrite -urtrace_trace -map_rot Dr Dp /urtrace /= addcC -/e1.
    case: {+}p1 Lp1 => //= nnz p2; rewrite last_map => ->.
    by rewrite -[ez]nf_e -/fz fzz Dnz (eqcP (k0F _)).
  have [//|e1 nz_e1 ->] := trace_r k.
  pose w2 := if e1 == Color1 then Gskip :: Gskip :: w else Gpush :: Gpop0 :: w.
  exists w2 => [|et etMw2]; first by case: e1 nz_e1 @w2.
  have [e2 nz_e2 [et2 et2Mw Det]]: exists2 e2, uniq [:: e2; Color0]
    & exists2 et2, matchg [::] et2 w & et = [:: e2, e2 & et2].
  - by case: ifP @w2 et => //= _ [|e2 et] // in etMw2 *; exists e2;
       case: e2 et etMw2 => // -[|[] et] //; exists et.
  have /sMw[k1 k1col] := et2Mw; rewrite -urtrace_trace -map_rot rotrK => Det2.
  have{nz_e2} [k0 k0col [Dk0 De2]] := invh_col_s k1 e2 k1col nz_e2.
  exists k0 => //; have [e3 _ tr_k0r] := trace_r k0 k0col; rewrite tr_k0r.
  rewrite {}Det {}Det2 (eq_map Dk0) map_comp h_s -{}De2 //; congr (ncons 2 _ _).
  by have:= tr_k0r; rewrite -urtrace_trace -map_rot Dr Dp => -[].
pose e1 := k ez +c k z; pose e2 := k ez +c k nez.
have De21: e2 +c e1 = k nez +c k z by rewrite [e2]addcC addcA addcK.
rewrite /urtrace /= last_map Lp1 !eq_kF -/e2 -{}De21 in kMw.
case: w => [|s1 [|s2 w]] // in kMw sMw *; first by case: (s1) e2 kMw => -[].
have [| nz_e1] := boolP (e1 == Color0); first by rewrite addc_eq0 [_ == _]kE.
have Ds12: if s1 == Gpush then s2 != Gpop0 else (s1, s2) == (Gskip, Gpush).
  by case: s1 e2 e1 nz_e1 s2 kMw {sMw} => [] // [] // [] // _ [].
exists (if Gskip \in [:: s1; s2] then Gpush :: gram_neg w else
        Gskip :: (if s2 == Gpush then gram_flip w else w)).
- rewrite -urtrace_trace -map_rot Dr Dp /urtrace /= last_map Lp1 eq_kF -/e1.
  move: (k z +c k nz :: _) kMw {sMw} => et.
  by case: s1 e2 s2 Ds12 e1 nz_e1 => [] // [] // [] // _ [] //= _;
     rewrite ?match_gram_neg // match_gram_flip => ->; rewrite ?orbT.
case=> [|e et etMw]; first by case: (s1) (s2) Ds12 => [] // [].
pose e0 := if s1 == Gskip then Color1 else
           if s2 == Gskip then Color1 +c e else
           ccons true ((s2 == Gpush) && matchg [:: false; true] et w).
have{kMw sMw} [|k1 k1col Det] := sMw [:: e0, e0 +c e & et].
  by case: s1 s2 Ds12 e etMw @e0 => [] // [] // _ [] //=;
    rewrite ?match_gram_neg // ?match_gram_flip orbC; case: ifP.
rewrite -urtrace_trace -map_rot rotrK in Det.
have [|k0 [k0E k0F] [Dk0 _]] := invh_col_s k1 Color0 k1col.
  rewrite -{}Det /= take0 inE andbT -addc_eq0 {e0}addKc.
  by case: e s1 s2 Ds12 etMw => [] // [] // [].
exists k0; rewrite // -urtrace_trace -map_rot Dr.
rewrite (eq_map Dk0) map_comp h_s Dp /urtrace /= (eqcP (k0F z)) in Det *.
by case: Det => -> /(canRL (addKc _))-> <-; rewrite addcA addcK.
Qed.

End KempeMap.

