(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype path fingraph.
From fourcolor Require Import hypermap walkup.

(******************************************************************************)
(* This file proves the validity of our Jordan curve theorem inspired         *)
(* combinatorial characterization of planaratity. The Euler_tree lemma below  *)
(* provides an analogue of the "break the dikes" proof of Euler's formula.    *)
(* It is later used to prove the correctness of the key step of the           *)
(* reducibility decision procedure in file kempe.v.                           *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Planarity.

Implicit Type G : hypermap.

Theorem even_genusP G : even_genus G.
Proof.
move: {2}_.+1 (ltnSn #|G|) => n; elim: n => // n IHn in G * => leGn.
have [z _ | noG] := pickP G.
  by apply/(@even_genus_WalkupE G z)/IHn; rewrite -card_S_Walkup.
have o0 (a : pred G): #|a| = 0 by apply: eq_card0 => x; have:= noG x.
by rewrite /even_genus /genus /Euler_rhs /Euler_lhs /n_comp_mem !{1}o0.
Qed.

Theorem Euler_le G : Euler_rhs G <= Euler_lhs G.
Proof. by rewrite even_genusP leq_addl. Qed.

Local Notation cpath := (path clink).

(******************************************************************************)
(* To prove the Jordan path planarity property we consider a minimal counter  *)
(* example G, planar (in the Euler formula sense) but containing a Moebius    *)
(* path p from x to node t for some darts x and t. Then p (hence G) must      *)
(* contain at least three darts, and the Euler formula rules out #|G| = 3.    *)
(* We use Walkup transforms to construct smaller maps with Moebius paths.     *)
(* In fact we can use an E-transform on any z not between F- and N-links in p *)
(* (in particular if z \notin p), and an F- (resp. N-) transform on any z     *)
(* in p that is followed by an N- (resp. F-) link, and that is not one of     *)
(* node x, edge (node t), and node t. However this is somewhat awkward to do  *)
(* for darts in the middle of p, so we restrict ourselves to the first three  *)
(* darts x, y, z of p, or darts outside p altogether. In detail, we suppress  *)
(*  1) a dart not in p, with an E-transform                                   *)
(*  2) x with an E-transform if x is followed by an N-link (i.e., x = node y) *)
(*  3) y = face x with an F-transform, if y is followed by an N-link.         *)
(*  4) y with an E-transform, if y != t (by 3), z = face y)                   *)
(*  5) y with an N-transform, if y != node x                                  *)
(*  6) z with an E-transform, if z is followed by an F-link in p              *)
(*  7) z with an F-transform, otherwise (z is followed by an N-link in p)     *)
(* Despite the larger number of cases, this proof is 15% shorter than the one *)
(* relying on the general transforms, because in each case we only need to    *)
(* lift a single subpath to the Walkup map, and we have extra facts on x, y   *)
(* and z that simplify the proof. In particular we only handle the #|G| = 3   *)
(* case between steps 5) and 6), where most of G is known.                    *)
(******************************************************************************)

Theorem planar_Jordan G : planar G -> Jordan G.
Proof.
move: {-1}_.+1 (ltnSn #|G|) => m; elim: m G => // m IHm G leGm planarG [//|].
have{leGm} ltG'm (z : G) : #|WalkupE z| < m by rewrite -card_S_Walkup.
have IHe z := IHm (WalkupE z) (ltG'm z) (planar_WalkupE z planarG).
have IHn z := IHm (WalkupN z) (ltG'm z) (planar_WalkupN z planarG).
have{m IHm ltG'm} IHf z := IHm (WalkupF z) (ltG'm z) (planar_WalkupF z planarG).
have injG z : injective (val : WalkupE z -> G) := val_inj.
pose ofG (z x : G) : x != z -> WalkupE z := Sub x.
have uniqG z := map_inj_uniq (injG z); have mem2G z := mem2_map (injG z).
have clink_eq := sameP clinkP pred2P.
pose map_cpath f x p := {q | (f q.1, map f q.2) = (x : G, p) & cpath q.1 q.2}.
pose lift_cpath z H f x p := z \notin x :: p -> cpath x p -> map_cpath H f x p.
have liftE z x p: lift_cpath z (WalkupE z) val x p.
  rewrite /lift_cpath -has_pred1 /= => /norP[z'x]; pose u := ofG z x z'x.
  elim: p => [|y p IHp] /= in x z'x u *; first by exists (u, nil).
  case/norP=> z'y _ /andP[xCy /IHp[]// [v q] /= [Dv Dq] vCq].
  exists (u, v :: q); rewrite /= ?clink_eq -?val_eqE /= Dv ?Dq //.
  by have [<- | ->] := clinkP xCy; rewrite (negPf z'x, negPf z'y) eqxx ?orbT.
have liftN z x p: face z \notin p -> lift_cpath z (WalkupN z) val x p.
  rewrite /lift_cpath -!has_pred1 /= => fz'p /norP[z'x]; pose u := ofG z x z'x.
  move: fz'p; elim: p => [|y p IHp] /= in x z'x u *; first by exists (u, nil).
  case/norP=> fz'y _ /norP[z'y _] /andP[xCy /IHp[]// [v q] /= [Dv Dq] vCq].
  exists (u, v :: q); rewrite /= ?clink_eq -?val_eqE /= Dv ?Dq //.
  rewrite (canF_eq (canF_sym faceK)) (negPf fz'y).
  have [<- | ->] := clinkP xCy; last by rewrite orbC ifN ?eqxx.
  by rewrite (negPf z'x) if_same eqxx.
have liftF z x p: face (edge z) \notin p -> lift_cpath z (WalkupF z) val x p.
  rewrite /lift_cpath -!has_pred1 /= => fez'p /norP[z'x]; pose u := ofG z x z'x.
  move: fez'p; elim: p => [|y p IHp] /= in x z'x u *; first by exists (u, nil).
  case/norP=> fez'y _ /norP[z'y _] /andP[xCy /IHp[]// [v q] /= [Dv Dq] vCq].
  exists (u, v :: q); rewrite /= ?clink_eq -?val_eqE /= Dv ?Dq //.
  rewrite !(canF_eq nodeK) ifN_eq //.
  have [<- | ->] := clinkP xCy; first by rewrite eqxx.
  by rewrite (negPf fez'y) (negPf z'y) if_same eqxx orbT.
move=> x p; have [t Lp]: {t | last x p = node t} := exist _ _ (esym (edgeK _)).
apply/and3P; rewrite Lp (finv_f nodeI) => -[/=/andP[p'x Up] xCp ptnx].
have /predT_subset-sGp: G \subset x :: p.
  apply/subsetPn=> -[z _ p'z]; have /liftE[//| [u q] /= [Du Dq] uCq] := p'z.
  have z't: t != z by rewrite (memPn p'z) // mem_behead ?(mem2l ptnx).
  have Lq: last u q = node (ofG z t z't).
    by apply/injG; rewrite -last_map /= Du Dq /= -Lp ifN ?(memPn p'z) ?mem_last.
  case/and3P: (IHe z (u :: q)); rewrite Lq (finv_f nodeI) -mem2G -uniqG /= Dq.
  by rewrite Du p'x ifN // (memPn p'z) // mem_behead ?(mem2r ptnx).
have oG: #|G| = (size p).+1 by rewrite -(eq_card sGp) (card_uniqP _) //= p'x.
case: p Up xCp => //= y p /andP[p'y Up] /andP[xCy yCp] in ptnx p'x Lp sGp oG *.
have x'y: y != x by rewrite (memPn p'x) ?mem_head.
have x't: t != x by rewrite (memPn p'x) ?(mem2l ptnx).
have x'nt: node t != x by rewrite -Lp (memPn p'x) ?mem_last.
case: p => [|z p] /= in ptnx p'x p'y Up yCp Lp sGp oG *.
  by rewrite mem2_seq1 Lp (inj_eq nodeI) andbC eq_sym (negPf x't) in ptnx.
have y'nt: node t != y by rewrite -Lp (memPn p'y) ?mem_last.
have{xCy} Dfx: face x = y.
  case/clinkP: xCy => // Dny; have /liftE[//| [u q] /= [Du Dq] uCq] := p'x.
  have Lq: finv node (last u q) = ofG x t x't.
    by apply/(canLR (finv_f nodeI))/injG; rewrite -last_map /= Du Dq /= ifN.
  case/and3P: (IHe x (u :: q)); rewrite Lq -mem2G -uniqG /= Du Dq -Dny eqxx p'y.
  by rewrite mem2_cons ifN // -(inj_eq nodeI) -Dny eq_sym in ptnx.
have{yCp Up} [[yCz zCp] [p'z Up]] := (andP yCp, andP Up).
move: ptnx p'x; rewrite !inE !negb_or mem2_cons => ptnx /and3P[y'x z'x p'x].
have z'y: y != z by rewrite (memPnC p'y) ?mem_head.
have{yCz} Dfy: face y = z.
  case/clinkP: yCz => // Dnz; pose u : WalkupN y := ofG y x y'x.
  have /liftF[|//| [v q] /= [Dv Dq] vCq] := p'y; first by rewrite Dnz nodeK.
  have Lq: finv node (last v q) = insubd v t.
    apply/(canLR (finv_f nodeI))/injG; rewrite -last_map Dq /= val_insubd /= Dv.
    by rewrite Lp; case: (t =P y) => [-> | _]; rewrite /= -?Dnz ?eqxx ?ifN.
  case/and3P: (IHf y (u :: v :: q)); rewrite Lq -mem2G -uniqG /= val_insubd Dq.
  rewrite vCq clink_eq -!val_eqE /= Dv Dnz nodeK !(inj_eq nodeI) -Dnz eqxx.
  rewrite -Dfx (inj_eq faceI) Dfx (negPf x'y) (negPf z'x) (negPf z'y) !eqxx.
  move: ptnx; rewrite orbT !negb_or p'x p'z inE Dnz (inj_eq nodeI) (negPf z'x).
  by rewrite eq_sym; case: ifP; rewrite // mem2_cons eqxx.
have Dt: t = y.
  have /liftE[//| [v q] /= [Dv Dq] vCq] := p'y.
  apply: contraNeq (IHe y (ofG y x y'x :: v :: q)) => y't; apply/and3P.
  have ->: finv node (last v q) = ofG y t y't.
    by apply/(canLR (finv_f nodeI))/injG; rewrite -last_map /= Dv Dq /= ifN.
  rewrite -mem2G -uniqG /= clink_eq orbC -val_eqE /= Dv Dq Dfx Dfy !eqxx /=.
  split=> //; first by rewrite negb_or z'x p'x p'z.
  by rewrite ifN_eqC // in ptnx; rewrite ifN // (memPn p'y) ?(mem2r ptnx).
move: ptnx Lp x'nt y'nt; rewrite {t x't}Dt eqxx /= => p_nx Lp x'ny y'ny.
have{p_nx} Dnx: node x = y.
  have /liftN[|//| [v q] /= [Dv Dq] vCq] := p'y; first by rewrite Dfy.
  apply: contraNeq (IHn y (ofG y x y'x :: v :: q)) => y'nx; apply/and3P.
  have ->: finv node (last v q) = v.
    apply/(canLR (finv_f nodeI))/injG; rewrite /= -last_map Dv Dq ifN //.
    by rewrite Lp -Dfy faceK eqxx.
  rewrite -mem2G -uniqG /= clink_eq -!val_eqE /= Dv Dq negb_or z'x p'x p'z.
  rewrite (negPf y'ny) vCq -Dfy faceK Dfy Dfx !eqxx orbT; split=> //.
  rewrite -(inj_eq faceI) nodeK Dfy !ifN // mem2_cons eqxx /=.
  by rewrite inE (negPf y'nx) /= in p_nx.
rewrite inE negb_or z'y /= in p'y.
case: p zCp => /= [_ | t p /andP[zCt tCp]] in p'x p'y p'z Up Lp sGp oG *.
  case/idPn: planarG; rewrite -lt0n half_gt0 ltn_subRL -addnA /Euler_lhs {}oG.
  have oG1 f: injective f -> f x = y /\ f y = z -> f z = x /\ fcard f G = 1.
    move=> injf [Dy Dz]; rewrite -Dy -Dz in sGp; split.
      by have/predU1P[|/norP[]] := sGp (f z); rewrite ?orbF ?inj_eq ?(eq_sym z).
    rewrite // -(n_comp_connect (fconnect_sym injf) x).
    apply/esym/eq_n_comp_r => t; have:= sGp t; rewrite !inE -Dy.
    by case/or3P=> /eqP->; rewrite -?same_fconnect1_r ?connect0.
  have [[//|Dfz ->] [//|Dnz ->]]:= (oG1 _ faceI, oG1 _ nodeI).
  have [|_ ->] := oG1 _ edgeI; first by rewrite -Dnz -{2}Dnx -Dfz -Dfy !faceK.
  by rewrite !addnS [n_comp _ G](cardD1 (root glink x)) inE (roots_root glinkC).
have z'ny: node y != z by rewrite -Lp (memPn p'z) ?mem_last.
have{zCt} Dnt: node t = z.
  case/clinkP: zCt => // Dfz; have /liftE[//| [w q] /= [Dw Dq] wCq] := p'z.
  have /and3P[] := IHe z [:: ofG z x z'x, ofG z y z'y, w & q].
  rewrite mem2_cons -uniqG -(canF_eq (finv_f nodeI)) /= !clink_eq -!val_eqE /=.
  rewrite -last_map Dw Dq wCq Lp Dfx Dfy Dfz (negPf z'y) !eqxx !orbT.
  split=> //; first by rewrite negb_or y'x p'x p'y.
  by rewrite (negPf z'ny) eqxx /= !inE -val_eqE /= Dnx (negPf z'y) eqxx.
have /liftF[|//| [w q] /= [Dw Dq] wCq] := p'z.
  by rewrite -Dnt nodeK; case/andP: Up.
have /and3P[] := IHf z [:: ofG z x z'x, ofG z y z'y, w & q].
rewrite mem2_cons -uniqG -(canF_eq (finv_f nodeI)) /= !clink_eq -!val_eqE /=.
rewrite (negPf z'ny) -last_map Dw Dq Lp eqxx inE negb_or y'x p'x p'y Up wCq.
split=> //; last by rewrite inE -val_eqE /= Dnx (negPf z'y) eqxx.
rewrite Dfx (negPf z'ny) -Dfy (inj_eq faceI) Dfy -Dnt !(inj_eq nodeI) nodeK Dnt.
by rewrite (eq_sym z) (negPf z'y) !eqxx ifN ?eqxx ?orbT //; case/norP: p'z.
Qed.

(******************************************************************************)
(*   This is a more precise reformulation of the central argument of the      *)
(* graph theoretical proof of Euler's formula: a connected map with only one  *)
(* face has no cycles so it must be a tree and contain one terminal node. Our *)
(* refined version states that every hyperedge contains either a dart linked  *)
(* to a different hyperedge (dual to a different face), or a degenerate dart  *)
(* (analogue to a terminal node). Since in either case the WalkupE transform  *)
(* suppressing the dart preserves the genus formula this immediately gives a  *)
(* proof of the Euler formula below; the additional precision is used in the  *)
(* correctness proof of the reducibility check.                               *)
(*   As in the graph theoretical proof, we assume both conditions fail for a  *)
(* given hyperedge and construct a Moebius path, our analogue of a contour    *)
(* that violates the Jordan curve theorem, as follows:                        *)
(*   1) We pick a maximal face-simple arc x :: p whose last dart z1 lies in   *)
(*      the same face as node (face x), the dart preceding x in the hyperedge *)
(*      (anticipating the definition of 'simple' in geometry.v.)              *)
(*   2) We construct a (dart-simple) contour face x :: q1 along p, that ends  *)
(*      at node (face x). As this contour is a concatenation of F-cycles,     *)
(*      together with the F-cycle arc from face z1 to node (face x),          *)
(*      z1 -- face z1 is the only F-link leading into face x :: q1.           *)
(*   3) We construct the arc face x :: p2 from face x to node (face x). This  *)
(*      arc does not contain z1: it is disjoint from x :: p1 because x :: p1  *)
(*      is face-simple and x is non-degenerate. Note that face x is on the    *)
(*      hyperedge because node (face x) is.                                   *)
(*   4) Finall we try to extend the contour face x :: q1 along the reverse of *)
(*      p2, until we hit face x :: q1 (this must surely happen as p2 ends in  *)
(*      face x). The only F-links in this extension originate in face x :: p2 *)
(*      so by 2) this extension must reach q1 with a reverse N-link; pruning  *)
(*      loops in the extension with undup thus yields a Moebius C-path, which *)
(*      contradicts the Jordan assumption.                                    *)
(******************************************************************************)

Lemma Euler_tree G (x : G) :
  Jordan G -> ~~ [disjoint cedge x & [pred y | clink y y || ~~ cross_edge y]].
Proof.
move: x => x0 JordanG; rewrite disjoint_subset; apply/subsetP=> tree_x0.
have rfP := rootP (@cfaceC G); move: (froot face) => rf in rfP.
have rfF x: rf (face x) = rf x by apply/rfP; rewrite -cface1.
pose simple := [pred p | uniq (map rf p)].
have [x x0Ex [p1 [xEp1 Sp1 Lp1]]]: exists2 x, cedge x0 x & exists p1,
  [/\ fpath edge x p1, simple (x :: p1) & cface (last x p1) (node (face x))].
- have /connectP[p0 ex0Ep0 Lp0]: cedge (edge x0) x0 by rewrite cedgeC fconnect1.
  pose p := edge x0 :: p0; pose x := x0; rewrite (Lp0 : x0 = last x p).
  have{Lp0} notSp: ~~ simple (x :: p) by rewrite [x]Lp0 /= -last_map mem_last.
  have{ex0Ep0} xEp: fpath edge x p by rewrite /= eqxx.
  elim: {p0}p x xEp notSp => //= _ p IHp x /andP[/eqP<- exEp].
  rewrite negb_and negbK -cons_uniq -map_cons orbC [~~ _ || _]if_neg.
  case: ifPn => [{IHp}Sp pFx | notSp _]; last exact: IHp notSp.
  exists (edge x); first by rewrite cedgeC; apply/connectP; exists p.
  case/mapP: pFx Sp exEp => y /splitPl[p1 p2 Lp1] /rfP-xFy.
  rewrite -cat_cons map_cat cat_uniq cat_path => /andP[Sp1 _] /andP[exEp1 _].
  by exists p1; rewrite Lp1 edgeK cfaceC.
do [set fx := face x; set nfx := node fx; set z1 := last x p1] in Lp1.
have{x0 x0Ex tree_x0} tree_x := tree_x0 _ (connect_trans x0Ex _).
have{Lp1} [q1 [fxCq1 Lq1 Uq1 _ z1Fq1]]: exists q1, let q := fx :: q1 in
  [/\ path clink fx q1, last fx q1 = nfx, uniq q, map rf q =i map rf (x :: p1)
    & forall y, face y \in q -> y \in belast z1 q].
- have spFC y p: fpath face y p -> path clink y p by apply/sub_path/subrelUr.
  move: nfx {tree_x} => z in Lp1 *.
  elim: p1 => /= [|y p IHp] in x z1 fx xEp1 Lp1 Sp1 *.
    have{Lp1} /connectP[_ /shortenP[q fxFq Uq _] Lq]: cface (face x) z.
      by rewrite -cface1.
    exists q; rewrite spFC //; split=> //= y.
      rewrite !inE -(rfF x) eq_sym orb_idr // => {y}/mapP[y q_y ->].
      by rewrite (sameP eqP (rfP _ _)) (path_connect fxFq) //= mem_behead.
    rewrite !inE (inj_eq faceI); case: (y == x) => //= q_fy.
    case/splitPr: q_fy fxFq => q1 q2; rewrite cat_path => /and3P[_ /eqP-Dfy _].
    by rewrite belast_cat -(faceI Dfy) mem_cat mem_head orbT.
  have{xEp1 Sp1} [[/eqP-Dy yEp] [p'Fx Sp]] := (andP xEp1, andP Sp1).
  have{IHp yEp Lp1 Sp} [q2 [fexCq2 Lq2 Uq2 rf_q2 z1Fq2]] := IHp y yEp Lp1 Sp.
  have /connectP[_ /shortenP[q1 fxFq1 Uq1 _] Lq1]: cface fx x by apply/rfP/rfF.
  have q1x: x \in fx :: q1 by rewrite Lq1 mem_last.
  have cFq1: fcycle face (fx :: q1) by rewrite (cycle_path x) /= -Lq1 eqxx.
  have{cFq1 q1x} q1Fx t: cface x t = (t \in fx :: q1) by apply: fconnect_cycle.
  exists (q1 ++ face y :: q2); rewrite cat_path -Lq1 last_cat spFC //=.
  split=> // [||t|t]; first by rewrite -[x]edgeK Dy clinkN.
  - rewrite -cons_uniq -cat_cons cat_uniq Uq1; case: hasP => //= -[t q2t q1t].
    by rewrite (rfP x t _) ?q1Fx // -rf_q2 -map_cons map_f in p'Fx.
  - rewrite map_cat 2!inE mem_cat rf_q2 orbA rfF [lhs in lhs || _]orb_idr //.
    by case/mapP=> {}t q1t ->; rewrite (rfP x t _) ?q1Fx // mem_behead.
  rewrite belast_cat -cat_cons mem_cat -q1Fx /= -cat_rcons -lastI -cface1r.
  by rewrite [t \in _]inE mem_cat orbCA -q1Fx; case: (cface x t) => // /z1Fq2.
have{rf rfP rfF simple Sp1} p1'fx: fx \notin x :: p1.
  apply: contra (tree_x x _); rewrite // !inE (sameP clinkP pred2P).
  by case/orP=> [-> | p1fx]; rewrite ?orbT //= -rfF map_f in Sp1 *.
have xEnfx: cedge x nfx by rewrite cedge1r faceK.
have xEfx: cedge x fx.
  suffices clNEx: fclosed node (cedge x) by rewrite [cedge _ _](fclosed1 clNEx).
  apply: (intro_closed cnodeC) => y _ /eqP<- xEy.
  by have /norP[_ /negPn] := tree_x y xEy; apply: connect_trans.
pose fxq1 := [pred y in fx :: q1]; pose y := fx.
have{tree_x xEnfx} nfx'y: y != nfx.
  by apply: contraNneq (tree_x _ xEnfx) => Dy; rewrite !inE -{2}Dy clinkN.
suffices{nfx'y} [q2 [_ Lq2 /(conj nfx'y)/norP]]:
  exists q2, [/\ path clink nfx q2, last nfx q2 = y & ~~ has fxq1 q2].
- by rewrite has_sym /= -/y -Lq2 orbA -in_cons mem_last.
have [p2 []]: exists p2, [/\ fpath edge y p2, last y p2 = nfx & z1 \notin p2].
  have /connectP[_ /shortenP[p z1Ep /andP[p'z1 _] _] Lp]: cedge z1 nfx.
    by rewrite cedgeC cedge1 faceK; apply/connectP; exists p1.
  have p1p_fx: fx \in (x :: p1) ++ p.
    apply: etrans xEfx; apply/esym/fconnect_cycle; last exact: mem_head.
    by rewrite /= rcons_path cat_path xEp1 z1Ep last_cat -Lp /= faceK.
  move: p1p_fx z1Ep p'z1 Lp; rewrite mem_cat (negPf p1'fx).
  case/splitPr: p / => p p2; rewrite cat_path /= => /and3P[_ _ fxEp2].
  by rewrite mem_cat last_cat => /norP[_ /norP[_]]; exists p2.
elim: p2 y => [|_ p IHp y /andP[/eqP<- /IHp{}IHp Lp]]; first by exists nil.
rewrite inE => /norP[ey'z1 /(IHp Lp){p Lp}{}IHp].
apply: (@proj2 (y != nfx)); pose fey := face (edge y).
have /connectP[q]: fconnect node y fey by rewrite cnode1r edgeK.
elim: q (y) => /= [_ _ <- | _ q IHq z /andP[/eqP<- /IHq-IHz] /IHz{IHq IHz IHp}].
  have [q2 [nfxCq2 Lq2 q1'q2]] := IHp; suffices fxq1'fey: ~~ fxq1 fey.
    split; first by rewrite -Lq1 (memPnC fxq1'fey) ?mem_last.
    exists (rcons q2 fey); rewrite last_rcons rcons_path nfxCq2 Lq2 clinkF.
    by rewrite has_rcons negb_or fxq1'fey.
  apply: contra q1'q2 => /z1Fq1/=; rewrite inE eq_sym (negPf ey'z1) /= => q1ey.
  apply/hasP; exists (edge y); rewrite /= ?mem_belast //.
  have /predU1P[Dey | //]: edge y \in nfx :: q2 by rewrite -Lq2 mem_last.
  by rewrite lastI Lq1 -Dey rcons_uniq q1ey in Uq1.
case=> nfx'nz [q3 [/shortenP[q2 nfxCq2 /=/andP[q2'nxf Uq2] sq23] Lq2 q1'q3]].
have{q q3 q1'q3 sq23} q1'q2: ~~ has fxq1 q2.
  by apply: contra q1'q3; rewrite ![has fxq1 _]has_sym; apply: sub_has.
suffices fxq1'z: ~~ fxq1 z.
  split; first by rewrite -Lq1 (memPnC fxq1'z) ?mem_last.
  exists (rcons q2 z); rewrite last_rcons rcons_path Lq2 clinkN.
  by rewrite nfxCq2 has_rcons negb_or fxq1'z.
rewrite /= inE -(inj_eq nodeI) (negPf nfx'nz) /=.
apply: contra (JordanG (fx :: q1 ++ q2)) => q1z; apply/and3P.
rewrite cat_path last_cat fxCq1 Lq1 nfxCq2 -/nfx -cat_cons cat_uniq Uq1 q1'q2.
by rewrite Lq2 (finv_f nodeI) mem2r_cat // -Lq1 mem2_last.
Qed.

Theorem Jordan_planar G : Jordan G -> planar G.
Proof.
move: {-1}_.+1 (ltnSn #|G|) => m; elim: m G => // m IHm G leGm JordanG.
have [x _ | noG] := pickP G; last first.
  have o0 (a : pred G): #|a| = 0 by apply: eq_card0 => z; have:= noG z.
  by rewrite /planar /genus /Euler_rhs /Euler_lhs /n_comp_mem !{1}o0.
have /pred0Pn[z /andP[_ leaf_z]] := Euler_tree x JordanG.
rewrite /planar -(@genus_WalkupE_eq _ z) //.
  by apply: IHm (Jordan_WalkupE JordanG); rewrite -card_S_Walkup.
apply/orP; case/orP: leaf_z => [|->]; last exact: orbT.
by case/clinkP=> [{2}-> | {2}<-]; rewrite (glinkN, glinkF).
Qed.

Theorem planarP G : reflect (Jordan G) (planarb G).
Proof. exact: iffP idP (@planar_Jordan G) (@Jordan_planar G). Qed.

End Planarity.

