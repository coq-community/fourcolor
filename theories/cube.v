(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype path fingraph.
From fourcolor Require Import hypermap geometry color coloring.

(******************************************************************************)
(*   Reduction of the coloring problem to cubic maps; since this is not the   *)
(* inductive case, we can construct a larger map:                             *)
(*    cube G == a cubic plain hypermap that is planar and bridgeless iff the  *)
(*              hypermap G is, and is four_colorable only if G is. Each dart  *)
(*              in G splits into six darts in cube G; there is a face in      *)
(*              cube G for each face, node and edge in G.                     *)
(*  cube_tag == the type of the tag that flags the six different copies of    *)
(*              each dart in cube G.                                          *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Cube.

Variable G : hypermap.

Inductive cube_tag := CTn | CTen | CTf | CTnf | CTe | CTfe.

Definition cube_tag_enum := [:: CTn; CTen; CTf; CTnf; CTe; CTfe].
Definition cube_tag_code o :=
  match o with
  | CTn => 0 | CTen => 1 | CTf => 2 | CTnf => 3 | CTe => 4 | CTfe => 5
  end.

Fact cube_tag_codeK : cancel cube_tag_code (nth CTn cube_tag_enum).
Proof. by case. Qed.

Definition cube_tag_eqMixin := CanEqMixin cube_tag_codeK.
Canonical cube_tag_eqType := EqType cube_tag cube_tag_eqMixin.
Definition cube_tag_choiceMixin := CanChoiceMixin cube_tag_codeK.
Canonical cube_tag_choiceType := ChoiceType cube_tag cube_tag_choiceMixin.
Definition cube_tag_countMixin := CanCountMixin cube_tag_codeK.
Canonical cube_tag_countType := CountType cube_tag cube_tag_countMixin.

Fact cube_tag_enumP : Finite.axiom cube_tag_enum. Proof. by case. Qed.
Definition cube_tag_finMixin := FinMixin cube_tag_enumP.
Canonical cube_tag_finType := FinType cube_tag cube_tag_finMixin.

Definition cube_dart := cube_tag * G : Type.
Canonical cube_dart_eqType := [eqType of cube_dart].
Canonical cube_dart_choiceType := [choiceType of cube_dart].
Canonical cube_dart_countType := [countType of cube_dart].
Canonical cube_dart_finType := [finType of cube_dart].

Let tsI : cube_tag -> G -> cube_dart := @pair _ _.
Let tsE (u : cube_dart) : G := u.2.

Definition cube_edge (u : cube_dart) :=
  let: (o, x) := u in
  match o with
  | CTen => tsI CTnf (edge x)
  | CTf  => tsI CTe  (node (face x))
  | CTnf => tsI CTen (node (face x))
  | CTe  => tsI CTf  (edge x)
  | CTfe => tsI CTn  x
  | CTn  => tsI CTfe x
  end.

Definition cube_node (u : cube_dart) :=
  let: (o, x) := u in
  match o with
  | CTn  => tsI CTen (node x)
  | CTen => tsI CTfe x
  | CTf  => tsI CTnf (edge x)
  | CTnf => tsI CTe  (node (face x))
  | CTe  => tsI CTf  x
  | CTfe => tsI CTn  (face (edge x))
  end.

Definition cube_face (u : cube_dart) :=
  let: (o, x) := u in
  match o with
  | CTn  => tsI CTen x
  | CTen => tsI CTf  x
  | CTf  => tsI CTnf x
  | CTnf => tsI CTn  (face x)
  | CTe  => tsI CTe  (edge x)
  | CTfe => tsI CTfe (node x)
  end.

Fact cube_cancel3 : cancel3 cube_edge cube_node cube_face.
Proof. by do 2![case]=> x; rewrite /= ?faceK ?edgeK ?nodeK. Qed.
Let qmap := Hypermap cube_cancel3.

Definition cube := locked qmap.

Lemma plain_cube : plain cube.
Proof.
unlock cube; apply/plainP => u _.
by case: u; case; split; rewrite //= ?edgeK ?faceK ?nodeK.
Qed.

Lemma cubic_cube : cubic cube.
Proof.
unlock cube; apply/cubicP=> u _.
by case: u; case; split; rewrite //= ?edgeK ?faceK ?nodeK.
Qed.

Let aQe := [pred u : qmap | u.1 == CTe].
Let aQn := [pred u : qmap | u.1 == CTfe].
Let aQf := [predC [predU aQe & aQn]].

Let qf : rel qmap := frel cube_face.

Let qfC : connect_sym qf. Proof. exact (@cfaceC qmap). Qed.

Let qFaQe : closed qf aQe.
Proof.
by apply: (intro_closed qfC) => [[o x] v Dv]; rewrite -((_ =P v) Dv); case o.
Qed.

Let qFaQn : closed qf aQn.
Proof.
by apply: (intro_closed qfC) => [[o x] v Dv]; rewrite -((_ =P v) Dv); case o.
Qed.

Let qFaQf : closed qf aQf.
Proof.
by move=> u v uFv; rewrite 3!inE /= [u \in _](qFaQe uFv) [u \in _](qFaQn uFv).
Qed.

Let qfAe : fun_adjunction (tsI CTe) cube_face edge aQe.
Proof.
apply: (strict_adjunction cedgeC qFaQe) => // [x y [Dx]|] //.
by apply/subsetP => [[o x]]; rewrite !inE /= => /eqP->; apply (codom_f _ x).
Qed.

Let qfAn : fun_adjunction (tsI CTfe) cube_face node aQn.
Proof.
apply: (strict_adjunction cnodeC qFaQn) => // [x y [Dx]|] //.
by apply/subsetP => [[o x]]; rewrite !inE /= => /eqP->; apply (codom_f _ x).
Qed.

Let qfAf : fun_adjunction (tsI CTnf) cube_face face aQf.
Proof.
apply: (intro_adjunction cfaceC qFaQf (fun x _ => tsE x)) => [[o x] a_ox | x].
  split=> [|v _ /(_ =P v) <-{v}].
    by case: o a_ox => // _; do 4!rewrite (@cface1 qmap) //.
  by case: o a_ox => // _; rewrite fconnect1.
by split=> // _ /eqP <-; rewrite 4!(@cface1 qmap).
Qed.

Lemma genus_cube : genus cube = genus G.
Proof.
move: plain_cube cubic_cube; unlock cube => plainQ cubicQ.
have oQ: #|qmap| = 6 * #|G| by rewrite card_prod cardT enumT unlock.
have oEQ: fcard edge qmap = 3 * #|G|.
  apply/eqP; rewrite -(@eqn_pmul2l 2) // mulnA mulnC -oQ.
  by rewrite (fcard_order_set edgeI) //; apply/subsetP.
have oNQ: fcard node qmap = 2 * #|G|.
  apply/eqP; rewrite -(@eqn_pmul2l 3) // mulnA mulnC -oQ.
  by rewrite (fcard_order_set nodeI) //; apply/subsetP.
have oFeQ: fcard edge G = n_comp qf aQe.
  exact: etrans (esym (adjunction_n_comp _ qfC cedgeC qFaQe qfAe)).
have oFnQ: fcard node G = n_comp qf aQn.
  exact: etrans (esym (adjunction_n_comp _ qfC cnodeC qFaQn qfAn)).
have oFfQ: fcard face G = n_comp qf aQf.
  exact: etrans (esym (adjunction_n_comp _ qfC cfaceC qFaQf qfAf)).
have{oFeQ oFnQ oFfQ} oFQ: fcard face qmap = Euler_rhs G.
  rewrite /Euler_rhs oFeQ -[fcard _ _](cardID aQe); congr (_ + _).
    by apply: eq_card => u; rewrite !inE -andbA.
  rewrite -(cardID aQn) oFnQ oFfQ; congr (_ + _); apply: eq_card => u.
    by rewrite !inE -!andbA /= !andbA; apply: andb_id2r => /eqP->.
  by rewrite !inE andbT andbCA andbA -negb_or andbC.
suffices{oQ oEQ oNQ oFQ} oGQ: n_comp glink qmap = n_comp glink G.
  rewrite {1}/genus /Euler_lhs /Euler_rhs oQ oEQ oNQ oFQ oGQ.
  by rewrite mulSn 2!addnA -mulnDl addnC subnDl.
have g1eq y g_y G x := @same_connect1 _ _ (@glinkC G) x (y G x) (g_y G x).
have{g1eq} g1eq := (g1eq _ glinkE, g1eq _ glinkN, g1eq _ glinkF).
have [[cGG cGQ] [[g1e g1n] g1f]] := (@clinkC G, @clinkC qmap, g1eq).
rewrite -!(eq_n_comp (@clink_glink _)) (adjunction_n_comp (tsI CTnf) _ cGG) //.
apply: (intro_adjunction _ _ (fun x _ => tsE x)) => // [u _ | x _].
  split=> [|v _]; last first.
    rewrite clink_glink => /clinkP[->{u} | <-{v}].
      by case: v => [[] v] //=; rewrite -!g1eq.
    by case: u => [[] u] //=; rewrite glinkC -g1eq.
  case: u => o x /=; pose gQx o1 := gcomp (tsI o1 x : qmap) (tsI CTnf x).
  have gQx_e: gQx CTe by rewrite /gQx g1n g1f.
  have gQx_fe: gQx CTfe by rewrite /gQx g1e 3!g1f.
  by rewrite (@clink_glink qmap); case: o; do 3!rewrite // g1f.
split=> // y; rewrite (@clink_glink qmap).
case/clinkP=> [->{x} | <-{y}]; last by rewrite 4!g1f.
apply: (@connect_trans _ _ (tsI CTn y)); last by rewrite 3!(g1f qmap).
by rewrite (@glinkC qmap) (g1n qmap) 2!(g1f qmap).
Qed.

Lemma planar_cube : planar cube = planar G.
Proof. by rewrite /planar genus_cube. Qed.

Lemma cube_colorable : four_colorable cube -> four_colorable G.
Proof.
unlock cube => [[k [kE kF]]]; exists (k \o (tsI CTnf)); split=> x.
  apply: contraFF (kE (tsI CTnf (edge x))) => /eqcP/= ->.
  by rewrite edgeK -2!(eqcP (kF _)).
by apply/eqcP/esym; rewrite /= -4!(eqcP (kF _)).
Qed.

Lemma bridgeless_cube : bridgeless cube = bridgeless G.
Proof.
have [_ qfEf] := qfAf; unlock cube; congr (is_true (~~ _)).
apply/existsP/existsP=> [[u uFeu] | [x xFex]]; last first.
  by exists (tsI CTen x); rewrite 2!cface1 -qfEf.
case Du: u uFeu (closed_connect qFaQf uFeu) => [[] //= x] uFeu _.
  by exists x; rewrite 2!(@cface1 qmap) -qfEf in uFeu.
exists (node (face x)); rewrite faceK.
by rewrite (@cfaceC qmap) 2!cface1 -qfEf in uFeu.
Qed.

End Cube.

