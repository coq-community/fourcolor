(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype path fingraph.
From fourcolor
Require Import hypermap color geometry.

(******************************************************************************)
(*    These "parts" are patterns for performing local matching on maps.       *)
(* Specifically, a part specifies ranges of arities for darts in the second   *)
(* neighbourhood of some match anchor x, using the "prange" type below to     *)
(* specify ranges.                                                            *)
(*   A part is broken into a sequence of subparts, each specifying arities in *)
(* a basic sector of the second neighbourhood of x. Subparts are listed       *)
(* counterclockwise around a "hub" (the face orbit of x); we also use part    *)
(* sublists (represented with the same type) to specify arities in larger     *)
(* sectors around the hub. Each subpart comprises a "spoke" (a face adjacent  *)
(* to the hub; the spoke of the first subpart is the face orbit of edge x),   *)
(* a "hat" (the face adjacent to the spokes of this subpart and the previous  *)
(* one, different from the hub; the hat of the first subpart is the face of   *)
(* edge (face (edge x))), and "fans" (the faces adjacent only to the spoke of *)
(* the subpart, numbered in a counterclockwise arc that starts from the hat). *)
(*   The hub and subparts are a partition of the second neighborhood of x; a  *)
(* subpart does not contain the hat of the next (counterclockwise) one, even  *)
(* though this hat is adjacent to the subpart's spoke.                        *)
(*   Because parts are created and traversed in the inner loop of the         *)
(* unavoidability checks their representation is somewhat optimised. The list *)
(* structure is merged into the record structure; there are four different    *)
(* kinds of parts, according to the number of (known) fans. The spoke arity   *)
(* is always fixed when there are known fans (e.g., if there are two known    *)
(* fans, the spoke is a heptagon). The converse isn't true, in fact we never  *)
(* use the explicit fan forms when there are no nontrivial fan constraints,   *)
(* as this simplifies the converse part computation.                          *)
(*   Parts are used throughout the unavoidability check: to specify the arity *)
(* discharging procedure and its rules, to enumerate all possible second      *)
(* neighbourhoods, to check for the presence of a reducible configuration.    *)
(*   If x fits p, we check whether a discharge rule applies to x by comparing *)
(* p to the part r of the rule; we force the application of the rule by       *)
(* intersecting p with r (function meet_part below); we check whether a       *)
(* reducible map appears near x by applying its quiz to the part ranges in p  *)
(* (library redpart).                                                         *)
(*   This file defines the following types:                                   *)
(*   prange == type enumerating all the possible arity ranges for non-hub     *)
(*             faces in a part; constructor PrMN means range [M, N], and      *)
(*             a prange coerces to the corresponding pred nat. We use N=9     *)
(*             to indicate an unbounded range, so Pr59 is the free            *)
(*             (unconstrained) range for pentagonal maps.                     *)
(* part_rel == type enumerating prange and part set comparison outcomes, with *)
(*             constructors Pdisjoint, Psubset and Pstraddle. A part_rel      *)
(*             coerces to a bool -> bool function that maps the result of a   *)
(*             membership test of an element of the first set in the second   *)
(*             one to its expected outcome (e.g., the identity function for   *)
(*             Pstraddle, and the constant true function for Psubset).        *)
(* subpart_loc == type enumerating all possible faces in a given subpart,     *)
(*             with constructors Pspoke, Phat and Pfan[1-3]; a subpart_loc i  *)
(*             coerces to a function mapping the corresponding hub dart to a  *)
(*             dart in the corresponding face, e.g., Pspoke _ x = edge x.     *)
(* --> Import SublocSyntax :: defines shorthand (s, h, f[1-3]) for            *)
(* subpart_loc constructors (Pspoke, Phat, Pfan[1-3]).                        *)
(*     part == type for parts and part sectors, represented as sequences of   *)
(*             subparts, with constructors Pnil for the empty sector, Pcons   *)
(*             for adding a subpart with no fans, and PconsN, N in [6-8] for  *)
(*             adding a subpart with spoke arity N and N-5 fans.              *)
(* --> Import PartSyntax :: activates the Notation for parts, e.g.,           *)
(*   Part $[6+] 7?8 $ 7- $[* 5] 6 $                                           *)
(*       denotes Pcons Pr78 Pr69 (Pcons Pr57 Pr59 (Pcons6 Pr59 Pr55 Pnil))    *)
(*     Grammar:             Part <part>                                       *)
(*               <part> ::= <subpart>* $                                      *)
(*            <subpart> ::= $[<range>+] <range> | $ <range>                   *)
(*                          in $[h f1 f2] s, s is the spoke range, h the hat  *)
(*                          range, and f1, f2 the fan ranges; s must be M > 5 *)
(*                          for f(s-5) to be present; $ s means $[*] s.       *)
(*              <range> ::= * | M | M?N | M+ | N- with M < N in 5..8          *)
(*                 meaning  Pr59, PrMM, PrMn, PrM9, Pr59, respectively.       *)
(*   pcons_s s p == add a subpart with spoke range s and free hat range to p. *)
(*      pcons_ n == part consisting of n free subparts (free spoke and hat    *)
(*                  ranges), which will fit any dart with arity n.            *)
(* Set comparison logic operation:                                            *)
(*    notPsubset c == Pstraddle if c = Psubset, else c.                       *)
(*  meet_prel c c' == the relation for products A x A' and B x B' of sets     *)
(*                    where A and B, A' and B' compare as c, c' : part_rel,   *)
(*                    respectively.                                           *)
(* Range operations:                                                          *)
(*   cmp_range r1 r2 == set comparison of r1 r2 : prange; returns a part_rel. *)
(*  meet_range r1 r2 == prange intersection of non-disjoint r1 r2 : prange.   *)
(*       prange_lo n == the prange [5,n].                                     *)
(*       prange_hi n == the prange [n+1,9].                                   *)
(*   good_rsplit k r <=> the prange r can be split at k, as it straddles      *)
(*                      [5,k], i.e., i <= k < j when r is the prange [i,j].   *)
(* split_range k lo r == the prange [i,k] if lo, and [k+1,j] if ~~ lo, when   *)
(*                      r is the prange [i,j], with i <= k < j.               *)
(* Part accessors:                                                            *)
(* get_spoke p == arity range for the first spoke in p : part.                *)
(* get_hat p == arity range for the first hat in p : part.                    *)
(* next_hat h0 p == range for the first hat in p, defaulting to h0 for Pnil.  *)
(* get_fanN[lr] p == arity range for the Nth (N in [1-3]) fan of the first    *)
(*             subpart of p, counting cLockwise/counteRclockwise, resp. Note  *)
(*             this counts right / left with respect to the position of the   *)
(*             PconsN arguments.                                              *)
(* Part semantics :                                                           *)
(*      size_part p == size (hub arity) of p.                                 *)
(*        fitp x p <=> the first spokes of x fit the (sector) part p.         *)
(*  exact_fitp x p <=> x fits p, including at the hub: arity x = size_part p. *)
(* tight_fitp x (u, p) <=> x fits sector part p, and the arity of x is in the *)
(*                     prange u (see converse_part above).                    *)
(*   cmp_part p1 p2 == set comparison of p1 p2 : part, viewed as sets of      *)
(*                     pointed maps; returns a part_rel.                      *)
(* part_update fp i <-> fp is a valid part constructor at i : subpart_loc:    *)
(*                     fp r p adds one subpart to p, and any x fitting sector *)
(*                     fp r p fits fp r' p iff arity (i _ x) in prange r'.    *)
(* Part operations:                                                           *)
(*  meet_part p q == part intersection of part p with part sector q - thus    *)
(*                   assuming size_part p >= size_part q, and p and q are not *)
(*                   disjoint.                                                *)
(*  drop_part n p == the sector left by dropping the n first subparts of p.   *)
(*  take_part n p == the sector consisting of the n first subparts of p.      *)
(* cat_part p1 p2 == part concatenation of p1 p2 : part.                      *)
(*   rot_part n p == p rotated n times, provided n < size_part p.             *)
(*     rev_part p == p : part reversed; NOT a mirror image, as subparts are   *)
(*                   not modified; used to implement zippers in redpart.v.    *)
(*  catrev_part p1 p2 == part concatenation of p1 reversed, and p2.           *)
(*  mirror_part p == mirror image (reflection across the first spoke) of p.   *)
(* converse_part p == converse of part p - reflection across the edge between *)
(*                   the hub and THIRD spoke. This returns a pair of a prange *)
(*                   constraint for the new hub and a sector part whose first *)
(*                   spoke is the first hat of p, since the arity of the      *)
(*                   first spoke of p might not be fixed.                     *)
(* --> The converse_part operation is only used to compute converse discharge *)
(* rules, and is over-approximate: constraints of p that fall outside of the  *)
(* second neighbourhood of its first spoke must be ignored, and we also cut   *)
(* out corner cases not needed by the data in discharge.v. The approximation  *)
(* only affects the hubcap computations, is provably safe, and empirically    *)
(* complete as approximations don't actually arise with the discharge.v data. *)
(*     inv_face2 x := face^-2 x (used in the converse_part specification).    *)
(* Part refinement:                                                           *)
(*  fitc i j k x <=> k is greater than the arity of i _ (face^j x), which     *)
(*                   corresponds to sublocation i : subloc_part of subpart j. *)
(* good_split i j k p <=> the arity range r at sublocation i in subpart j of  *)
(*                   part p can be split at k.                                *)
(* split_part i j k lo p == part p where the arity range r at sublocation i   *)
(*                   in subpart j has been replaced split_range k lo r.       *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* PrMN stands for the range M..N; N=9 actually means infinity, e.g, Pr59 *)
(* means any arity greater than or equal to 5, that is any arity in a     *)
(* pentagonal map.                                                        *)
Inductive prange :=
  | Pr55 | Pr66 | Pr77 | Pr88 | Pr99
  | Pr56 | Pr67 | Pr78 | Pr89
  | Pr57 | Pr68 | Pr79
  | Pr58 | Pr69
  | Pr59.

Inductive part : Set :=
  | Pnil
  | Pcons (spk hat : prange) of part
  | Pcons6 (hat fan1 : prange) of part
  | Pcons7 (hat fan1 fan2 : prange) of part
  | Pcons8 (hat fan1 fan2 fan3 : prange) of part.

Inductive subpart_loc := Pspoke | Phat | Pfan1 | Pfan2 | Pfan3.

(* These should be in the PartSyntax module, but need to appear here because *)
(* of a regression in the module scope of grammar rules (see below).         *)
Notation "5" := 5 (at level 0) : nat_scope.
Notation "6" := 6 (at level 0) : nat_scope.
Notation "7" := 7 (at level 0) : nat_scope.
Notation "8" := 8 (at level 0) : nat_scope.

Module PartSyntax.

Notation "5" := Pr55 (at level 0) : prange_scope.
Notation "6" := Pr66 (at level 0) : prange_scope.
Notation "7" := Pr77 (at level 0) : prange_scope.
Notation "8" := Pr88 (at level 0) : prange_scope.

Notation "*" := Pr59.
Notation "6 +" := Pr69 (at level 0, format "6 +") : prange_scope.
Notation "7 +" := Pr79 (at level 0, format "7 +") : prange_scope.
Notation "8 +" := Pr89 (at level 0, format "8 +") : prange_scope.
Notation "9 +" := Pr99 (at level 0, format "9 +") : prange_scope.

Notation "6 -" := Pr56 (at level 0, format "6 -") : prange_scope.
Notation "7 -" := Pr57 (at level 0, format "7 -") : prange_scope.
Notation "8 -" := Pr58 (at level 0, format "8 -") : prange_scope.

Notation "6 ? 7" := Pr67 (at level 0, format "6 ? 7") : prange_scope.
Notation "6 ? 8" := Pr68 (at level 0, format "6 ? 8") : prange_scope.
Notation "7 ? 8" := Pr78 (at level 0, format "7 ? 8") : prange_scope.

Bind Scope part_scope with part.
Delimit Scope part_scope with part.
Delimit Scope prange_scope with prange.

Arguments Pcons (spk hat)%prange _%part.
Arguments Pcons6 (hat fan1)%prange _%part.
Arguments Pcons7 (hat fan1 fan2)%prange _%part.
Arguments Pcons8 (hat fan1 fan2 fan3)%prange _%part.

Undelimit Scope part_scope.
Undelimit Scope prange_scope.

Definition Part (p : part) := p.

(* The obnoxious $ help overcome parsing limitations of Coq. *)
Notation "$" := Pnil (at level 8) : part_scope.
Notation "$[ h ] s p" := (Pcons s h p)
  (at level 8, s, h at level 0, p at level 9,
   format "$[ h ]  s  p") : part_scope.
Notation "$ s p" := (Pcons s * p)
  (at level 8, s at level 0, p at level 9,
   format "$  s  p") : part_scope.
Notation "$[ h f1 ] 6 p" := (Pcons6 h f1 p)
  (at level 8, h, f1 at level 0, p at level 9,
   format "$[ h  f1 ]  6  p") : part_scope.
Notation "$[ h f1 f2 ] 7 p" := (Pcons7 h f1 f2 p)
  (at level 8, h, f1, f2 at level 0, p at level 9,
   format "$[ h f1 f2 ]  7  p") : part_scope.
Notation "$[ h f1 f2 f3 ] 8 p" := (Pcons8 h f1 f2 f3 p)
  (at level 8, h, f1, f2, f3 at level 0, p at level 9,
   format "$[ h f1 f2 f3 ]  8  p") : part_scope.

End PartSyntax.

Module SublocSyntax.

Definition s := Pspoke.
Definition h := Phat.
Definition f1 := Pfan1.
Definition f2 := Pfan2.
Definition f3 := Pfan3.

End SublocSyntax.

(* Shorthand for making (mostly) empty parts.                                 *)

Definition pcons_s s := Pcons s Pr59.

Definition pcons_ n := iter n (Pcons Pr59 Pr59) Pnil.

(* Range semantics.                                                           *)

Definition mem_range r :=
  match r return pred nat with
  | Pr55 => pred1 5
  | Pr66 => pred1 6
  | Pr77 => pred1 7
  | Pr88 => pred1 8
  | Pr56 => pred2 5 6
  | Pr67 => pred2 6 7
  | Pr78 => pred2 7 8
  | Pr57 => pred3 5 6 7
  | Pr68 => pred3 6 7 8
  | Pr58 => pred4 5 6 7 8
  | Pr59 => leq 5
  | Pr69 => leq 6
  | Pr79 => leq 7
  | Pr89 => leq 8
  | Pr99 => leq 9
  end.

Coercion mem_range : prange >-> pred.

(* Part/range comparison results; Pstraddle covers all the remaining cases,  *)
(* including when the left hand side stricly contains the right hand side.   *)
(* We use the result of a comparison by applying it to a "fit" predicate.    *)

Inductive part_rel := Pdisjoint | Pstraddle | Psubset.

Definition apply_part_rel pr b :=
  match pr with
  | Pdisjoint => false
  | Psubset => true
  | _ => b
  end.

Coercion apply_part_rel : part_rel >-> Funclass.

Definition notPsubset c := if c is Psubset then Pstraddle else c.

Definition meet_prel c c' :=
  match c with
  | Pdisjoint => c
  | Psubset => c'
  | Pstraddle => notPsubset c'
  end.

(* Range comparison and meet.                                                 *)

Definition cmp_range r r' :=
  match r', r with
  | Pr59, _    => Psubset
  | _ ,   Pr59 => Pstraddle
  | Pr69, Pr55 => Pdisjoint
  | Pr69, Pr56 => Pstraddle
  | Pr69, Pr57 => Pstraddle
  | Pr69, Pr58 => Pstraddle
  | Pr69, _    => Psubset
  | Pr55, Pr69 => Pdisjoint
  | _,    Pr69 => Pstraddle
  | Pr58, Pr99 => Pdisjoint
  | Pr58, Pr89 => Pstraddle
  | Pr58, Pr79 => Pstraddle
  | Pr58, _    => Psubset
  | Pr99, Pr58 => Pdisjoint
  | _,    Pr58 => Pstraddle
  | Pr55, Pr55 => Psubset
  | Pr55, Pr56 => Pstraddle
  | Pr55, Pr57 => Pstraddle
  | Pr55, _    => Pdisjoint
  | Pr56, Pr55 => Psubset
  | Pr57, Pr55 => Psubset
  | _,    Pr55 => Pdisjoint
  | Pr99, Pr99 => Psubset
  | Pr99, Pr89 => Pstraddle
  | Pr99, Pr79 => Pstraddle
  | Pr99, _    => Pdisjoint
  | Pr89, Pr99 => Psubset
  | Pr79, Pr99 => Psubset
  | _,    Pr99 => Pdisjoint
  | Pr66, Pr66 => Psubset
  | Pr66, Pr56 => Pstraddle
  | Pr66, Pr57 => Pstraddle
  | Pr66, Pr67 => Pstraddle
  | Pr66, Pr68 => Pstraddle
  | Pr66, _    => Pdisjoint
  | Pr56, Pr66 => Psubset
  | Pr57, Pr66 => Psubset
  | Pr67, Pr66 => Psubset
  | Pr68, Pr66 => Psubset
  | _,    Pr66 => Pdisjoint
  | Pr88, Pr88 => Psubset
  | Pr88, Pr89 => Pstraddle
  | Pr88, Pr79 => Pstraddle
  | Pr88, Pr78 => Pstraddle
  | Pr88, Pr68 => Pstraddle
  | Pr88, _    => Pdisjoint
  | Pr89, Pr88 => Psubset
  | Pr79, Pr88 => Psubset
  | Pr78, Pr88 => Psubset
  | Pr68, Pr88 => Psubset
  | _,    Pr88 => Pdisjoint
  | Pr77, Pr77 => Psubset
  | Pr77, Pr56 => Pdisjoint
  | Pr77, Pr89 => Pdisjoint
  | Pr77, _    => Pstraddle
  | Pr56, Pr77 => Pdisjoint
  | Pr89, Pr77 => Pdisjoint
  | _,    Pr77 => Psubset
  | Pr68, Pr68 => Psubset
  | Pr68, Pr67 => Psubset
  | Pr68, Pr78 => Psubset
  | Pr68, _    => Pstraddle
  | _,    Pr68 => Pstraddle
  | Pr67, Pr67 => Psubset
  | Pr67, Pr89 => Pdisjoint
  | Pr67, _    => Pstraddle
  | Pr57, Pr67 => Psubset
  | Pr89, Pr67 => Pdisjoint
  | _,    Pr67 => Pstraddle
  | Pr78, Pr78 => Psubset
  | Pr78, Pr56 => Pdisjoint
  | Pr78, _    => Pstraddle
  | Pr79, Pr78 => Psubset
  | Pr56, Pr78 => Pdisjoint
  | _,    Pr78 => Pstraddle
  | Pr89, Pr56 => Pdisjoint
  | Pr79, Pr56 => Pdisjoint
  | _,    Pr56 => Psubset
  | Pr56, Pr57 => Pstraddle
  | Pr56, _    => Pdisjoint
  | Pr57, Pr89 => Pdisjoint
  | _,    Pr89 => Psubset
  | Pr89, Pr79 => Pstraddle
  | Pr89, _    => Pdisjoint
  | Pr57, Pr57 => Psubset
  | Pr79, Pr79 => Psubset
  | _,    _    => Pstraddle
  end.

Definition meet_range r r' :=
  match r', r with
  | Pr56, Pr67 => Pr66
  | Pr56, Pr68 => Pr66
  | Pr56, Pr69 => Pr66
  | Pr67, Pr56 => Pr66
  | Pr68, Pr56 => Pr66
  | Pr69, Pr56 => Pr66
  | Pr57, Pr78 => Pr77
  | Pr57, Pr79 => Pr77
  | Pr67, Pr78 => Pr77
  | Pr67, Pr79 => Pr77
  | Pr78, Pr57 => Pr77
  | Pr79, Pr57 => Pr77
  | Pr78, Pr67 => Pr77
  | Pr79, Pr67 => Pr77
  | Pr89, Pr58 => Pr88
  | Pr89, Pr68 => Pr88
  | Pr89, Pr78 => Pr88
  | Pr58, Pr89 => Pr88
  | Pr68, Pr89 => Pr88
  | Pr78, Pr89 => Pr88
  | Pr57, Pr68 => Pr67
  | Pr57, Pr69 => Pr67
  | Pr68, Pr57 => Pr67
  | Pr69, Pr57 => Pr67
  | Pr79, Pr58 => Pr78
  | Pr79, Pr68 => Pr78
  | Pr58, Pr79 => Pr78
  | Pr68, Pr79 => Pr78
  | Pr58, Pr69 => Pr68
  | Pr69, Pr58 => Pr68
  | Pr59, _    => r
  | _,    Pr59 => r'
  | Pr58, _    => r
  | Pr69, _    => r
  | _,    Pr58 => r'
  | _,    Pr69 => r'
  | Pr57, _    => r
  | Pr68, _    => r
  | Pr79, _    => r
  | _,    Pr57 => r'
  | _,    Pr68 => r'
  | _,    Pr79 => r'
  | Pr56, _    => r
  | Pr67, _    => r
  | Pr78, _    => r
  | Pr89, _    => r
  | _,    Pr56 => r'
  | _,    Pr67 => r'
  | _,    Pr78 => r'
  | _,    _    => r'
  end.

Lemma mem_cmp_range (r1 : prange) n :
  r1 n -> forall r2 : prange, r2 n = cmp_range r1 r2 (r2 n).
Proof. by do 9?case: n => [|n]; case: r1 => // _; case. Qed.

Lemma mem_meet_range (r1 r2 : prange) n : r1 n -> r2 n -> meet_range r1 r2 n.
Proof. by do 9?case: n => [|n]; case: r1 => // _; case: r2. Qed.

(* List-like operations on parts. Most also have a geometric meaning, exept   *)
(* "rev_part", which is just a subroutine for the implementation of zipped    *)
(* parts in redpart.v.                                                        *)

Fixpoint size_part (p : part) : nat :=
  match p with
  | Pnil              => 0
  | Pcons _ _ p'      => (size_part p').+1
  | Pcons6 _ _ p'     => (size_part p').+1
  | Pcons7 _ _ _ p'   => (size_part p').+1
  | Pcons8 _ _ _ _ p' => (size_part p').+1
  end.

Fixpoint drop_part (n : nat) (p : part) {struct n} : part :=
  match n, p with
  | n'.+1, Pcons _ _ p'      => drop_part n' p'
  | n'.+1, Pcons6 _ _ p'     => drop_part n' p'
  | n'.+1, Pcons7 _ _ _  p'  => drop_part n' p'
  | n'.+1, Pcons8 _ _ _ _ p' => drop_part n' p'
  | _,     _                 => p
  end.

Fixpoint take_part (n : nat) (p : part) {struct n} : part :=
  match n, p with
  | n'.+1, Pcons s h p'         => Pcons s h (take_part n' p')
  | n'.+1, Pcons6 h f1 p'       => Pcons6 h f1 (take_part n' p')
  | n'.+1, Pcons7 h f1 f2 p'    => Pcons7 h f1 f2 (take_part n' p')
  | n'.+1, Pcons8 h f1 f2 f3 p' => Pcons8 h f1 f2 f3 (take_part n' p')
  | _,     _                    => Pnil
  end.

Fixpoint cat_part (p q : part) : part :=
  match p with
  | Pcons s h p'         => Pcons s h (cat_part p' q)
  | Pcons6 h f1 p'       => Pcons6 h f1 (cat_part p' q)
  | Pcons7 h f1 f2 p'    => Pcons7 h f1 f2 (cat_part p' q)
  | Pcons8 h f1 f2 f3 p' => Pcons8 h f1 f2 f3 (cat_part p' q)
  | Pnil                 => q
  end.

Definition rot_part n p := cat_part (drop_part n p) (take_part n p).

Lemma size_cat_part p1 p2 :
  size_part (cat_part p1 p2) = size_part p1 + size_part p2.
Proof. by apply/eqP; elim: p1. Qed.

Lemma size_drop_part n p : size_part (drop_part n p) = size_part p - n.
Proof. by elim: n p => [|n IHn] []. Qed.

Lemma cat_take_drop_part n p :
  cat_part (take_part n p) (drop_part n p) = p.
Proof. by elim: n p => [|n IHn] [] //= *; rewrite IHn. Qed.

Lemma size_rot_part n p : size_part (rot_part n p) = size_part p.
Proof. by rewrite -{2}(cat_take_drop_part n p) !size_cat_part addnC. Qed.

Fixpoint catrev_part (p1 p2 : part) : part :=
  match p1 with
  | Pnil                  => p2
  | Pcons s h p1'         => catrev_part p1' (Pcons s h p2)
  | Pcons6 h f1 p1'       => catrev_part p1' (Pcons6 h f1 p2)
  | Pcons7 h f1 f2 p1'    => catrev_part p1' (Pcons7 h f1 f2 p2)
  | Pcons8 h f1 f2 f3 p1' => catrev_part p1' (Pcons8 h f1 f2 f3 p2)
  end.

Definition rev_part p := catrev_part p Pnil.

Lemma catrev_part_eq p1 p2 : catrev_part p1 p2 = cat_part (rev_part p1) p2.
Proof.
rewrite /rev_part -{1}[p2]/(cat_part Pnil p2); move: p1 Pnil p2.
by elim=> //= [s h | h f1 | h f1 f2 | h f1 f2 f3] p1 IHp p2 p3; rewrite -IHp.
Qed.

Lemma size_rev_part p : size_part (rev_part p) = size_part p.
Proof.
rewrite /rev_part -[size_part p]addn0 -[0]/(size_part Pnil).
elim: p Pnil => //= [s h|h f1|h f1 f2|h f1 f2 f3] p1 IHp p2;
  by rewrite addSnnS IHp.
Qed.

Lemma rev_rev_part p : rev_part (rev_part p) = p.
Proof.
rewrite {2}/rev_part -{2}[p]/(catrev_part Pnil p); move: p Pnil.
by elim=> //= [s h|h f1|h f1 f2|h f1 f2 f3] p IHp p'; rewrite IHp.
Qed.

(******************************************************************************)
(* Accessors; except for "next_hat", they assume the part is not nil.         *)
(* The accessors are mostly used for zipped parts, where we also need to      *)
(* access the fans in clockwise order, so we have both "r" (counterclockwise) *)
(* and "l" (clockwise) versions of the fan accessors. We don't provide update *)
(* functions because both here (for split_part) and in redpart, update is     *)
(* bundeled with another operation.                                           *)
(******************************************************************************)

Definition get_spoke p :=
  match p with
  | Pcons s _ _      => s
  | Pcons6 _ _ _     => Pr66
  | Pcons7 _ _ _ _   => Pr77
  | Pcons8 _ _ _ _ _ => Pr88
  | _                => Pr59
  end.

Definition next_hat h0 p :=
  match p with
  | Pnil             => h0
  | Pcons _ h _      => h
  | Pcons6 h _ _     => h
  | Pcons7 h _ _ _   => h
  | Pcons8 h _ _ _ _ => h
  end.

Definition get_hat := Eval compute in next_hat Pr59.

Definition get_fan1r p :=
  match p with
  | Pcons6 _ f1 _     => f1
  | Pcons7 _ f1 _ _   => f1
  | Pcons8 _ f1 _ _ _ => f1
  | _               => Pr59
  end.

Definition get_fan2r p :=
  match p with
  | Pcons7 _ _ f2 _   => f2
  | Pcons8 _ _ f2 _ _ => f2
  | _               => Pr59
  end.

Definition get_fan3r p :=
  match p with
  | Pcons8 _ _ _ f3 _ => f3
  | _               => Pr59
  end.

Definition get_fan1l p :=
  match p with
  | Pcons6 _ f1 _     => f1
  | Pcons7 _ _ f2 _   => f2
  | Pcons8 _ _ _ f3 _ => f3
  | _               => Pr59
  end.

Definition get_fan2l p :=
  match p with
  | Pcons7 _ f1 _ _   => f1
  | Pcons8 _ _ f2 _ _ => f2
  | _               => Pr59
  end.

Definition get_fan3l p :=
  match p with
  | Pcons8 _ f1 _ _ _ => f1
  | _               => Pr59
  end.

(* Mirror image : reflection ACROSS the first spoke (exchanges second and     *)
(* last spoke faces).                                                         *)

Fixpoint mirror_part_rec (h0 : prange) (rp p : part) : part :=
  match p with
  | Pnil =>
    rp
  | Pcons s _ p' =>
    mirror_part_rec h0 (Pcons s (next_hat h0 p') rp) p'
  | Pcons6 _ f1 p'       =>
    mirror_part_rec h0 (Pcons6 (next_hat h0 p') f1 rp) p'
  | Pcons7 _ f1 f2 p'    =>
    mirror_part_rec h0 (Pcons7 (next_hat h0 p') f2 f1 rp) p'
  | Pcons8 _ f1 f2 f3 p' =>
    mirror_part_rec h0 (Pcons8 (next_hat h0 p') f3 f2 f1 rp) p'
  end.

Definition mirror_part p := mirror_part_rec (get_hat p) Pnil p.

Lemma size_mirror_part p : size_part (mirror_part p) = size_part p.
Proof.
rewrite /mirror_part -[size_part p]/(size_part Pnil + size_part p).
elim: p Pnil (get_hat p) => //= [s h|h f1|h f1 f2|h f1 f2 f3] p IHp q h0;
  by rewrite ?addn0 ?addnS ?IHp.
Qed.

Lemma mirror_mirror_part p : mirror_part (mirror_part p) = p.
Proof.
rewrite {2}/mirror_part; move Dh0: (get_hat p) => h0.
have Eh0: next_hat (if p is Pnil then Pr59 else h0) Pnil = next_hat h0 p.
  by rewrite -Dh0; case p.
transitivity (mirror_part_rec h0 p Pnil); last by [].
elim: p {Dh0}Pnil Eh0
  => [|s h p IHp|h f1 p IHp|h f1 f2 p IHp|h f1 f2 f3 p IHp] q /= Eh0;
  by rewrite ?IHp // /mirror_part /= ?Eh0 // -Eh0.
Qed.

(* Converse part: reflection ALONG the THIRD spoke (exchanges hub and third *)
(* spoke faces).                                                            *)

Definition conv_part12 p4 :=
  match p4 with
  | Pcons s2 s1 (Pcons h23 f2 _) =>
     match f2, s2 with
     | Pr59, _ => (h23, fun q => pcons_s s1 (pcons_s s2 q))
     | _, Pr55 => (h23, fun q => pcons_s s1 (Pcons Pr55 f2 q))
     | _, Pr66 => (h23, fun q => pcons_s s1 (Pcons6 Pr59 f2 q))
     | _, Pr77 => (h23, fun q => pcons_s s1 (Pcons7 Pr59 Pr59 f2 q))
     | _, _    => (Pr59, fun _ => Pnil)
     end
  | Pcons6 s1 h12 (Pcons h23 f21 _) =>
    (h23, fun q => pcons_s s1 (Pcons6 h12 f21 q))
  | Pcons7 s1 h12 f21 (Pcons h23 f22 _) =>
    (h23, fun q => pcons_s s1 (Pcons7 h12 f21 f22 q))
  | _ =>
   (Pr59, fun _ => Pnil)
  end.

Definition conv_part3 h23 p6 :=
  match p6 with
  | Pnil =>
    Pcons Pr55 h23
  | Pcons _ _ Pnil =>
    Pcons Pr66 h23
  | Pcons f31 _ (Pcons f32 _ Pnil) =>
    match f31, f32 with
    | Pr59, Pr59 => Pcons Pr77 h23
    | _,    _    => Pcons7 h23 f31 f32
    end
  | Pcons f31 _ (Pcons f32 _ (Pcons f33 _ Pnil)) =>
    Pcons8 h23 f31 f32 f33
  | _ =>
    fun _ => Pnil
  end.

Definition conv_part4 p1 :=
  match p1 with
  | Pcons h34 _ (Pcons s4 f41 _) =>
    match f41, s4 with
    | Pr59, _ => (Pr59, Pcons s4 h34)
    | _, Pr55 => (f41,  Pcons Pr55 h34)
    | _, Pr66 => (Pr59, Pcons6 h34 f41)
    | _, Pr77 => (Pr59, Pcons7 h34 f41 Pr59)
    | _, _    => (Pr59, fun _ => Pnil)
    end
  | Pcons h34 _ (Pcons6 f41 h45 _) =>
    (h45, Pcons6 h34 f41)
  | Pcons h34 _ (Pcons7 f41 f42 h45 _) =>
    (h45, Pcons7 h34 f41 f42)
  | _ =>
    (Pr59,  fun _ => Pnil)
  end.

Definition conv_part5 h45 p3 :=
  match p3 with
  | Pcons u s5 _      => (u,    Pcons s5 h45 Pnil)
  | Pcons7 s5 s6 s7 _ => (Pr77, Pcons s5 h45 (pcons_s s6 (pcons_s s7 Pnil)))
  | _                 => (Pr59, Pnil)
  end.

Definition converse_part p1 :=
  let (h45, q4) := conv_part4 p1 in
  let (u, q5) := conv_part5 h45 (drop_part 2 p1) in
  let (h23, q12) := conv_part12 (drop_part 3 p1) in
  let q3 := conv_part3 h23 (drop_part 5 p1) in
  (u, q12 (q3 (q4 q5))).

(******************************************************************************)
(* Part (and range) splitting with respect to a condition, i.e., a quadruple  *)
(* of a part location i, spoke index j, arity value k, and a boolean lo, true *)
(* if want to restrict the range at i[j] to arities lower than or equal to k, *)
(* and false if we want the arities greater than k. A split is "good" if it   *)
(* is nontrivial (k is in the range) and definite (if i is a fan location,    *)
(* the spoke below it has a definite arity that is large enough).             *)
(******************************************************************************)

Definition prange_lo k :=
  match k with
  | 5 => Pr55
  | 6 => Pr56
  | 7 => Pr57
  | 8 => Pr58
  | _ => Pr59
  end.

Definition prange_hi k :=
  match k with
  | 5 => Pr69
  | 6 => Pr79
  | 7 => Pr89
  | 8 => Pr99
  | _ => Pr59
  end.

Definition good_rsplit k r :=
  if cmp_range r (prange_lo k) is Pstraddle then true else false.

Definition split_range k (lo : bool) r :=
  meet_range ((if lo then prange_lo else prange_hi) k) r.

Lemma fit_split_range k r : good_rsplit k r ->
  forall lo a, split_range k lo r a = (lo (+) (k < a)) && r a.
Proof. by case: r => k_r [] a; move: k a k_r; do !case=> //. Qed.

Definition good_split i j k p :=
  match i, drop_part j p with
  | Pspoke, Pcons s _ _       => good_rsplit k s
  | Phat,   Pcons s h _       => good_rsplit k h
  | Phat,   Pcons6 h _ _      => good_rsplit k h
  | Phat,   Pcons7 h _ _ _    => good_rsplit k h
  | Phat,   Pcons8 h _ _ _ _  => good_rsplit k h
  | Pfan1,  Pcons6 _ f1 _     => good_rsplit k f1
  | Pfan1,  Pcons Pr66 _ _    => good_rsplit k Pr59
  | Pfan1,  Pcons7 _ f1 _ _   => good_rsplit k f1
  | Pfan1,  Pcons Pr77 _ _    => good_rsplit k Pr59
  | Pfan1,  Pcons8 _ f1 _ _ _ => good_rsplit k f1
  | Pfan1,  Pcons Pr88 _ _    => good_rsplit k Pr59
  | Pfan2,  Pcons7 _ _ f2 _   => good_rsplit k f2
  | Pfan2,  Pcons Pr77 _ _    => good_rsplit k Pr59
  | Pfan2,  Pcons8 _ _ f2 _ _ => good_rsplit k f2
  | Pfan2,  Pcons Pr88 _ _    => good_rsplit k Pr59
  | Pfan3,  Pcons8 _ _ _ f3 _ => good_rsplit k f3
  | Pfan3,  Pcons Pr88 _ _    => good_rsplit k Pr59
  | _,       _                => false
  end.

Definition split_part i j k lo p :=
  let p1 := take_part j p in
  let p2 := drop_part j p in
  let mkp df r p' := cat_part p1 (df (split_range k lo r) p') in
  match i, p2 with
  | Pspoke, Pcons s h p'         => mkp (fun r => Pcons r h) s p'
  | Phat,   Pcons s h p'         => mkp (fun r => Pcons s r) h p'
  | Phat,   Pcons6 h f1 p'       => mkp (fun r => Pcons6 r f1) h p'
  | Phat,   Pcons7 h f1 f2 p'    => mkp (fun r => Pcons7 r f1 f2) h p'
  | Phat,   Pcons8 h f1 f2 f3 p' => mkp (fun r => Pcons8 r f1 f2 f3) h p'
  | Pfan1,  Pcons6 h f1 p'       => mkp (fun r => Pcons6 h r) f1 p'
  | Pfan1,  Pcons Pr66 h p'      => mkp (fun r => Pcons6 h r) Pr59 p'
  | Pfan1,  Pcons7 h f1 f2 p'    => mkp (fun r => Pcons7 h r f2) f1 p'
  | Pfan1,  Pcons Pr77 h p'      => mkp (fun r => Pcons7 h r Pr59) Pr59 p'
  | Pfan1,  Pcons8 h f1 f2 f3 p' => mkp (fun r => Pcons8 h r f2 f3) f1 p'
  | Pfan1,  Pcons Pr88 h p'      => mkp (fun r => Pcons8 h r Pr59 Pr59) Pr59 p'
  | Pfan2,  Pcons7 h f1 f2 p'    => mkp (fun r => Pcons7 h f1 r) f2 p'
  | Pfan2,  Pcons Pr77 h p'      => mkp (fun r => Pcons7 h Pr59 r) Pr59 p'
  | Pfan2,  Pcons8 h f1 f2 f3 p' => mkp (fun r => Pcons8 h f1 r f3) f2 p'
  | Pfan2,  Pcons Pr88 h p'      => mkp (fun r => Pcons8 h Pr59 r Pr59) Pr59 p'
  | Pfan3,  Pcons8 h f1 f2 f3 p' => mkp (fun r => Pcons8 h f1 f2 r) f3 p'
  | Pfan3,  Pcons Pr88 h p'      => mkp (fun r => Pcons8 h Pr59 Pr59 r) Pr59 p'
  | _,      _                    => p
  end.

Lemma size_split_part i j k lo p :
  size_part (split_part i j k lo p) = size_part p.
Proof.
move: (size_rot_part j p); rewrite /rot_part size_cat_part addnC.
case: i => //=; case: (drop_part j p) => [|s h|h f1|h f1 f2|h f1 f2 f3] //= p';
  by try case: s; rewrite //= ?size_cat_part.
Qed.

(* Part comparison and intersection; note that the intersection is slightly *)
(* asymmetric, in that it will truncate the second argument.                *)

Fixpoint cmp_part (p q : part) {struct q} : part_rel :=
  match q, p with
  | Pcons sq hq q',           Pcons sp hp p' =>
      meet_prel (cmp_range sp sq)
     (meet_prel (cmp_range hp hq)
                (cmp_part p' q'))
  | Pcons sq hq q',           Pcons6 hp _ p' =>
      meet_prel (cmp_range Pr66 sq)
     (meet_prel (cmp_range hp hq)
                (cmp_part p' q'))
  | Pcons sq hq q',           Pcons7 hp _ _ p' =>
      meet_prel (cmp_range Pr77 sq)
     (meet_prel (cmp_range hp hq)
                (cmp_part p' q'))
  | Pcons sq hq q',           Pcons8 hp _ _ _ p' =>
      meet_prel (cmp_range Pr88 sq)
     (meet_prel (cmp_range hp hq)
                (cmp_part p' q'))
  | Pcons6 hq _ q',           Pcons sp hp p' =>
      meet_prel (notPsubset (cmp_range sp Pr66))
     (meet_prel (cmp_range hp hq)
                (cmp_part p' q'))
  | Pcons7 hq _ _ q',         Pcons sp hp p' =>
      meet_prel (notPsubset (cmp_range sp Pr77))
     (meet_prel (cmp_range hp hq)
                (cmp_part p' q'))
  | Pcons8 hq _ _ _ q',       Pcons sp hp p' =>
      meet_prel (notPsubset (cmp_range sp Pr88))
     (meet_prel (cmp_range hp hq)
                (cmp_part p' q'))
  | Pcons6 hq f1q q',         Pcons6 hp f1p p' =>
      meet_prel (cmp_range hp hq)
     (meet_prel (cmp_range f1p f1q)
                (cmp_part p' q'))
  | Pcons7 hq f1q f2q q',     Pcons7 hp f1p f2p p' =>
      meet_prel (cmp_range hp hq)
     (meet_prel (cmp_range f1p f1q)
     (meet_prel (cmp_range f2p f2q)
                (cmp_part p' q')))
  | Pcons8 hq f1q f2q f3q q', Pcons8 hp f1p f2p f3p p' =>
      meet_prel (cmp_range hp hq)
     (meet_prel (cmp_range f1p f1q)
     (meet_prel (cmp_range f2p f2q)
     (meet_prel (cmp_range f3p f3q)
                (cmp_part p' q'))))
  | Pnil,                    _ =>
     Psubset
  | _,                      Pnil =>
     Pstraddle
  | _,                      _ =>
     Pdisjoint
  end.

Fixpoint meet_part (p q : part) {struct q} : part :=
  match q, p with
  | Pcons sq hq q',            Pcons sp hp p' =>
    Pcons (meet_range sp sq) (meet_range hp hq) (meet_part p' q')
  | Pcons sq hq q',            Pcons6 hp f1 p' =>
    Pcons6 (meet_range hp hq) f1 (meet_part p' q')
  | Pcons sq hq q',            Pcons7 hp f1 f2 p' =>
    Pcons7 (meet_range hp hq) f1 f2 (meet_part p' q')
  | Pcons sq hq q',            Pcons8 hp f1 f2 f3 p' =>
    Pcons8 (meet_range hp hq) f1 f2 f3 (meet_part p' q')
  | Pcons6 hq f1 q',          Pcons sp hp p' =>
    Pcons6 (meet_range hp hq) f1 (meet_part p' q')
  | Pcons7 hq f1 f2 q',       Pcons sp hp p' =>
    Pcons7 (meet_range hp hq) f1 f2 (meet_part p' q')
  | Pcons8 hq f1 f2 f3 q',    Pcons sp hp p' =>
    Pcons8 (meet_range hp hq) f1 f2 f3 (meet_part p' q')
  | Pcons6 hq f1q q',         Pcons6 hp f1p p' =>
    Pcons6 (meet_range hp hq) (meet_range f1p f1q) (meet_part p' q')
  | Pcons7 hq f1q f2q q',     Pcons7 hp f1p f2p p' =>
    Pcons7 (meet_range hp hq) (meet_range f1p f1q) (meet_range f2p f2q) 
           (meet_part p' q')
  | Pcons8 hq f1q f2q f3q q', Pcons8 hp f1p f2p f3p p' =>
    Pcons8 (meet_range hp hq) (meet_range f1p f1q) (meet_range f2p f2q)
           (meet_range f3p f3q) (meet_part p' q')
  | _,                      _ =>
    p
  end.

Lemma size_meet_part p q : size_part (meet_part p q) = size_part p.
Proof.
move Dn: (size_part q) => n; move/eqP: Dn.
by elim: n p q => [|n IHn] p [] //; case: p => //= *; rewrite IHn.
Qed.

(* Part semantics : matching map. *)

Definition subpart_loc_move i g x :=
  match i with
  | Pspoke => @edge g x
  | Phat   => edge (iter 2 face (edge x))
  | Pfan1  => edge (iter 3 face (edge x))
  | Pfan2  => edge (iter 4 face (edge x))
  | Pfan3  => edge (iter 5 face (edge x))
  end.

Coercion subpart_loc_move : subpart_loc >-> Funclass.

Section FitPart.

Variable G : hypermap.

Fixpoint fitp (x : G) (p : part) : bool :=
  let ax := arity (edge x) in
  let axn n := arity (edge (iter n face (edge x))) in
  match p with
  | Pcons s h p' =>
    [&& s (arity (Pspoke G x)), h (arity (Phat G x)) & fitp (face x) p']
  | Pcons6 h f1 p' =>
    [&& Pr66 (arity (Pspoke G x)), h (arity (Phat G x)),
        f1 (arity (Pfan1 G x)) & fitp (face x) p']
  | Pcons7 h f1 f2 p' =>
    [&& Pr77 (arity (Pspoke G x)), h (arity (Phat G x)),
        f1 (arity (Pfan1 G x)), f2 (arity (Pfan2 G x)) & fitp (face x) p']
  | Pcons8 h f1 f2 f3 p' =>
    [&& Pr88 (arity (Pspoke G x)), h (arity (Phat G x)),
        f1 (arity (Pfan1 G x)), f2 (arity (Pfan2 G x)),
        f3 (arity (Pfan3 G x)) & fitp (face x) p']
  | Pnil =>
    true
  end.

Definition exact_fitp x p : bool := (arity x == size_part p) && fitp x p.

(* An intermediate notion, for part converse: simple fit, plus an  *)
(* explicit range check for the hub arity.                         *)
Definition tight_fitp x (up : prange * _) :=
  let (u, p) := up in u (arity x) && fitp x p.

(* Simple properties of fitp (that do not require geometrical properties),  *)
(* that is, list functions, comparison, meet, and split.                    *)

Lemma fitp_drop n p x : fitp x p -> fitp (iter n face x) (drop_part n p).
Proof.
elim: n p x => // n IHn p x; rewrite iterSr.
case: p => //= [s h|h f1|h f1 f2|h f1 f2 f3] p;
  by rewrite ?andbA => /andP[]; auto.
Qed.

Lemma fitp_cat x p1 p2 :
  fitp x (cat_part p1 p2) = fitp x p1 && fitp (iter (size_part p1) face x) p2.
Proof.
elim: p1 x => //= [s h|h f1|h f1 f2|h f1 f2 f3] p1 IHp x;
  by rewrite -?andbA -iterS iterSr -IHp.
Qed.

Lemma fitp_rot n p : n <= size_part p ->
  forall x, exact_fitp x p = exact_fitp (iter n face x) (rot_part n p).
Proof.
move=> le_n_p x; rewrite /exact_fitp size_rot_part arity_iter_face.
case: eqP => //= nFx.
rewrite /rot_part -{1}(cat_take_drop_part n p) !fitp_cat andbC.
congr (_ && _); congr (fitp _ _).
  congr (iter _ face x); move: (congr1 size_part (cat_take_drop_part n p)).
  by rewrite -(subnKC le_n_p) size_cat_part size_drop_part; apply: addIn.
by rewrite -iter_add size_drop_part subnK // -nFx iter_face_arity.
Qed.

Lemma fitp_catrev x p1 p2 :
 fitp x (catrev_part p1 p2)
   = fitp x (rev_part p1) && fitp (iter (size_part p1) face x) p2.
Proof. by rewrite catrev_part_eq fitp_cat size_rev_part. Qed.

(* Comparison and meet.                                                      *)

Let Epr m n :
 (m == n)
     = match n with 6 => Pr66 m | 7 => Pr77 m | 8 => Pr88 m | _ => m == n end.
Proof. by do 9!case: n => // n. Qed.

Lemma fitp_cmp p x :
   fitp x p -> forall q, fitp x q = cmp_part p q (fitp x q).
Proof.
(elim: p x; first by move=> x _ []) => [sp hp|hp f1p|hp f1p f2p|hp f1p f2p f3p];
  move=> p IHp x; rewrite [fitp _ _]/= => /and3P[Es Eh];
  do ?[case/andP=> Ef1 | case/andP=> Ef2 | case/andP=> Ef3] => fit_p;
  case=> //= [sq hq|hq f1q|hq f1q f2q|hq f1q f2q f3q] q; rewrite 1?Epr;
  rewrite 1?(mem_cmp_range Es) ?(eqnP Es) // (mem_cmp_range Eh) (IHp _ fit_p);
  rewrite 1?(mem_cmp_range Ef1) 1?(mem_cmp_range Ef2) 1?(mem_cmp_range Ef3);
  do 1?[case: (cmp_range sp sq) | case: (sp) | case: (sq)] => //=;
  case: (cmp_range hp hq); rewrite /= ?andbF //;
  try (case: (cmp_range f1p f1q); rewrite /= ?andbF //);
  try (case: (cmp_range f2p f2q); rewrite /= ?andbF //);
  try (case: (cmp_range f3p f3q); rewrite /= ?andbF //);
  by case (cmp_part p q); rewrite /= ?andbF.
Qed.

Lemma fitp_meet p q x : fitp x p -> fitp x q -> fitp x (meet_part p q).
Proof.
elim: p q x
  => [|sp hp p IHp|hp f1p p IHp|hp f1p f2p p IHp|hp f1p f2p f3p p IHp];
  do [move=> q x; rewrite [fitp _ _]/= => /and3P[Esp Ehp] | by case];
  do ?[case/andP=> Ef1p | case/andP=> Ef2p | case/andP=> Ef3p] => fit_p;
  case: q => [|sq hq q|hq f1q q|hq f1q f2q q|hq f1q f2q f3q q] /=;
  rewrite ?(eqP Esp) ?Esp ?Ehp ?Ef1p ?Ef2p ?Ef3p // => /and3P[Esq Ehq];
  do ?[case/andP=> Ef1q | case/andP=> Ef2q | case/andP=> Ef3q] => fit_q;
  by rewrite (IHp _ _ fit_p fit_q) ?Esq ?Ef1q ?Ef2q ?Ef3q !mem_meet_range.
Qed.

Lemma exact_fitp_meet p q x :
  exact_fitp x p -> fitp x q -> exact_fitp x (meet_part p q).
Proof.
by rewrite /exact_fitp size_meet_part; case: eqP => // _; exact: fitp_meet.
Qed.

End FitPart.

(* Part location sematics: a constructor function is valid wrt a location if *)
(* it only affects the validity of the range at that location.               *)
(* This definition appears here because we need to quantify over the map.    *)

Definition part_update fp (i : subpart_loc) :=
  forall (r : prange) p,
      size_part (fp r p) = (size_part p).+1
  /\ (forall G x, @fitp G x (fp r p) ->
        r (arity (i G x))
     /\ (forall r' : prange, r' (arity (i G x)) -> fitp x (fp r' p))).

Lemma updatePs h : part_update (fun r => Pcons r h) Pspoke.
Proof. by move=> r p; split=> //= g x /andP[-> ->]; split=> // r' ->. Qed.

Lemma updatePh s : part_update (fun r => Pcons s r) Phat.
Proof. by move=> r p; split=> //= g x /and3P[-> -> ->]; split=> // r' ->. Qed.

Lemma updateP6h f1 : part_update (fun r => Pcons6 r f1) Phat.
Proof. by move=> r p; split=> //= g x /and3P[-> -> ->]; split=> // r' ->. Qed.

Lemma updateP6f1 h : part_update (fun r => Pcons6 h r) Pfan1.
Proof.
by move=> r p; split=> //= g x /and4P[-> -> -> ->]; split=> // r' ->.
Qed.

Lemma updateP7h f1 f2 : part_update (fun r => Pcons7 r f1 f2) Phat.
Proof. by move=> r p; split=> //= g x /and3P[-> -> ->]; split=> // r' ->. Qed.

Lemma updateP7f1 h f2 : part_update (fun r => Pcons7 h r f2) Pfan1.
Proof.
by move=> r p; split=> //= g x /and4P[-> -> -> ->]; split=> // r' ->.
Qed.

Lemma updateP7f2 h f1 : part_update (fun r => Pcons7 h f1 r) Pfan2.
Proof.
by move=> r p; split=> //= g x /and5P[-> -> -> -> ->]; split=> // r' ->.
Qed.

Lemma updateP8h f1 f2 f3 : part_update (fun r => Pcons8 r f1 f2 f3) Phat.
Proof. by move=> r p; split=> //= g x /and3P[-> -> ->]; split=> // r' ->. Qed.

Lemma updateP8f1 h f2 f3 : part_update (fun r => Pcons8 h r f2 f3) Pfan1.
Proof.
by move=> r p; split=> //= g x /and4P[-> -> -> ->]; split=> // r' ->.
Qed.

Lemma updateP8f2 h f1 f3 : part_update (fun r => Pcons8 h f1 r f3) Pfan2.
Proof.
by move=> r p; split=> //= g x /and5P[-> -> -> -> ->]; split=> // r' ->.
Qed.

Lemma updateP8f3 h f1 f2 : part_update (fun r => Pcons8 h f1 f2 r) Pfan3.
Proof.
by split=> //= g x /and5P[-> -> -> -> /andP[-> ->]]; split=> // r' ->.
Qed.

Section FitMirrorPart.

(* Properties of fitp that do depend on geometrical assumptions. They are *)
(* all grouped here, although fitp_pcons_ and fitp_split depend only on   *)
(* the pentagonal property, while fitp_mirror doesn't depend on it.       *)

Variable G : hypermap.
Hypothesis geoG : plain_cubic G.
Let De2 := plain_eq geoG.
Let Dn3 := cubic_eq geoG.

Ltac PopAnd Hn :=
  match goal with
  |  |- (?X1 && _ = _) => case: {-1}X1 (erefl X1) => /= [] Hn;
        rewrite /= ?andbF // ?andbT
  end.

Lemma fitp_mirror p x :
  @exact_fitp G x (mirror_part p) = @exact_fitp (mirror G) x p.
Proof.
move Dars: (fun n G1 x => arity (edge (iter n face (@edge G1 x)))) => ars.
have DarsG := fun n G1 x => erefl (ars n G1 x).
move: {DarsG}(DarsG 2) (DarsG 3) (DarsG 4) (DarsG 5) x p.
rewrite -{2 4 6 8}Dars /= => Dars2 Dars3 Dars4 Dars5.
have Ears2 (x : G): ars 2 (mirror G) x = ars 2 G x.
  rewrite -{1}Dars arity_mirror /= arity_face.
  rewrite -[node x]nodeK -{1}[x]edgeK Dn3 !(finv_f faceI).
  rewrite -{1}[face (edge x)]faceK De2.
  by rewrite -{1}[face (face (edge x))]edgeK Dn3 arity_face -Dars2.
have Earsf n m (x : G):
    arity (edge x) == m -> n <= m -> 
  ars n (mirror G) (face x) = ars (m - n) G x.
- move=> Dm Hnm; rewrite -{1}Dars /= -{1}[x]De2 edgeK.
  rewrite -arity_face in Dm; rewrite (iter_finv faceI) (eqP Dm) //.
  by rewrite -iterSr -(canRL edgeK (De2 _)) (order_finv faceI) arity_face -Dars.
have Ears (x : G): arity (edge (face x : mirror G)) = arity (edge x).
  by rewrite arity_mirror /= -{1}[x]De2 edgeK arity_face.
move: {Earsf}Ears Ears2 (Earsf 3) (Earsf 4) (Earsf 5).
rewrite -{1 3 5 7}Dars /= => Ears Ears2 Ears3 Ears4 Ears5.
have fit_ars G1 x p h0: @fitp G1 x p -> p = Pnil \/ next_hat h0 p (ars 2 _ x).
  by rewrite -Dars; case Dp: p; by [left | case/and3P; right].
move=> x p; rewrite /exact_fitp size_mirror_part arity_mirror /mirror_part.
set h0 := get_hat p; pose h0hx := h0 (ars 2 _ x); symmetry.
case: (arity x =P size_part p) => // nFx.
pose sz0 q := size_part q == 0; set q := Pnil.
transitivity (fitp x q && @fitp (mirror G) x p && (sz0 p || h0hx)).
  case fit_p: (@fitp (mirror G) x p); rewrite {nFx}//= {}/h0hx {}/h0.
  case: (fit_ars (mirror G) x p Pr59 fit_p) => [-> // | ].
  by rewrite -{1}Dars /= Ears2 /= => h0x; apply/esym/orP; right.
have Eqp: next_hat h0 q = next_hat h0 p by rewrite /h0; case p.
have: sz0 q ==> (next_hat h0 q (ars 2 _ x) == h0hx) by apply: eqxx.
clearbody h0; move: q Eqp; rewrite -{1 2 3}[x]iter_face_arity {}nFx /=.
elim: p => [|s h p IHp|h f1 p IHp|h f2 f1 p IHp|h f3 f2 f1 p IHp] q /=;
 (rewrite ?andbT //; set y := iter (size_part p) face x => <- Dh0hx;
   rewrite Ears Ears2 -[RHS]IHp // -/y /=;
   rewrite -Dars2 -?Dars3 -?Dars4 -?Dars5 -?andbA; PopAnd fit_q; PopAnd Es;
   rewrite ?(Ears3 _ _ Es, Ears4 _ _ Es, Ears5 _ _ Es) // (finv_f faceI);
   rewrite andbC -(andbC h0hx) -?andbA [andb h0hx]lock; do ?bool_congr;
   rewrite andbC -lock andbA andbC; PopAnd fit_p;
   by transitivity h0hx;
    [ case: {fit_q}(fit_ars _ _ _ h0 fit_q) => [Dq | ->];
        [rewrite {1}Dq /= in Dh0hx; rewrite (eqP Dh0hx) andbb | rewrite andbT]
    | case: {fit_p}(fit_ars _ _ _ h0 fit_p) => [Dp | ];
        [ rewrite /y Dp /= andbT
        | rewrite -{1}Dars /= Ears2 /y => fit_p ; rewrite fit_p /=;
          case: (p) fit_p ] ]).
Qed.

Lemma fitp_sym p : cmp_part p (mirror_part p) = Psubset ->
  forall x : G, @exact_fitp (mirror G) x p = exact_fitp x p.
Proof.
move=> p_sym x; apply/idP/idP=> /andP[Exp fit_p].
  rewrite -{1}[p]mirror_mirror_part fitp_mirror /exact_fitp size_mirror_part.
  by rewrite Exp (fitp_cmp fit_p) p_sym.
by rewrite -fitp_mirror /exact_fitp size_mirror_part Exp (fitp_cmp fit_p) p_sym.
Qed.

End FitMirrorPart.

Section FitConversePart.

Variable G : hypermap.
Hypothesis geoG : plain_cubic_pentagonal G.
Let pentaG : pentagonal G := geoG.
Let De2 := plain_eq geoG.
Let Dn3 := cubic_eq geoG.

Definition inv_face2 x : G := edge (node (edge (node x))).

Lemma fitp_converse p x:
     exact_fitp x p ->
   tight_fitp (inv_face2 (edge (face (face x)))) (converse_part p).
Proof.
pose t59 h := if h is Pr59 then true else false.
have Et59 h T (r1 r2 : T) :
  (if h is Pr59 then r1 else r2) = if t59 h then r1 else r2.
- by case: h.
have eEnf (y : G) :edge y = node (face y) by rewrite -{2}[y]De2 edgeK.
have fEnne (y : G) : face y = node (node (edge y)) by rewrite eEnf Dn3.
move: p => p1 /andP[Ep1 fit_p1]; rewrite /converse_part.
set effx := edge (face (face x)).
have: let: (h45, q4) := conv_part4 p1 in
    h45 (arity (edge (face (face (edge (face (face effx)))))))
 /\ (forall q5, fitp (face (face effx)) q5 -> fitp (face effx) (q4 q5)).
- case: p1 fit_p1 {Ep1}; (try by simpl) => h34 h p2.
  rewrite [fitp _ _]/= => /and3P[Eh34 _ fit_p2].
  rewrite fEnne -arity_face nodeK fEnne De2 -eEnf fEnne /effx De2 -eEnf.
  rewrite -{1}[edge (face x)](iter_face_subn (ltnW (ltnW (pentaG _)))).
  set n := arity (edge (face x)).
  rewrite -iter_add addnC iter_add {1}[Pcons]lock /= !faceK -eEnf -lock.
  have En: arity (edge (node (edge (face x)))) = n by rewrite -arity_face nodeK.
  rewrite -[edge x]nodeK arity_face -[node (edge x)]nodeK -fEnne in Eh34.
  case: p2 fit_p2 => [|s4 f41 p|f41 h45 p|f41 f42 h45 p|h' f1 f2 f3 p];
    rewrite /= ?Et59 -/n //.
  + case/and3P=> Es4 Ef41 _.
    case (t59 f41); first by rewrite /= En pentaG nodeK Eh34 Es4.
    by case: s4 in Es4 *; rewrite /= ?pentaG // nodeK En (eqnP Es4) Eh34 ?Ef41.
  + by case/and4P=> /eqP Dn Ef41 Eh45 _; rewrite En Dn !nodeK eqxx Eh34 Ef41.
  case/and5P=> /eqP Dn Ef41 Ef42 Eh45 _.
  by rewrite En Dn !nodeK eqxx Eh34 Ef41 Ef42.
case: (conv_part4 p1) => [h45 q4] [Eh45 fit_q4].
move: (drop_part 2 p1) (fitp_drop 2 fit_p1) => p3; rewrite [_ x]/= => fit_p3.
have{fit_p3 Eh45}: let: (u, q5) := conv_part5 h45 p3 in
    u (arity effx) /\ fitp (face (face effx)) q5.
- case: p3 fit_p3 => [|u s5 p|h f p|s5 s6 s7 p|h f1 f2 f3 p] //=.
    by rewrite -/effx Eh45 /= andbT => /and3P[Eu Es5 _].
  rewrite -/effx Eh45 !pentaG /= andbT => /andP[Eu].
  by rewrite !andbA andbC -!andbA => /andP[].
case: {p3 h45}(conv_part5 h45 p3) => [u q5] [Eu {fit_q4}/fit_q4].
move: {q4 q5}(q4 q5) => q fit_q.
move: (drop_part 3 p1) (fitp_drop 3 fit_p1) => p4; rewrite [_ x]/= => fit_p4.
have{fit_p4}: let: (h23, q12) := conv_part12 p4 in
        h23 (arity (edge (face (face (edge effx)))))
    /\ (forall q3, fitp effx q3 -> fitp (inv_face2 effx) (q12 q3)).
  set ef3x := edge (face (face (face x))); set n := arity ef3x.
  have Ds1: arity (edge (inv_face2 effx)) = arity (edge (face (face ef3x))).
    by symmetry; rewrite 2!fEnne -arity_face nodeK /ef3x /inv_face2 !De2 -eEnf.
  have Ds2: edge (face (inv_face2 effx)) = face ef3x.
    by rewrite /inv_face2 nodeK De2 -[node effx]nodeK /effx -fEnne.
  rewrite {1}/effx De2; set ef4x := edge (face (face (face (face x)))).
  have Df21:
       arity (edge (face (face ef4x))) = arity (edge (iter (n - 2) face ef3x)).
  + rewrite /ef4x 3!fEnne -/ef3x -arity_face nodeK De2 Dn3 /n.
    by rewrite -{1}[ef3x]iter_face_arity -(subnKC (pentaG ef3x)) faceK -eEnf.
  case: p4 fit_p4 => [|s2 s1 p|s1 h12 p|s1 h12 f21 p|h f1 f2 f3 p]; first
    [ by simpl; split | case: p; rewrite /= ?Et59 ?if_same /=; try by split ].
  - move=> h23 f21 _ /and5P[Es2 Es1 Eh23 Ef21 _]; rewrite !Et59 /=.
    case (t59 f21); first split=> //=.
      by rewrite //= !pentaG Ds1 Ds2 /ef3x Es1 arity_face Es2 /inv_face2 !nodeK.
    case: s2 Es2 => //=; rewrite Ds1 Ds2 arity_face -/ef3x -/n => /eqP Dn;
     rewrite -/ef4x Df21 Dn /= in Ef21;
     by split; rewrite // Dn eqxx !pentaG /inv_face2 !nodeK Ef21 /ef3x Es1.
  - rewrite -/ef3x -/ef4x Ds1 Ds2 !pentaG arity_face /= => h23 f21.
    move=> _ /and5P[/eqP Dn Es1 Eh12 Eh23 /andP[Ef21 _]].
    rewrite Df21 /n Dn /= in Ef21.
    by split; last by rewrite Dn Es1 Eh12 Ef21 /inv_face2 !nodeK.
  rewrite -/ef3x -/ef4x Ds1 Ds2 !pentaG arity_face /= => h23 f22.
  move=> _ /and5P[/eqP Dn Es1 Eh12 Ef21 /and3P[Eh23 Ef22 _]].
  rewrite Df21 /n Dn /= in Ef22.
  by split; last by rewrite Dn Es1 Eh12 Ef21 Ef22 /inv_face2 !nodeK.
case: {p4}(conv_part12 p4) => [h23 q12] [Eh23 fit_q12].
move: (drop_part 5 p1) (size_drop_part 5 p1) (fitp_drop 5 fit_p1) => p6 Ep6.
have{Ep6 Ep1} Ep6: arity x = 5 + size_part p6 by rewrite Ep6 -(eqP Ep1) subnKC.
move=> /= fit_p6.
rewrite -2!arity_face {1}/inv_face2 !nodeK Eu /=; apply: {q12}fit_q12.
case: p6 fit_p6 Ep6 => //= [_ Ex5 | f31 _ p7 /and3P[Ef31 _]].
  by rewrite Eh23 /effx De2 !arity_face Ex5.
case: p7 => //= [_ Ex6 | f32 _ p8 /and3P[Ef32 _]].
  by rewrite Eh23 /effx De2 !arity_face Ex6 /=.
case: p8 => //= [_ Ex7 | f33 _ [] //= /andP[Ef33 _] Ex8].
  rewrite !Et59.
  by do 2?case: ifP; rewrite /= Eh23 /effx De2 !arity_face Ex7 ?Ef31 ?Ef32.
by rewrite Eh23 /effx De2 !arity_face Ef31 Ef32 Ef33 Ex8.
Qed.

End FitConversePart.

Section FitSplitPart.

Variable G : hypermap.
Hypothesis pentaG : pentagonal G.

Lemma fitp_pcons_(x : G) n : fitp x (pcons_ n).
Proof. by elim: n x => [|n IHn] x //=; rewrite !pentaG IHn. Qed.

Lemma exact_fitp_pcons_ (x : G) : exact_fitp x (pcons_ (arity x)).
Proof. by rewrite /exact_fitp fitp_pcons_; elim (arity x). Qed.

Definition fitc (i : subpart_loc) j k (x : G) :=
  k < arity (i G (iter j face x)).

Lemma fitp_split i j k p :
    good_split i j k p -> forall lo (x : G),
  exact_fitp x (split_part i j k lo p)
    = (lo (+) fitc i j k x) && exact_fitp x p.
Proof.
move=> p_ok lo x; rewrite /exact_fitp size_split_part andbCA; congr (_ && _).
move: p_ok; rewrite /split_part /good_split.
have (pc): part_update pc i -> forall q r,
    size_part (drop_part j p) = size_part (pc r q) ->
    (forall y : G, fitp y (drop_part j p) = fitp y (pc r q)) ->
    good_rsplit k r ->
  let p1 := cat_part (take_part j p) (pc (split_range k lo r) q) in
  fitp x p1 = (lo (+) (k < arity (i G (iter j face x)))) && fitp x p.
- move=> Dpci q r Eq fit_q kr_ok.
  move: (Dpci r q) (Dpci (split_range k lo r) q) => [Erp fit_rp] [Erq fit_rq].
  rewrite -{2}(cat_take_drop_part j p) /= !fitp_cat; bool_congr.
  have <-: j = size_part (take_part j p).
    apply: (@addIn (size_part (drop_part j p))).
    rewrite -size_cat_part cat_take_drop_part size_drop_part subnKC //.
    by rewrite ltnW // -subn_gt0 -size_drop_part Eq Erp.
  rewrite fit_q; apply/idP/idP=> [/fit_rq[] | /andP[xk_ok /fit_rp[Er]]].
    by rewrite fit_split_range // => /andP[-> Er] ->.
  by apply; rewrite fit_split_range // xk_ok.
case: (drop_part j p) i => [|s h p1|h f1 p1|h f1 f2 p1|h f1 f2 f3 p1] [] //.
- by move/(_ _ (updatePs h)); apply.
- by move/(_ _ (updatePh s)); apply.
- case: s => //.
  + by move/(_ _ (updateP6f1 h)); apply=> //= y; rewrite !pentaG.
  + by move/(_ _ (updateP7f1 h Pr59)); apply=> //= y; rewrite !pentaG.
  by move/(_ _ (updateP8f1 h Pr59 Pr59)); apply=> //= y; rewrite !pentaG.
- case: s => //.
  + by move/(_ _ (updateP7f2 h Pr59)); apply=> //= y; rewrite !pentaG.
  by  move/(_ _ (updateP8f2 h Pr59 Pr59)); apply=> //= y; rewrite !pentaG.
- case: s => //.
  by move/(_ _ (updateP8f3 h Pr59 Pr59)); apply=> //= y; rewrite !pentaG.
- by move/(_ _ (updateP6h f1)); apply.
- by move/(_ _ (updateP6f1 h)); apply.
- by move/(_ _ (updateP7h f1 f2)); apply.
- by move/(_ _ (updateP7f1 h f2)); apply.
- by move/(_ _ (updateP7f2 h f1)); apply.
- by move/(_ _ (updateP8h f1 f2 f3)); apply.
- by move/(_ _ (updateP8f1 h f2 f3)); apply.
- by move/(_ _ (updateP8f2 h f1 f3)); apply.
by move/(_ _ (updateP8f3 h f1 f2)); apply.
Qed.

End FitSplitPart.
