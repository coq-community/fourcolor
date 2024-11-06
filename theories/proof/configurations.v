(* (c) Copyright 2006-2018 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq.
From fourcolor Require Import cfmap.

(******************************************************************************)
(*   The construction programs for the 633 reducible configurations, using    *)
(* the special syntax defined in cfmap.ConfigSyntax.                          *)
(*        cfXXX == the data for configuration number XXX.                     *)
(*  the_configs == a list of all the cfXXX; note that configuration number n  *)
(*                 has index n-1 in the_configs, as seq indices start at 0.   *)
(******************************************************************************)

Import ConfigSyntax.

Definition cf001 := Config* 13
  H 3 H 5 H 5 Y 4 H 4 Y 2 Y 1 Y.

Definition cf002 := Config* 6
  H 2 H 6 Y 4 H 1 Y 4 H 4 Y 2 Y Y.

Definition cf003 := Config* 17
  H 1 H 6 H 1 Y 4 H 6 H 6 H 6 Y Y 4 H 1 Y 3 Y 1 Y.

Definition cf004 := Config* 1 2 12 13 
  H 2 H 7 Y 5 H 1 Y 4 H 1 Y 4 Y 2 Y 2 Y.

Definition cf005 := Config* 10
  H 6 H 1 Y 5 H 1 Y 4 H 1 Y 4 H 4 Y 2 Y Y.

Definition cf006 := Config 19
  H 2 H 8 Y 4 H 7 H 2 H 7 Y 6 H 1 Y 1 Y 2 H 4 Y 2 Y Y.

Definition cf007 := Config* 17
  H 3 H 8 H 8 Y 6 H 1 Y 5 H 1 Y 5 Y 3 Y 2 Y Y.

Definition cf008 := Config* 6
  H 2 H 7 Y 3 H 6 Y 2 H 1 H 1 Y H 4 Y Y 1 Y.

Definition cf009 := Config* 26
  H 8 H 1 Y 7 H 7 H 1 Y 5 H 7 Y 3 H 6 H 6 Y Y Y 3 Y Y.

Definition cf010 := Config 20
  H 2 H 9 Y 4 H 2 H 8 Y 3 H 1 Y 6 H 1 Y 1 Y 2 H 4 Y 2 Y Y.

Definition cf011 := Config* 1 2 8 9
  H 8 H 1 Y 7 H 1 Y 5 H 1 H 6 H 1 Y 2 H 6 Y Y Y 3 Y 2 Y.

Definition cf012 := Config* 6
  H 2 H 8 Y 3 H 7 Y 3 H 6 Y 2 H 1 Y H 4 Y Y 1 Y.

Definition cf013 := Config 23
  H 3 H 9 H 9 Y 7 H 1 Y 5 H 2 H 7 Y 6 Y 4 Y 3 Y 2 Y 1 Y.

Definition cf014 := Config* 14
  H 8 H 1 Y 7 H 1 Y 6 H 1 Y 5 H 1 Y 5 H 5 Y 2 Y 3 Y 1 Y.

Definition cf015 := Config 8 9 15 16
  H 9 H 1 Y 8 H 8 H 1 Y 7 H 1 Y 6 H 7 Y 2 H 6 Y Y Y 3 Y 2 Y.

Definition cf016 := Config 30
  H 2 H 10 Y 3 H 9 Y 5 H 8 H 2 H 8 Y 6 H 1 H 1 Y 1 Y 1 Y 3 Y 2 Y 1 Y.

Definition cf017 := Config* 26
  H 2 H 10 Y 4 H 8 H 1 Y 3 H 8 Y 4 H 7 H 7 Y 3 Y 4 Y 3 Y Y 1 Y.

Definition cf018 := Config 26
  H 9 H 1 Y 8 H 1 Y 6 H 2 H 8 Y 6 H 1 Y 6 H 6 Y 3 Y 3 Y Y 1 Y.

Definition cf019 := Config* 6
  H 2 H 9 Y 3 H 8 Y 3 H 7 Y 2 H 1 H 1 Y H 5 Y Y Y 1 Y.

Definition cf020 := Config 1 2 8 9
  H 10 H 1 Y 9 H 1 Y 8 H 7 H 2 H 9 Y 5 Y 3 H 7 H 7 Y Y Y 3 Y 1 Y 2 Y.

Definition cf021 := Config* 6
  H 2 H 10 Y 3 H 9 Y 3 H 8 Y 3 H 7 Y 2 H 1 Y H 5 Y Y Y 1 Y.

Definition cf022 := Config 29
  H 2 H 11 Y 3 H 10 Y 4 H 8 H 1 Y 3 H 8 Y 2 H 1 H 1 Y 5 Y 3 Y 1 Y Y 1 Y.

Definition cf023 := Config 1 2 8 9
  H 2 H 12 Y 3 H 11 Y 3 H 2 H 10 Y 3 H 9 Y 5 Y 6 H 1 H 1 Y 1 Y 1 Y 3 Y 2 Y 1 Y.

Definition cf024 := Config* 6
  H 2 H 7 Y 5 H 1 Y 5 H 5 H 5 Y 3 Y Y Y.

Definition cf025 := Config* 25
  H 3 H 7 H 1 Y 4 H 1 H 1 H 1 Y 1 Y 1 Y 2 H 4 Y 2 Y 1 Y.

Definition cf026 := Config 19
  H 7 H 1 Y 3 H 7 Y 4 H 5 H 1 Y 2 Y 3 Y 1 Y 2 Y.

Definition cf027 := Config 6
  H 2 H 8 Y 6 H 1 Y 4 H 6 Y 3 H 1 Y 4 H 1 Y 3 Y 1 Y.

Definition cf028 := Config 26
  H 2 H 9 Y 4 H 3 H 7 H 1 Y 5 H 1 H 1 Y 1 Y 1 Y 1 Y 2 Y 1 Y.

Definition cf029 := Config* 4 5 21 25
  H 8 H 1 Y 7 H 1 Y 5 H 1 H 6 H 1 Y 6 H 1 Y 1 Y 1 Y 1 Y 2 Y.

Definition cf030 := Config 19
  H 2 H 9 Y 4 H 8 H 2 H 8 Y 7 H 1 Y 1 Y 3 H 5 H 5 Y 3 Y Y Y.

Definition cf031 := Config 18
  H 2 H 9 Y 6 H 8 H 2 H 8 Y 2 H 7 Y Y 5 H 1 Y 4 H 1 Y 3 Y 1 Y.

Definition cf032 := Config 23
  H 2 H 9 Y 7 H 1 Y 4 H 3 H 7 H 7 Y 6 Y 4 Y Y 3 Y 1 Y.

Definition cf033 := Config 24
  H 3 H 9 H 9 Y 6 H 2 H 8 Y 6 H 1 Y 6 Y 4 Y Y 2 Y 2 Y.

Definition cf034 := Config 15
  H 8 H 1 Y 7 H 1 Y 5 H 2 H 7 Y 5 H 1 Y 4 Y 3 Y Y 2 Y.

Definition cf035 := Config 6
  H 2 H 9 Y 7 H 1 Y 6 H 1 Y 5 H 6 Y 4 Y 4 H 4 Y 2 Y Y.

Definition cf036 := Config* 23
  H 7 H 1 H 1 Y 3 H 8 Y 4 H 6 H 1 Y 2 Y 3 Y 1 Y 1 Y 2 Y.

Definition cf037 := Config* 23
  H 2 H 9 Y 7 H 1 Y 5 H 2 H 7 Y 6 H 6 Y 4 Y 2 Y 2 Y 1 Y.

Definition cf038 := Config 10
  H 2 H 8 Y 3 H 7 Y 3 H 6 Y 2 H 1 H 1 Y H 4 Y Y 1 Y.

Definition cf039 := Config* 1 2 8 9
  H 2 H 10 Y 3 H 9 Y 3 H 3 H 7 H 1 Y 6 H 1 Y 1 Y 1 Y 1 Y 2 Y 1 Y.

Definition cf040 := Config 11 12 21 26
  H 2 H 10 Y 4 H 2 H 9 Y 3 H 8 Y 5 H 1 H 1 Y 1 Y 1 Y 1 Y 2 Y 1 Y.

Definition cf041 := Config 20
  H 2 H 10 Y 5 H 2 H 9 Y 3 H 1 Y 7 H 1 Y 1 Y 3 H 5 H 5 Y 3 Y Y Y.

Definition cf042 := Config 23
  H 2 H 10 Y 3 H 9 Y 4 H 8 H 2 H 8 Y 7 H 1 Y 1 Y 2 H 5 Y Y 1 Y 2 Y.

Definition cf043 := Config 30
  H 8 H 2 H 10 Y 8 H 1 Y 6 H 1 H 7 H 1 Y 2 H 7 Y Y Y 3 Y 1 Y 2 Y.

Definition cf044 := Config 25
  H 2 H 10 Y 4 H 8 H 1 Y 4 H 8 H 2 H 8 Y 2 H 7 Y Y Y Y 3 Y 1 Y.

Definition cf045 := Config* 24
  H 6 H 3 H 9 H 9 Y 6 H 1 H 7 H 1 Y 2 H 7 Y Y Y 4 H 4 Y 2 Y Y.

Definition cf046 := Config 18
  H 8 H 1 Y 6 H 1 H 7 H 1 Y 2 H 7 Y Y 4 H 1 H 1 Y H 4 Y Y 1 Y.

Definition cf047 := Config* 25
  H 3 H 10 H 10 Y 8 H 1 Y 7 H 1 Y 6 H 1 Y 6 Y 4 Y 2 Y 3 Y Y.

Definition cf048 := Config 27
  H 2 H 9 Y 3 H 8 Y 3 H 7 Y 4 H 5 H 1 Y H 5 Y Y 1 Y 2 Y.

Definition cf049 := Config 28
  H 2 H 10 Y 3 H 9 Y 3 H 8 Y 4 H 6 H 1 Y 2 H 1 Y 5 Y 4 Y 3 Y Y.

Definition cf050 := Config 27
  H 9 H 1 Y 7 H 2 H 9 Y 7 H 1 Y 6 H 1 Y 6 H 6 Y 2 Y 2 Y 2 Y 1 Y.

Definition cf051 := Config 14
  H 9 H 1 Y 8 H 1 Y 7 H 1 Y 6 H 1 Y 6 H 6 H 6 Y 3 Y Y 3 Y 1 Y.

Definition cf052 := Config 24
  H 3 H 9 H 1 Y 3 H 9 Y 3 H 8 Y 3 H 7 Y 2 H 1 Y 1 Y 3 Y 3 Y Y.

Definition cf053 := Config 23
  H 9 H 1 Y 6 H 3 H 9 H 9 Y 7 H 1 Y 6 H 1 Y 5 Y Y 3 Y 1 Y 1 Y.

Definition cf054 := Config 28
  H 3 H 10 H 10 Y 7 H 2 H 9 Y 6 H 2 H 8 Y 7 Y 5 Y Y 3 Y 2 Y Y.

Definition cf055 := Config 28
  H 9 H 1 Y 8 H 1 Y 6 H 2 H 8 Y 6 H 1 Y 4 Y 2 H 1 Y 1 Y Y 2 Y.

Definition cf056 := Config 28
  H 9 H 1 Y 8 H 1 Y 5 H 3 H 8 H 8 Y 6 H 1 Y 5 Y 3 Y 1 Y 2 Y Y.

Definition cf057 := Config 7
  H 3 H 10 H 10 Y 8 H 1 Y 7 H 1 Y 6 H 7 Y 5 Y 4 H 5 Y 3 Y Y Y.

Definition cf058 := Config 26
  H 3 H 10 H 10 Y 8 H 1 Y 5 H 3 H 8 H 8 Y 7 Y 5 Y Y Y 3 Y 1 Y.

Definition cf059 := Config 28
  H 9 H 1 Y 7 H 2 H 9 Y 7 H 1 Y 6 H 1 Y 6 H 6 Y Y Y 2 Y 2 Y.

Definition cf060 := Config 21
  H 2 H 10 Y 7 H 2 H 9 Y 5 H 3 H 8 H 8 Y 7 Y 4 Y 1 Y 3 Y 2 Y Y.

Definition cf061 := Config 6
  H 2 H 10 Y 8 H 1 Y 7 H 1 Y 5 H 7 Y 2 H 1 H 1 Y 1 Y Y 3 Y 1 Y.

Definition cf062 := Config 8 9 15 16
  H 2 H 11 Y 3 H 2 H 10 Y 3 H 9 Y Y 4 H 7 H 7 H 7 Y Y Y 4 Y Y Y.

Definition cf063 := Config 31
  H 10 H 1 Y 9 H 8 H 2 H 10 Y 8 H 1 Y 7 H 8 Y 2 H 7 Y Y Y 3 Y 1 Y 2 Y.

Definition cf064 := Config 4 5 22 27
  H 2 H 11 Y 3 H 10 Y 3 H 2 H 9 Y 3 H 8 Y 6 H 7 Y Y Y 4 H 1 Y 3 Y 1 Y.

Definition cf065 := Config 31
  H 2 H 11 Y 4 H 2 H 10 Y 4 H 8 H 1 Y 8 Y 6 H 1 H 1 Y 1 Y 1 Y 1 Y 2 Y 1 Y.

Definition cf066 := Config 1 2 8 9
  H 2 H 11 Y 3 H 10 Y 4 H 3 H 8 H 1 Y 7 H 1 Y 7 H 1 Y 1 Y 1 Y 1 Y 2 Y 1 Y.

Definition cf067 := Config 34
  H 10 H 1 Y 8 H 2 H 10 Y 6 H 1 H 8 H 1 Y 3 H 8 H 8 Y Y Y 3 Y 1 Y 3 Y Y.

Definition cf068 := Config 32
  H 9 H 2 H 11 Y 9 H 1 Y 6 H 1 H 8 H 1 Y 8 H 1 Y 1 Y 2 H 6 Y 5 Y 3 Y 1 Y 1 Y.

Definition cf069 := Config* 25
  H 10 H 1 Y 9 H 9 H 1 Y 7 H 1 H 8 H 1 Y 2 H 8 Y Y Y 4 H 1 Y 4 Y 2 Y Y.

Definition cf070 := Config 33
  H 2 H 10 Y 3 H 2 H 9 Y 5 H 8 H 7 H 1 H 1 H 1 Y 1 Y Y 1 Y 1 Y 2 Y 1 Y.

Definition cf071 := Config 21
  H 9 H 1 Y 7 H 8 H 1 Y 6 H 1 H 1 H 8 H 8 Y Y 1 Y Y 4 H 1 Y 3 Y 1 Y.

Definition cf072 := Config 25
  H 9 H 1 Y 8 H 6 H 3 H 9 H 9 Y 7 H 8 Y 2 H 7 Y Y Y 4 H 4 Y 2 Y Y.

Definition cf073 := Config 25
  H 2 H 11 Y 3 H 10 Y 3 H 9 Y 3 H 8 Y 3 H 7 Y 2 H 1 Y 4 Y 3 Y 1 Y Y.

Definition cf074 := Config 15
  H 10 H 1 Y 9 H 1 Y 7 H 2 H 9 Y 7 H 1 Y 6 H 1 Y 5 Y 3 Y 3 Y 3 Y 1 Y.

Definition cf075 := Config 15 29
  H 3 H 11 H 11 Y 9 H 1 Y 8 H 1 Y 6 H 2 H 8 Y 7 Y 5 Y 3 Y 3 Y Y Y.

Definition cf076 := Config* 27
  H 10 H 1 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 6 H 1 Y 6 H 6 Y 2 Y 4 Y Y Y.

Definition cf077 := Config* 14
  H 2 H 9 Y 3 H 8 Y 3 H 7 Y 3 H 6 Y 2 H 1 H 1 Y H 4 Y Y 1 Y.

Definition cf078 := Config 14
  H 2 H 10 Y 3 H 9 Y 3 H 8 Y 3 H 7 Y 2 H 1 H 1 Y 1 Y 4 H 1 Y 3 Y 1 Y.

Definition cf079 := Config 18
  H 2 H 11 Y 3 H 10 Y 3 H 9 Y 3 H 8 Y 3 H 7 Y 3 H 5 H 1 Y 2 Y 1 Y Y Y.

Definition cf080 := Config 27
  H 3 H 10 H 1 Y 3 H 10 Y 3 H 9 Y 3 H 8 Y 2 H 1 H 1 Y 1 Y 4 Y 3 Y Y Y.

Definition cf081 := Config 30
  H 10 H 1 Y 9 H 1 Y 6 H 3 H 9 H 9 Y 7 H 1 Y 7 H 7 Y 3 Y 1 Y 3 Y Y 1 Y.

Definition cf082 := Config 14
  H 9 H 1 Y 8 H 1 Y 7 H 1 Y 6 H 1 Y 5 H 1 H 1 Y H 5 Y Y Y 1 Y.

Definition cf083 := Config 4 5 25 30
  H 11 H 1 Y 10 H 1 Y 9 H 9 H 1 Y 8 H 1 Y 8 H 8 H 8 Y Y Y Y 3 Y 1 Y 1 Y.

Definition cf084 := Config 20
  H 10 H 1 Y 9 H 1 Y 7 H 8 H 1 Y 7 H 1 Y 3 H 1 H 1 Y 1 Y Y 3 Y 1 Y 1 Y.

Definition cf085 := Config 30
  H 10 H 1 Y 9 H 1 Y 6 H 3 H 9 H 9 Y 7 H 1 Y 7 H 1 Y 1 Y Y 3 Y 1 Y Y.

Definition cf086 := Config 26
  H 10 H 1 Y 9 H 1 Y 5 H 4 H 9 H 9 H 9 Y 7 H 1 Y 5 Y 4 Y 1 Y 3 Y Y Y.

Definition cf087 := Config 25
  H 11 H 1 Y 10 H 1 Y 8 H 9 H 1 Y 3 H 1 Y 1 Y 7 H 1 Y 1 Y 3 H 5 H 5 Y 3 Y Y Y.

Definition cf088 := Config 35
  H 11 H 1 Y 10 H 10 H 1 Y 8 H 2 H 10 Y 7 H 9 Y 3 H 8 H 8 Y Y Y 3 Y 1 Y 3 Y Y.

Definition cf089 := Config 8 9 15 16
  H 10 H 1 Y 9 H 9 H 1 Y 8 H 1 Y 6 H 1 H 1 H 8 H 8 Y Y 1 Y Y Y 3 Y 1 Y.

Definition cf090 := Config* 14 15 21 22
  H 8 H 3 H 11 H 11 Y 9 H 9 H 1 Y 8 H 1 Y 6 H 8 Y 3 H 7 Y Y Y Y 3 Y 1 Y.

Definition cf091 := Config 34
  H 11 H 1 Y 9 H 2 H 11 Y 9 H 1 Y 7 H 1 H 8 H 1 Y 8 H 1 Y 1 Y 2 H 6 Y Y Y Y Y.

Definition cf092 := Config 28
  H 8 H 3 H 11 H 11 Y 9 H 1 Y 7 H 1 H 8 H 1 Y 2 H 8 Y Y Y 5 H 5 Y 2 Y 3 Y 1 Y.

Definition cf093 := Config 22
  H 10 H 1 Y 9 H 1 Y 7 H 1 H 8 H 1 Y 2 H 8 Y Y 5 H 1 H 1 Y H 5 Y Y Y 1 Y.

Definition cf094 := Config 25
  H 10 H 1 Y 9 H 9 H 1 Y 8 H 1 Y 6 H 1 H 1 H 8 H 8 Y Y 1 Y Y 4 H 1 Y 3 Y 1 Y.

Definition cf095 := Config 28
  H 2 H 12 Y 3 H 11 Y 3 H 10 Y 3 H 9 Y 3 H 8 Y 2 H 1 H 1 Y 5 Y 3 Y 1 Y Y Y.

Definition cf096 := Config 27
  H 11 H 1 Y 10 H 1 Y 8 H 2 H 10 Y 8 H 1 Y 7 H 1 Y 7 H 7 Y 3 Y 4 Y Y 1 Y Y.

Definition cf097 := Config 26
  H 2 H 11 Y 3 H 10 Y 3 H 9 Y 3 H 8 Y 4 H 7 H 7 Y Y 2 H 1 Y 1 Y 1 Y Y.

Definition cf098 := Config 26
  H 3 H 11 H 11 Y 9 H 1 Y 8 H 1 Y 6 H 2 H 8 Y 7 Y 1 Y 5 H 5 Y Y Y 1 Y.

Definition cf099 := Config 18
  H 10 H 1 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 6 H 1 Y 6 H 1 Y H 5 Y Y Y 1 Y.

Definition cf100 := Config* 27
  H 2 H 11 Y 3 H 10 Y 3 H 9 Y 3 H 8 Y 2 H 1 H 1 Y H 6 Y Y Y Y Y.

Definition cf101 := Config 31
  H 3 H 12 H 12 Y 10 H 1 Y 9 H 1 Y 8 H 8 H 1 Y 8 Y 6 Y 5 H 6 Y 3 Y Y 3 Y 1 Y.

Definition cf102 := Config 31
  H 11 H 1 Y 10 H 1 Y 8 H 2 H 10 Y 8 H 1 Y 6 H 1 H 1 Y 6 Y 3 Y 4 Y Y 3 Y 1 Y.

Definition cf103 := Config 33
  H 11 H 1 Y 10 H 1 Y 9 H 1 Y 7 H 2 H 9 Y 7 H 1 Y 7 H 7 Y 3 Y 4 Y Y Y Y.

Definition cf104 := Config* 31 33
  H 3 H 12 H 12 Y 10 H 1 Y 8 H 2 H 10 Y 7 H 2 H 9 Y 8 Y 5 Y 4 Y 4 Y Y Y Y.

Definition cf105 := Config 6
  H 9 H 1 Y 8 H 1 Y 7 H 1 Y 6 H 1 Y 5 H 1 H 6 H 1 H 1 Y 1 Y 1 Y Y Y.

Definition cf106 := Config 33
  H 2 H 12 Y 3 H 11 Y 4 H 2 H 10 Y 3 H 9 Y 6 H 1 H 1 Y 1 Y Y 2 H 1 Y 1 Y 1 Y 1
  Y.

Definition cf107 := Config 29
  H 11 H 1 Y 10 H 10 H 1 Y 7 H 3 H 10 H 10 Y 8 H 9 Y 2 H 8 Y Y Y 3 H 1 Y 1 Y 1 Y
  Y.

Definition cf108 := Config 23
  H 11 H 1 Y 8 H 10 H 1 Y 9 H 1 Y 8 H 9 Y 2 H 8 Y Y 5 H 1 H 1 Y H 5 Y Y Y 1 Y.

Definition cf109 := Config 6
  H 10 H 1 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 5 H 2 H 7 Y H 1 H 1 Y 1 Y 1 Y Y Y.

Definition cf110 := Config 32
  H 12 H 1 Y 11 H 1 Y 9 H 2 H 11 Y 9 H 1 Y 8 H 1 Y 7 H 8 Y 2 H 1 Y 5 Y Y 3 Y 1 Y
  1 Y.

Definition cf111 := Config 23
  H 8 H 1 Y 6 H 2 H 8 Y 6 H 1 Y 5 H 1 Y 4 Y Y 3 Y Y.

Definition cf112 := Config* 23
  H 2 H 9 Y 7 H 1 Y 6 H 6 H 1 Y 6 Y 3 H 1 Y 4 Y 1 Y 2 Y.

Definition cf113 := Config* 6
  H 8 H 1 Y 3 H 8 Y 5 H 1 Y 4 H 6 Y 3 H 5 H 5 Y 3 Y Y Y.

Definition cf114 := Config 25
  H 2 H 10 Y 3 H 9 Y 4 H 8 H 2 H 8 Y 3 H 7 H 7 Y Y Y Y 3 Y Y.

Definition cf115 := Config 25
  H 2 H 10 Y 4 H 9 H 2 H 9 Y 3 H 8 H 8 Y Y Y 4 H 5 H 5 Y 3 Y Y Y.

Definition cf116 := Config* 1 2 19 24
  H 9 H 1 Y 3 H 9 Y 4 H 7 H 1 Y 3 H 7 Y 2 Y 3 Y 4 Y 3 Y Y.

Definition cf117 := Config 14
  H 8 H 1 Y 7 H 1 Y 6 H 1 Y 6 H 6 H 6 Y 1 H 1 Y 1 Y Y 2 Y.

Definition cf118 := Config 23
  H 9 H 1 Y 7 H 2 H 9 Y 7 H 1 Y 6 H 1 Y 4 Y Y 2 H 1 Y 1 Y Y.

Definition cf119 := Config 6
  H 9 H 1 Y 3 H 9 Y 4 H 2 H 8 Y 2 Y 4 H 6 Y 2 H 5 Y 3 Y Y Y.

Definition cf120 := Config* 6
  H 9 H 1 Y 3 H 9 Y 6 H 5 H 1 H 1 H 1 Y 2 Y 3 Y 1 Y 3 Y Y Y.

Definition cf121 := Config 28
  H 3 H 9 H 1 Y 3 H 9 Y 3 H 8 Y 4 H 7 H 7 Y 3 Y 1 Y 3 Y 1 Y 2 Y.

Definition cf122 := Config 27
  H 3 H 10 H 10 Y 6 H 3 H 9 H 9 Y 7 H 1 Y 7 Y 5 Y Y Y 3 Y Y.

Definition cf123 := Config 27
  H 2 H 10 Y 3 H 9 Y 3 H 8 Y 3 H 1 H 1 Y 5 H 1 Y 5 Y 1 Y 2 Y 1 Y.

Definition cf124 := Config 12 13 28
  H 2 H 10 Y 3 H 9 Y 3 H 8 Y 4 H 6 H 1 Y 4 Y 5 H 5 Y Y 1 Y 2 Y.

Definition cf125 := Config 26
  H 3 H 10 H 10 Y 8 H 1 Y 7 H 7 H 1 Y 7 Y 5 Y 5 H 5 Y 2 Y Y 2 Y.

Definition cf126 := Config 13
  H 9 H 1 Y 7 H 2 H 9 Y 7 H 1 Y 5 H 1 H 1 Y 5 Y Y Y 3 Y Y.

Definition cf127 := Config 31
  H 3 H 10 H 1 Y 3 H 3 H 9 H 1 Y 3 H 9 Y 2 H 1 Y 1 Y 1 Y 1 Y 3 Y Y Y.

Definition cf128 := Config 4 5 18 23
  H 2 H 11 Y 3 H 10 Y 5 H 2 H 9 Y 2 H 1 Y 1 Y 1 Y 3 H 5 H 5 Y 3 Y Y Y.

Definition cf129 := Config 26
  H 2 H 11 Y 5 H 2 H 10 Y 3 H 9 Y 5 H 8 Y 3 H 7 H 7 Y Y Y Y 3 Y Y.

Definition cf130 := Config 6
  H 9 H 1 Y 3 H 9 Y 3 H 8 Y 4 H 1 Y 6 H 1 Y 4 H 5 Y 1 H 1 Y 1 Y Y.

Definition cf131 := Config 29
  H 2 H 11 Y 3 H 10 Y 4 H 9 H 2 H 9 Y 3 H 8 H 8 Y Y Y 3 H 5 Y 3 Y Y Y.

Definition cf132 := Config 32
  H 4 H 9 H 1 H 1 Y 3 H 10 Y 4 H 9 H 2 H 9 Y 2 H 8 Y Y Y 2 Y 3 Y Y Y.

Definition cf133 := Config 34
  H 9 H 2 H 11 Y 9 H 1 Y 7 H 1 H 8 H 1 Y 2 H 8 Y Y 6 H 1 Y 5 Y 1 Y 3 Y Y.

Definition cf134 := Config 19
  H 2 H 10 Y 4 H 9 H 2 H 9 Y 8 H 1 Y 1 Y 2 H 6 Y 2 H 1 H 1 Y 4 H 1 Y 3 Y 1 Y.

Definition cf135 := Config* 13
  H 8 H 1 H 1 Y 3 H 9 Y 3 H 8 Y 3 H 7 Y 2 Y 2 H 1 Y 4 Y 1 Y 2 Y.

Definition cf136 := Config 14
  H 9 H 1 Y 8 H 1 Y 7 H 1 Y 6 H 1 Y 6 H 6 Y 1 H 1 Y 1 Y Y 2 Y.

Definition cf137 := Config 29
  H 10 H 1 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 6 H 1 Y 6 H 6 Y 2 Y 2 Y 2 Y 1 Y.

Definition cf138 := Config 18 19 29
  H 10 H 1 Y 3 H 10 Y 5 H 7 H 1 H 1 Y 3 H 8 Y 2 Y 3 Y 1 Y 3 Y Y Y.

Definition cf139 := Config 7
  H 3 H 11 H 11 Y 8 H 2 H 10 Y 8 H 1 Y 7 H 1 Y 7 Y 5 Y Y 3 Y 2 Y 2 Y.

Definition cf140 := Config 12 13 29
  H 2 H 11 Y 3 H 10 Y 3 H 9 Y 3 H 8 Y 3 H 7 Y 4 Y 5 H 5 Y Y 1 Y 2 Y.

Definition cf141 := Config* 29
  H 10 H 1 Y 3 H 10 Y 3 H 9 Y 3 H 2 H 8 Y 2 Y 3 Y 4 Y 4 H 4 Y 2 Y Y.

Definition cf142 := Config 29
  H 3 H 11 H 11 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 7 H 7 Y 5 Y 2 Y 2 Y 2 Y 2 Y.

Definition cf143 := Config 17 22 23 28
  H 9 H 1 H 1 Y 3 H 10 Y 4 H 8 H 1 Y 3 H 8 Y 2 Y 3 Y 5 Y 4 Y 3 Y 1 Y.

Definition cf144 := Config 14
  H 2 H 11 Y 3 H 10 Y 3 H 9 Y 3 H 8 Y 4 H 7 H 7 Y 3 Y 4 Y 1 Y 2 Y 1 Y.

Definition cf145 := Config 5 19 27 29
  H 3 H 11 H 11 Y 9 H 1 Y 7 H 2 H 9 Y 7 H 1 Y 7 Y 5 Y Y Y 3 Y Y.

Definition cf146 := Config 26
  H 9 H 2 H 11 Y 9 H 1 Y 7 H 2 H 9 Y 7 H 1 Y 7 H 7 Y Y 3 Y 1 Y 2 Y 1 Y.

Definition cf147 := Config 30
  H 8 H 3 H 11 H 11 Y 9 H 1 Y 8 H 1 Y 6 H 1 H 1 Y 6 Y Y Y 3 Y 1 Y Y.

Definition cf148 := Config 13
  H 10 H 1 Y 8 H 2 H 10 Y 8 H 1 Y 7 H 1 Y 6 H 7 Y Y Y 2 H 1 Y 1 Y Y.

Definition cf149 := Config 29
  H 9 H 1 H 1 Y 3 H 10 Y 6 H 6 H 1 H 1 H 1 Y 2 Y 3 Y 1 Y 1 Y 3 Y Y Y.

Definition cf150 := Config 32
  H 10 H 1 Y 9 H 1 Y 8 H 8 H 1 Y 7 H 1 Y 7 H 7 Y 5 H 6 Y 3 Y Y Y 2 Y.

Definition cf151 := Config 31
  H 10 H 1 Y 9 H 1 Y 7 H 2 H 9 Y 7 H 1 Y 7 H 7 H 7 Y Y Y Y 3 Y Y.

Definition cf152 := Config 4 5 22 27
  H 2 H 12 Y 3 H 11 Y 4 H 2 H 10 Y 3 H 9 Y 2 H 1 Y 1 Y 1 Y 2 H 5 Y 3 Y Y Y.

Definition cf153 := Config 32
  H 3 H 11 H 11 Y 9 H 1 Y 8 H 1 Y 6 H 8 Y 6 Y 4 H 1 H 1 Y 4 Y Y 1 Y 1 Y.

Definition cf154 := Config 29
  H 9 H 2 H 11 Y 9 H 1 Y 6 H 3 H 9 H 9 Y 7 H 1 Y 5 Y 1 Y 3 Y 1 Y Y 1 Y.

Definition cf155 := Config 26
  H 4 H 11 H 11 H 11 Y 9 H 1 Y 8 H 1 Y 7 H 8 Y 5 Y 1 Y 4 H 5 Y Y 1 Y 1 Y.

Definition cf156 := Config 29
  H 4 H 11 H 11 H 11 Y 9 H 1 Y 6 H 3 H 9 H 9 Y 8 Y 5 Y 1 Y 3 Y Y 1 Y 1 Y.

Definition cf157 := Config 6
  H 10 H 1 Y 3 H 10 Y 3 H 9 Y 5 H 1 Y 7 H 7 H 7 H 7 Y Y 1 Y 3 Y Y Y.

Definition cf158 := Config 6
  H 10 H 1 Y 3 H 10 Y 3 H 9 Y 5 H 1 Y 5 H 7 Y 3 H 1 Y 5 H 1 Y 3 Y 1 Y 1 Y.

Definition cf159 := Config 1 2 32
  H 10 H 1 Y 9 H 1 Y 8 H 1 Y 5 H 3 H 8 H 8 Y 7 H 1 Y 1 Y Y 3 Y 1 Y 2 Y.

Definition cf160 := Config 30
  H 2 H 12 Y 3 H 11 Y 3 H 2 H 10 Y 2 H 9 Y 3 H 8 H 8 Y Y Y 3 H 5 Y 3 Y Y Y.

Definition cf161 := Config 30
  H 2 H 12 Y 3 H 11 Y 4 H 2 H 10 Y 9 H 1 Y 3 H 8 H 8 Y Y Y 3 H 5 Y 3 Y Y Y.

Definition cf162 := Config 33
  H 4 H 10 H 1 H 1 Y 3 H 11 Y 3 H 2 H 10 Y 2 H 9 Y 2 H 8 Y Y Y 2 Y 3 Y Y Y.

Definition cf163 := Config 33
  H 4 H 10 H 1 H 1 Y 3 H 11 Y 4 H 2 H 10 Y 9 H 1 Y 2 H 8 Y Y Y 2 Y 3 Y Y Y.

Definition cf164 := Config 35
  H 3 H 11 H 1 Y 4 H 3 H 10 H 1 Y 3 H 10 Y 2 H 1 Y 3 H 8 Y Y 1 Y 1 Y 3 Y Y Y.

Definition cf165 := Config 36
  H 11 H 1 Y 10 H 1 Y 8 H 9 H 1 Y 8 H 1 Y 8 H 8 Y 4 H 7 Y Y 1 Y 2 H 1 Y 3 Y 1 Y.

Definition cf166 := Config 11 12 18 19
  H 10 H 2 H 12 Y 8 H 10 H 1 Y 9 H 1 Y 1 Y 8 H 1 Y 1 Y 3 H 6 H 6 Y 5 Y 4 Y Y Y.

Definition cf167 := Config 33
  H 10 H 2 H 12 Y 10 H 1 Y 9 H 1 Y 7 H 1 H 8 H 1 Y 8 H 1 Y 1 Y 1 Y 5 Y 4 Y Y Y.

Definition cf168 := Config 35
  H 2 H 12 Y 3 H 2 H 11 Y 4 H 9 H 1 Y 4 H 1 Y 7 H 1 H 1 Y 1 Y 1 Y 4 Y 1 Y 3 Y Y.

Definition cf169 := Config* 11 12 18 19
  H 10 H 2 H 12 Y 9 H 10 H 1 Y 9 H 1 Y 1 Y 7 H 1 H 1 Y 1 Y 2 H 6 Y 4 Y 1 Y 3 Y Y.

Definition cf170 := Config 38
  H 4 H 10 H 1 H 1 Y 3 H 11 Y 5 H 10 H 2 H 10 Y 2 H 9 Y Y 7 H 1 Y 2 Y 4 Y Y Y Y.

Definition cf171 := Config 26
  H 2 H 12 Y 4 H 2 H 11 Y 4 H 10 H 2 H 10 Y 9 H 1 Y 1 Y 1 Y 4 H 6 H 6 Y 3 Y Y 3 
  Y 1 Y.

Definition cf172 := Config 34
  H 2 H 12 Y 3 H 11 Y 4 H 10 H 2 H 10 Y 9 H 1 Y 1 Y 3 H 7 H 7 Y 3 H 6 Y Y 3 Y Y 
  Y.

Definition cf173 := Config 36
  H 10 H 1 Y 9 H 9 H 1 Y 5 H 1 H 3 H 9 H 9 H 9 H 9 Y Y 1 Y Y Y 4 Y Y Y.

Definition cf174 := Config 36
  H 10 H 1 Y 7 H 9 H 1 Y 9 H 9 H 1 H 1 Y 4 H 8 H 8 H 8 Y Y Y Y 4 Y Y Y.

Definition cf175 := Config 20
  H 2 H 11 Y 3 H 2 H 10 Y 2 H 9 Y 8 H 1 Y 1 Y 2 H 6 Y 2 H 1 H 1 Y H 4 Y Y 1 Y.

Definition cf176 := Config 20
  H 2 H 11 Y 6 H 2 H 10 Y 3 H 1 Y 8 H 1 Y 1 Y 2 H 6 Y 2 H 1 H 1 Y 4 H 1 Y 3 Y 1 
  Y.

Definition cf177 := Config 26
  H 8 H 3 H 11 H 11 Y 9 H 9 H 1 Y 4 H 1 Y 7 H 1 Y 1 Y 1 Y 3 H 5 H 5 Y 3 Y Y Y.

Definition cf178 := Config 29
  H 11 H 1 Y 10 H 1 Y 9 H 1 Y 7 H 2 H 9 Y 7 H 1 Y 7 H 7 Y 6 Y 4 Y Y 1 Y Y.

Definition cf179 := Config 32
  H 4 H 11 H 11 H 11 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 7 Y 6 H 6 Y 3 Y 3 Y Y 1 Y.

Definition cf180 := Config 7
  H 3 H 12 H 12 Y 9 H 2 H 11 Y 8 H 2 H 10 Y 8 H 1 Y 8 Y 6 Y Y 4 Y 2 Y 3 Y Y.

Definition cf181 := Config 7 29 32
  H 10 H 1 H 1 Y 4 H 10 H 1 Y 4 H 9 H 1 Y 3 H 9 Y 2 Y 3 Y 1 Y 4 Y 3 Y 2 Y Y.

Definition cf182 := Config 27
  H 10 H 2 H 12 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 7 H 7 Y Y 3 Y 3 Y Y 2 Y.

Definition cf183 := Config 16 32
  H 3 H 12 H 12 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 4 Y 3 H 6 Y 2 Y 3 Y 3 Y Y.

Definition cf184 := Config 33
  H 10 H 1 H 1 Y 3 H 11 Y 3 H 2 H 10 Y 3 H 9 Y 2 Y 3 Y 6 Y 3 H 1 Y 4 Y 2 Y Y.

Definition cf185 := Config 8 31 33
  H 2 H 12 Y 3 H 11 Y 4 H 9 H 1 Y 3 H 9 Y 4 H 8 H 8 Y 3 Y 4 Y 1 Y 1 Y 2 Y 1 Y.

Definition cf186 := Config 14
  H 2 H 12 Y 3 H 11 Y 3 H 10 Y 3 H 9 Y 3 H 8 Y 3 H 1 Y 6 H 6 Y Y 1 Y 2 Y 1 Y.

Definition cf187 := Config 25 30 33
  H 11 H 1 Y 9 H 2 H 11 Y 9 H 1 Y 8 H 1 Y 6 H 1 H 1 Y 6 Y Y Y 3 Y 1 Y Y.

Definition cf188 := Config 32
  H 10 H 1 H 1 Y 3 H 11 Y 3 H 10 Y 5 H 7 H 1 H 1 Y 2 Y 3 Y 5 Y Y 3 Y 1 Y 1 Y.

Definition cf189 := Config 33
  H 11 H 1 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 6 H 2 H 8 Y 7 H 7 Y 2 Y 2 Y 3 Y Y 2 Y.

Definition cf190 := Config 30
  H 2 H 12 Y 3 H 11 Y 4 H 9 H 1 Y 3 H 9 Y 3 H 8 Y 2 H 1 Y 6 Y 5 Y 3 Y 1 Y 1 Y.

Definition cf191 := Config 31
  H 2 H 12 Y 3 H 11 Y 3 H 10 Y 3 H 9 Y 3 H 8 Y 2 H 1 H 1 Y 5 Y 1 Y 2 Y 1 Y 1 Y.

Definition cf192 := Config 27
  H 11 H 1 Y 9 H 2 H 11 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 7 H 7 Y Y Y 3 Y 2 Y 2 Y.

Definition cf193 := Config 18 21 30 33
  H 11 H 1 Y 4 H 10 H 1 Y 5 H 8 H 1 H 1 Y 3 H 9 Y 2 Y 4 Y Y 4 Y 3 Y 2 Y Y.

Definition cf194 := Config 6 10 19 33
  H 4 H 12 H 12 H 12 Y 9 H 2 H 11 Y 9 H 1 Y 8 H 1 Y 8 Y 5 Y 1 Y 3 Y 3 Y Y 2 Y.

Definition cf195 := Config 18
  H 10 H 2 H 12 Y 10 H 1 Y 8 H 2 H 10 Y 8 H 1 Y 7 H 1 Y 5 Y 1 Y 3 Y 1 Y Y 1 Y.

Definition cf196 := Config 32
  H 4 H 12 H 12 H 12 Y 10 H 1 Y 9 H 1 Y 7 H 2 H 9 Y 8 Y 5 Y 1 Y 3 Y Y 1 Y 1 Y.

Definition cf197 := Config 24
  H 11 H 1 Y 3 H 11 Y 3 H 10 Y 4 H 2 H 9 Y 2 Y 6 H 7 H 7 Y Y 1 Y 3 Y Y Y.

Definition cf198 := Config 33
  H 11 H 1 Y 3 H 11 Y 3 H 10 Y 4 H 2 H 9 Y 2 Y 5 H 7 Y 4 Y 3 Y 2 H 4 Y 2 Y Y.

Definition cf199 := Config 21 24 30 33
  H 11 H 1 Y 3 H 11 Y 3 H 10 Y 6 H 6 H 1 H 1 H 1 Y 2 Y 4 Y 4 Y Y 3 Y 1 Y 1 Y.

Definition cf200 := Config 23
  H 3 H 12 H 12 Y 10 H 1 Y 7 H 3 H 10 H 10 Y 8 H 1 Y 8 Y 5 Y 1 Y Y Y 3 Y Y.

Definition cf201 := Config 1 2 32
  H 11 H 1 Y 10 H 1 Y 9 H 1 Y 6 H 3 H 9 H 9 Y 7 H 1 Y 5 Y 4 Y 1 Y 3 Y 2 Y 1 Y.

Definition cf202 := Config 10
  H 9 H 1 Y 8 H 1 Y 7 H 1 Y 6 H 1 Y 5 H 1 H 2 H 6 Y H 1 Y 3 Y 1 Y 1 Y.

Definition cf203 := Config 12 13 19 20
  H 2 H 13 Y 3 H 12 Y 3 H 2 H 11 Y 3 H 10 Y Y 3 H 8 H 8 Y Y Y 3 H 5 Y 3 Y Y Y.

Definition cf204 := Config 36
  H 11 H 1 Y 9 H 2 H 11 Y 7 H 3 H 10 H 10 Y 7 H 1 H 1 Y 7 Y 6 Y 5 Y 1 Y 3 Y Y 2 
  Y.

Definition cf205 := Config 35
  H 3 H 12 H 12 Y 9 H 2 H 11 Y 9 H 1 Y 8 H 9 H 9 Y 7 Y 7 Y 6 H 6 Y Y 3 Y 2 Y 1 Y.

Definition cf206 := Config 36
  H 11 H 1 Y 10 H 1 Y 8 H 9 H 1 Y 7 H 1 H 1 Y 7 Y 5 H 1 H 1 Y 4 Y 1 Y Y 1 Y 1 Y.

Definition cf207 := Config 18 19 25 26
  H 11 H 2 H 13 Y 10 H 2 H 12 Y 10 H 10 H 1 Y 9 H 1 Y 1 Y 8 H 1 Y 1 Y 1 Y 5 Y 4 
  Y Y Y.

Definition cf208 := Config 35
  H 4 H 12 H 12 H 12 Y 10 H 10 H 1 Y 8 H 2 H 10 Y 9 Y 5 H 1 Y 1 Y 6 Y 4 Y 3 Y 2 
  Y 1 Y.

Definition cf209 := Config 26
  H 4 H 12 H 12 H 12 Y 10 H 1 Y 8 H 9 H 1 Y 9 Y 6 Y 1 Y 6 H 6 H 6 Y Y Y 1 Y 1 Y.

Definition cf210 := Config 35
  H 11 H 1 Y 8 H 10 H 1 Y 9 H 1 Y 8 H 1 Y 6 H 8 H 8 H 8 Y Y 1 Y 4 Y Y Y Y.

Definition cf211 := Config 31
  H 11 H 1 Y 8 H 3 H 11 H 11 Y 9 H 1 Y 8 H 1 Y 5 Y 2 H 7 Y Y Y 2 H 1 Y 1 Y Y.

Definition cf212 := Config 35
  H 5 H 9 H 1 H 1 H 1 Y 3 H 11 Y 3 H 10 Y 3 H 9 Y 2 H 1 Y 1 Y Y 3 Y 1 Y 1 Y 2 Y.

Definition cf213 := Config 34
  H 2 H 13 Y 3 H 12 Y 3 H 2 H 11 Y 3 H 10 Y 9 H 1 Y 3 H 8 H 8 Y Y Y 3 H 5 Y 3 Y 
  Y Y.

Definition cf214 := Config 37
  H 11 H 1 Y 10 H 1 Y 8 H 9 H 1 Y 9 H 9 H 1 H 1 Y 3 H 8 H 8 Y Y Y Y 4 Y Y Y.

Definition cf215 := Config 27
  H 2 H 13 Y 4 H 2 H 12 Y 3 H 2 H 11 Y 2 H 10 Y 9 H 1 Y 1 Y 1 Y 4 H 1 Y 5 H 1 Y 
  4 Y Y 1 Y.

Definition cf216 := Config 8 9 15 16
  H 2 H 13 Y 3 H 2 H 12 Y 3 H 11 Y Y 4 H 9 H 9 H 9 Y Y Y 5 H 6 H 6 Y Y 3 Y Y Y.

Definition cf217 := Config 8 9 15 16
  H 12 H 1 Y 10 H 11 H 1 Y 10 H 1 Y 1 Y 7 H 1 H 1 H 1 Y 1 Y 2 H 7 Y 4 H 1 Y 1 Y 
  4 Y Y Y.

Definition cf218 := Config 33
  H 3 H 12 H 12 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 7 Y 1 Y 5 H 5 Y Y Y 1 Y.

Definition cf219 := Config 28
  H 12 H 1 Y 11 H 1 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 7 H 7 Y 3 Y 4 Y Y Y 2 Y.

Definition cf220 := Config 36
  H 11 H 1 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 5 H 3 H 8 H 8 Y 1 H 1 Y 5 Y 3 Y 1 Y Y 2 Y.

Definition cf221 := Config 31
  H 3 H 12 H 1 Y 3 H 12 Y 4 H 10 H 1 Y 3 H 10 Y 3 H 9 Y 2 H 1 Y 1 Y 5 Y 3 Y 1 Y 
  2 Y Y.

Definition cf222 := Config 34
  H 2 H 13 Y 3 H 12 Y 5 H 9 H 1 H 1 Y 3 H 10 Y 4 H 9 H 9 Y 3 Y 6 Y Y Y 3 Y 1 Y 1
  Y.

Definition cf223 := Config 37
  H 12 H 1 Y 11 H 11 H 1 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 8 H 8 Y 2 Y 5 H 6 Y 2 Y 4 Y 
  1 Y 2 Y.

Definition cf224 := Config 36
  H 12 H 1 Y 11 H 1 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 7 H 8 H 8 Y 3 H 7 Y 2 Y 4 Y Y 3 Y
  Y.

Definition cf225 := Config 35
  H 2 H 13 Y 3 H 12 Y 3 H 11 Y 3 H 10 Y 3 H 9 Y 3 H 8 Y 3 H 6 H 1 Y 6 Y 1 Y 2 Y 
  1 Y 1 Y.

Definition cf226 := Config 35 37
  H 12 H 1 Y 10 H 2 H 12 Y 10 H 1 Y 8 H 2 H 10 Y 8 H 1 Y 8 H 8 Y 6 Y 5 Y 4 Y Y 2
  Y 1 Y.

Definition cf227 := Config 30
  H 12 H 1 Y 10 H 2 H 12 Y 9 H 2 H 11 Y 9 H 1 Y 8 H 1 Y 8 H 8 Y Y Y 4 Y 2 Y 3 Y 
  Y.

Definition cf228 := Config 35
  H 11 H 2 H 13 Y 11 H 1 Y 9 H 2 H 11 Y 9 H 1 Y 7 H 1 H 1 Y 7 Y 7 Y 4 Y 4 Y 3 Y 
  Y 1 Y.

Definition cf229 := Config 36
  H 3 H 13 H 13 Y 10 H 2 H 12 Y 10 H 1 Y 7 H 3 H 10 H 10 Y 9 Y 7 Y 3 Y 4 Y 3 Y 1
  Y 2 Y Y.

Definition cf230 := Config 7
  H 4 H 13 H 13 H 13 Y 10 H 2 H 12 Y 9 H 2 H 11 Y 9 H 1 Y 9 Y 6 Y 1 Y 4 Y 3 Y Y 
  3 Y Y.

Definition cf231 := Config 19
  H 10 H 1 H 1 H 1 Y 4 H 11 H 1 Y 4 H 10 H 1 Y 3 H 10 Y 2 Y 4 Y Y 5 Y 3 Y 1 Y 2 
  Y Y.

Definition cf232 := Config 11 33 37
  H 2 H 13 Y 5 H 10 H 1 H 1 Y 3 H 11 Y 4 H 9 H 1 Y 3 H 9 Y 6 Y 1 Y 1 Y 3 Y 1 Y Y
  1 Y.

Definition cf233 := Config 35
  H 3 H 13 H 13 Y 11 H 1 Y 9 H 2 H 11 Y 8 H 2 H 10 Y 9 H 9 Y 6 Y 5 Y Y 4 Y Y Y 2
  Y.

Definition cf234 := Config 6
  H 2 H 13 Y 10 H 2 H 12 Y 7 H 4 H 11 H 11 H 11 Y 9 H 1 Y 9 Y 6 Y Y 5 Y 3 Y Y 3 
  Y Y.

Definition cf235 := Config 32
  H 12 H 1 Y 9 H 11 H 1 Y 10 H 1 Y 9 H 1 Y 9 Y 7 H 1 Y 7 H 1 Y 6 H 6 Y Y Y 1 Y 1
  Y.

Definition cf236 := Config 10
  H 10 H 1 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 6 H 1 Y 5 H 1 H 6 H 1 H 1 Y 1 Y 1 Y Y Y.

Definition cf237 := Config 36
  H 12 H 1 Y 11 H 9 H 3 H 12 H 12 Y 10 H 1 Y 8 H 1 H 1 Y 8 Y 8 H 8 Y Y 5 Y 4 Y Y
  3 Y Y.

Definition cf238 := Config 43
  H 12 H 1 Y 11 H 11 H 1 Y 7 H 4 H 11 H 11 H 11 Y 9 H 10 Y 2 H 9 Y Y Y 3 H 1 Y 1
  Y 1 Y 1 Y 2 Y.

Definition cf239 := Config 36
  H 4 H 11 H 1 H 1 Y 3 H 2 H 12 Y 4 H 10 H 1 Y 5 H 1 Y 7 H 1 H 1 Y 1 Y 1 Y 1 Y 4
  Y Y Y Y.

Definition cf240 := Config 38
  H 12 H 1 Y 11 H 1 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 8 H 8 H 8 H 8 Y 2 H 1 Y 5 Y Y 3 Y
  1 Y Y.

Definition cf241 := Config 37
  H 12 H 1 Y 11 H 1 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 6 H 1 H 1 H 8 H 8 Y Y Y 2 H 1 Y 1
  Y 1 Y Y.

Definition cf242 := Config 14
  H 9 H 1 Y 8 H 1 Y 7 H 1 Y 6 H 1 Y 5 H 1 H 1 Y H 5 Y 4 Y 1 Y 1 Y.

Definition cf243 := Config 32
  H 3 H 11 H 11 Y 7 H 3 H 10 H 10 Y 7 H 2 H 9 Y 8 Y 6 Y Y 2 Y 3 Y Y 2 Y.

Definition cf244 := Config 32
  H 3 H 11 H 11 Y 7 H 3 H 10 H 10 Y 7 H 2 H 9 Y 8 Y 6 Y Y Y 3 Y 1 Y 2 Y.

Definition cf245 := Config 30
  H 10 H 1 Y 9 H 1 Y 8 H 8 H 1 Y 6 H 1 H 1 Y 6 Y 5 H 1 Y 1 Y Y 3 Y Y.

Definition cf246 := Config 1 2 30
  H 2 H 11 Y 8 H 2 H 10 Y 8 H 7 H 2 H 9 Y 8 Y 4 H 1 Y 1 Y Y 3 Y 1 Y 2 Y.

Definition cf247 := Config 6
  H 10 H 1 Y 4 H 9 H 1 Y 3 H 9 Y 4 H 1 Y 4 Y Y 3 H 1 Y 4 H 1 Y 3 Y 1 Y.

Definition cf248 := Config* 31
  H 10 H 1 Y 8 H 2 H 10 Y 8 H 1 Y 5 H 1 H 1 H 1 Y 5 Y 1 Y Y Y 3 Y Y.

Definition cf249 := Config 26
  H 2 H 12 Y 3 H 11 Y 6 H 2 H 10 Y 2 H 1 Y 3 H 8 Y Y 1 Y 3 H 5 H 5 Y 3 Y Y Y.

Definition cf250 := Config 20
  H 8 H 1 H 1 H 1 Y 3 H 10 Y 3 H 9 Y 3 H 8 Y 2 Y 4 Y 5 H 1 Y 1 Y Y 2 Y.

Definition cf251 := Config 18
  H 10 H 1 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 6 H 1 Y 3 Y 3 H 1 Y H 4 Y Y 1 Y.

Definition cf252 := Config 18
  H 11 H 1 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 7 H 7 H 7 Y 3 Y Y 3 Y 1 Y 1 Y.

Definition cf253 := Config 33
  H 3 H 12 H 12 Y 9 H 2 H 11 Y 9 H 1 Y 7 H 2 H 9 Y 8 Y 6 Y Y 5 Y 4 Y Y Y.

Definition cf254 := Config 11 12 33
  H 3 H 12 H 12 Y 8 H 3 H 11 H 11 Y 9 H 1 Y 8 H 1 Y 8 Y 6 Y Y Y 3 Y 1 Y 2 Y.

Definition cf255 := Config 33
  H 10 H 2 H 12 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 7 H 7 Y Y 2 Y 3 Y 3 Y Y.

Definition cf256 := Config 31
  H 11 H 1 Y 9 H 2 H 11 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 7 H 7 Y Y Y 2 Y 2 Y 2 Y.

Definition cf257 := Config 33
  H 10 H 2 H 12 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 6 H 1 H 1 Y 6 Y 3 Y Y 3 Y 1 Y 1 Y.

Definition cf258 := Config 24
  H 3 H 11 H 11 Y 9 H 1 Y 7 H 2 H 9 Y 7 H 1 Y 7 Y 5 Y 5 H 5 Y 2 Y Y 2 Y.

Definition cf259 := Config 4 5 22 29
  H 2 H 12 Y 3 H 11 Y 4 H 9 H 1 Y 3 H 9 Y 4 H 8 H 8 Y 3 Y 5 Y 1 Y 3 Y Y 1 Y.

Definition cf260 := Config 31
  H 3 H 12 H 12 Y 10 H 1 Y 9 H 1 Y 8 H 8 H 1 Y 8 Y 6 Y 5 H 1 Y 1 Y Y 3 Y Y.

Definition cf261 := Config 15 16 33
  H 10 H 2 H 12 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 4 Y 1 Y 2 H 1 Y 1 Y Y Y.

Definition cf262 := Config 33
  H 11 H 1 Y 4 H 10 H 1 Y 3 H 10 Y 3 H 2 H 9 Y 2 Y 4 Y Y 4 Y 4 H 1 Y 3 Y 1 Y.

Definition cf263 := Config 21 26 33
  H 11 H 1 Y 4 H 10 H 1 Y 3 H 10 Y 5 H 7 H 1 H 1 Y 2 Y 4 Y Y 4 Y Y 3 Y 1 Y.

Definition cf264 := Config* 5 30
  H 2 H 12 Y 3 H 11 Y 3 H 10 Y 3 H 9 Y 5 H 8 H 8 H 8 Y 4 Y Y 4 Y 1 Y 2 Y 1 Y.

Definition cf265 := Config 14 29 31
  H 4 H 12 H 12 H 12 Y 10 H 1 Y 8 H 2 H 10 Y 8 H 1 Y 8 Y 5 Y 1 Y Y Y 3 Y Y.

Definition cf266 := Config 1 2 32
  H 11 H 1 Y 3 H 11 Y 3 H 10 Y 3 H 9 Y 4 H 1 Y 4 Y 3 H 1 Y 5 H 1 Y 3 Y 1 Y 1 Y.

Definition cf267 := Config 35
  H 9 H 3 H 12 H 12 Y 9 H 2 H 11 Y 9 H 1 Y 7 H 1 H 1 Y 7 Y Y Y 3 Y 1 Y 1 Y 2 Y.

Definition cf268 := Config 32
  H 2 H 12 Y 5 H 9 H 1 H 1 Y 3 H 10 Y 3 H 9 Y 3 H 1 Y 1 Y 1 Y 5 H 5 Y 2 Y Y 2 Y.

Definition cf269 := Config 33
  H 10 H 1 H 1 Y 3 H 11 Y 3 H 10 Y 5 H 1 Y 3 Y 5 H 7 H 7 H 7 Y Y 1 Y 3 Y Y Y.

Definition cf270 := Config 33
  H 12 H 1 Y 11 H 1 Y 9 H 10 H 1 Y 9 H 1 Y 9 H 9 H 9 Y 7 H 1 Y 1 Y Y Y 4 Y Y Y.

Definition cf271 := Config 18 19 33
  H 3 H 11 H 1 Y 3 H 11 Y 3 H 3 H 9 H 1 Y 3 H 9 Y 6 H 1 Y 1 Y Y 3 Y 1 Y 1 Y 2 Y.

Definition cf272 := Config 31
  H 11 H 1 Y 9 H 2 H 11 Y 9 H 1 Y 8 H 1 Y 6 H 8 Y 2 H 7 Y Y Y 2 H 1 Y 1 Y Y.

Definition cf273 := Config 8
  H 9 H 1 H 1 H 1 Y 3 H 11 Y 6 H 7 H 1 H 1 H 1 Y 2 Y 4 Y Y 1 Y 1 Y 3 Y Y Y.

Definition cf274 := Config 36
  H 2 H 12 Y 4 H 10 H 1 Y 3 H 10 Y 3 H 9 Y 4 H 1 Y 6 H 1 H 1 Y 1 Y 1 Y 3 Y 1 Y 2
  Y.

Definition cf275 := Config 26
  H 11 H 1 Y 8 H 10 H 1 Y 8 H 2 H 10 Y 9 Y 5 H 8 Y Y Y 3 H 1 Y 4 H 1 Y 3 Y 1 Y.

Definition cf276 := Config 6
  H 11 H 1 Y 3 H 11 Y 3 H 10 Y 6 H 1 Y 5 H 8 Y 4 H 7 H 7 H 7 Y Y 1 Y 3 Y Y Y.

Definition cf277 := Config 36
  H 12 H 1 Y 11 H 1 Y 10 H 10 H 1 Y 7 H 3 H 10 H 10 H 9 H 1 Y 8 Y 1 Y 1 Y Y Y 4 
  Y Y Y.

Definition cf278 := Config 30
  H 2 H 13 Y 3 H 12 Y 5 H 2 H 11 Y 3 H 10 H 2 H 10 Y 3 Y Y Y 1 Y 3 H 5 H 5 Y 3 Y
  Y Y.

Definition cf279 := Config 40
  H 4 H 11 H 1 H 1 Y 3 H 12 Y 3 H 2 H 11 Y 2 H 10 Y 9 H 1 Y 1 Y 2 H 7 Y 2 Y Y 3 
  Y Y 2 Y.

Definition cf280 := Config 39
  H 2 H 13 Y 3 H 2 H 12 Y 4 H 10 H 1 Y 5 H 1 Y 9 H 1 Y 7 H 1 H 1 Y 1 Y 1 Y 4 Y 1
  Y 3 Y Y.

Definition cf281 := Config 27 30 33
  H 12 H 1 Y 11 H 1 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 7 H 7 Y 6 Y 4 Y Y 3 Y 1
  Y.

Definition cf282 := Config 21
  H 2 H 13 Y 4 H 11 H 1 Y 3 H 11 Y 3 H 10 Y 3 H 9 Y 2 H 8 Y 2 H 7 Y 5 Y 5 Y Y 3 
  Y 1 Y.

Definition cf283 := Config 7
  H 3 H 13 H 13 Y 10 H 2 H 12 Y 9 H 2 H 11 Y 8 H 2 H 10 Y 9 Y 7 Y Y 3 Y 2 Y 2 Y 
  3 Y 2 Y.

Definition cf284 := Config 36
  H 10 H 3 H 13 H 13 Y 11 H 1 Y 10 H 1 Y 9 H 1 Y 7 H 1 H 1 Y 7 Y Y Y 3 Y 1 Y 1 Y
  2 Y.

Definition cf285 := Config 21
  H 2 H 12 Y 4 H 10 H 1 Y 3 H 10 Y 3 H 9 Y 4 H 8 H 8 Y 3 Y 1 Y 5 H 5 Y 2 Y Y 2
  Y.

Definition cf286 := Config 31
  H 2 H 13 Y 3 H 12 Y 4 H 10 H 1 Y 3 H 10 Y 3 H 9 Y 3 H 1 Y 7 H 7 Y 3 Y 1 Y Y Y 
  2 Y.

Definition cf287 := Config 28 33 37
  H 12 H 1 Y 9 H 3 H 12 H 12 Y 10 H 1 Y 9 H 1 Y 7 H 1 H 1 Y 7 Y Y Y 3 Y 2 Y 2 Y 
  1 Y.

Definition cf288 := Config 6 12 32 34
  H 3 H 13 H 13 Y 11 H 1 Y 8 H 3 H 11 H 11 Y 8 H 2 H 10 Y 9 Y 7 Y Y Y 3 Y 2 Y Y 
  2 Y.

Definition cf289 := Config 37
  H 12 H 1 Y 11 H 1 Y 10 H 1 Y 9 H 1 Y 7 H 2 H 9 Y 8 H 8 H 8 Y 3 Y Y 2 Y 3 Y Y 1
  Y.

Definition cf290 := Config 27
  H 12 H 1 Y 11 H 11 H 1 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 8 H 8 Y 7 H 7 Y 2 Y Y 3 Y Y 
  Y.

Definition cf291 := Config 36
  H 11 H 1 H 1 Y 4 H 11 H 1 Y 3 H 11 Y 5 H 8 H 1 H 1 Y 2 Y 3 Y 2 Y 4 Y Y 3 Y 1 Y
  1 Y.

Definition cf292 := Config 18 19 37
  H 3 H 13 H 13 Y 10 H 2 H 12 Y 10 H 10 H 1 Y 9 H 1 Y 9 Y 7 Y 6 H 1 Y 1 Y Y 3 Y 
  1 Y 2 Y.

Definition cf293 := Config 34
  H 11 H 1 H 1 Y 3 H 12 Y 3 H 11 Y 4 H 2 H 10 Y 2 Y 3 Y 4 H 7 H 7 Y Y 1 Y 3 Y Y 
  Y.

Definition cf294 := Config 28 34 36
  H 11 H 2 H 13 Y 10 H 2 H 12 Y 10 H 1 Y 8 H 2 H 10 Y 8 H 1 Y 3 Y Y 5 Y Y Y 3 Y 
  1 Y.

Definition cf295 := Config 33
  H 10 H 1 H 1 H 1 Y 3 H 12 Y 3 H 11 Y 5 H 8 H 1 H 1 Y 2 Y 4 Y Y 5 Y Y 3 Y 1 Y 1
  Y.

Definition cf296 := Config 31
  H 2 H 13 Y 3 H 12 Y 3 H 11 Y 4 H 9 H 1 Y 2 H 1 H 1 H 1 Y 6 Y 1 Y 1 Y 3 Y 3 Y Y
  2 Y.

Definition cf297 := Config 8 9 30 37
  H 2 H 13 Y 3 H 12 Y 4 H 10 H 1 Y 3 H 10 Y 4 H 8 H 1 Y 7 Y 1 Y 1 Y 2 H 1 Y 1 Y 
  Y Y.

Definition cf298 := Config 26 33 35
  H 2 H 13 Y 3 H 12 Y 5 H 9 H 1 H 1 Y 3 H 10 Y 2 H 1 H 1 Y 6 Y 1 Y 1 Y Y Y 3 Y
  Y.

Definition cf299 := Config 13 31 37
  H 12 H 1 Y 11 H 1 Y 9 H 2 H 11 Y 9 H 1 Y 8 H 1 Y 5 Y 2 H 7 Y Y Y 2 H 1 Y 1 Y
  Y.

Definition cf300 := Config 35
  H 2 H 13 Y 4 H 11 H 1 Y 3 H 2 H 11 Y 3 H 10 Y 2 H 1 Y 7 Y 7 H 7 Y 3 Y Y Y 3 Y 
  Y.

Definition cf301 := Config 17
  H 12 H 1 Y 8 H 4 H 12 H 12 H 12 Y 9 H 2 H 11 Y 9 H 1 Y 9 Y 4 Y Y 4 Y Y 3 Y 1 Y
  1 Y.

Definition cf302 := Config 18 19 37
  H 2 H 13 Y 3 H 12 Y 5 H 9 H 1 H 1 Y 3 H 10 Y 3 H 9 Y 2 H 8 Y Y 1 Y 3 Y 1 Y Y 1
  Y.

Definition cf303 := Config* 24 29 37
  H 12 H 1 Y 3 H 12 Y 3 H 11 Y 7 H 6 H 1 H 1 H 1 H 1 Y 2 Y 4 Y 1 Y 4 Y Y 3 Y 1 Y
  1 Y.

Definition cf304 := Config* 32
  H 12 H 1 Y 3 H 12 Y 3 H 11 Y 3 H 10 Y 3 H 2 H 9 Y 2 Y Y 4 Y 1 H 5 Y 1 H 1 Y 1 
  Y Y.

Definition cf305 := Config 37
  H 2 H 13 Y 3 H 12 Y 5 H 2 H 11 Y 4 H 10 H 10 Y 3 Y 5 H 8 H 8 H 8 Y Y 1 Y 4 Y Y
  Y Y.

Definition cf306 := Config 35
  H 12 H 1 Y 8 H 4 H 12 H 12 H 12 Y 10 H 1 Y 9 H 1 Y 6 Y Y 2 H 7 Y Y Y 2 H 1 Y 1
  Y Y.

Definition cf307 := Config 36
  H 2 H 13 Y 4 H 2 H 12 Y 3 H 11 Y 5 H 10 H 10 H 10 H 1 H 1 Y 2 Y Y Y 1 Y 2 H 5 
  Y 3 Y Y Y.

Definition cf308 := Config 7
  H 5 H 13 H 13 H 13 H 13 Y 11 H 1 Y 9 H 2 H 11 Y 9 H 1 Y 9 Y 7 H 8 Y Y 1 Y 4 Y 
  Y Y Y.

Definition cf309 := Config 30
  H 2 H 13 Y 3 H 12 Y 3 H 11 Y 3 H 10 Y 3 H 9 Y 2 H 1 H 1 H 8 H 8 Y Y 1 Y 3 Y 3 
  Y Y 2 Y.

Definition cf310 := Config 7
  H 3 H 13 H 13 Y 9 H 3 H 12 H 12 Y 9 H 2 H 11 Y 9 H 1 Y 9 Y 6 H 8 Y 2 Y Y 4 Y Y
  Y Y.

Definition cf311 := Config 34
  H 2 H 13 Y 3 H 12 Y 3 H 11 Y 3 H 10 Y 5 H 7 H 1 H 1 Y H 8 Y 3 H 7 Y Y 3 Y 3 Y 
  Y 2 Y.

Definition cf312 := Config 31
  H 12 H 1 Y 3 H 12 Y 3 H 11 Y 5 H 2 H 10 Y 2 Y 5 H 8 Y 2 H 1 H 7 H 7 Y Y 1 Y 3 
  Y Y Y.

Definition cf313 := Config 42
  H 2 H 13 Y 3 H 12 Y 3 H 11 Y 3 H 10 Y 6 H 1 Y 5 H 1 H 1 H 1 H 1 Y 7 H 7 Y Y 3 
  Y Y 3 Y Y.

Definition cf314 := Config 33
  H 2 H 13 Y 3 H 12 Y 5 H 9 H 1 H 1 Y 3 H 10 Y 4 H 9 H 9 H 1 H 1 Y 1 Y Y 5 Y Y 3
  Y 1 Y 1 Y.

Definition cf315 := Config 42
  H 12 H 1 Y 11 H 1 Y 10 H 1 Y 9 H 1 Y 8 H 9 H 9 H 9 H 2 H 9 Y 3 H 8 Y Y 6 Y 4 Y
  3 Y 2 Y Y.

Definition cf316 := Config 6
  H 12 H 1 Y 3 H 12 Y 3 H 11 Y 7 H 1 Y 5 H 9 Y 5 H 8 H 8 H 8 H 8 Y 2 H 1 Y 2 Y 3
  Y 1 Y 2 Y Y.

Definition cf317 := Config 46
  H 12 H 1 Y 11 H 1 Y 10 H 1 Y 9 H 1 Y 5 H 1 H 1 H 1 H 1 H 9 H 9 Y 8 H 1 Y 1 Y 2
  Y 4 Y Y 3 Y 2 Y.

Definition cf318 := Config 37
  H 3 H 13 H 13 Y 10 H 2 H 12 Y 10 H 1 Y 7 H 3 H 10 H 10 Y 9 Y 7 Y Y 6 Y 4 Y 1 Y
  2 Y 1 Y.

Definition cf319 := Config 35
  H 12 H 1 Y 11 H 1 Y 10 H 10 H 1 Y 9 H 1 Y 8 H 1 Y 8 H 8 Y 6 H 1 Y 1 Y Y 2 Y 2 
  Y 2 Y.

Definition cf320 := Config 14 32 34
  H 4 H 13 H 13 H 13 Y 11 H 1 Y 9 H 2 H 11 Y 8 H 2 H 10 Y 9 Y 6 Y 1 Y Y Y 3 Y 1 
  Y 2 Y.

Definition cf321 := Config 1 2 35
  H 2 H 13 Y 11 H 1 Y 10 H 1 Y 8 H 8 H 2 H 10 Y 9 Y 5 H 1 Y 7 H 1 Y 1 Y Y 3 Y 1 
  Y 2 Y.

Definition cf322 := Config 32
  H 12 H 1 Y 11 H 1 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 8 H 8 H 8 H 8 Y 2 H 1 Y 1 Y Y 3 Y
  1 Y 1 Y.

Definition cf323 := Config 30
  H 12 H 1 Y 9 H 3 H 12 H 12 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 8 H 8 Y 7 H 7 Y 2 Y Y 3 
  Y Y Y.

Definition cf324 := Config* 6
  H 2 H 8 Y 6 H 1 Y 6 H 6 H 6 H 6 Y 4 Y Y Y Y.

Definition cf325 := Config* 21
  H 7 H 2 H 9 Y 7 H 6 H 2 H 8 Y 7 H 7 Y Y Y Y Y Y.

Definition cf326 := Config* 29
  H 4 H 7 H 1 H 1 Y 4 H 1 H 1 H 1 Y 1 Y 1 Y 1 Y 2 H 4 Y 2 Y 1 Y.

Definition cf327 := Config 23
  H 8 H 1 Y 3 H 8 Y 5 H 5 H 1 H 1 Y 2 Y 3 Y 1 Y 1 Y 2 Y.

Definition cf328 := Config* 0 23
  H 8 H 1 Y 3 H 8 Y 4 H 6 H 1 Y 2 H 1 Y 3 Y 1 Y 3 Y Y.

Definition cf329 := Config 6
  H 2 H 9 Y 7 H 1 Y 4 H 7 Y 4 H 1 Y 5 H 1 Y 4 H 1 Y 3 Y 1 Y.

Definition cf330 := Config* 14 15 21 26
  H 3 H 9 H 1 Y 3 H 2 H 9 Y 3 H 8 Y 2 H 1 Y 1 Y 1 Y 1 Y 1 Y 2 Y.

Definition cf331 := Config 30
  H 2 H 10 Y 4 H 4 H 7 H 1 H 1 Y 5 H 1 H 1 Y 1 Y 1 Y 1 Y 1 Y 2 Y 1 Y.

Definition cf332 := Config 30
  H 9 H 1 Y 7 H 2 H 9 Y 6 H 1 H 7 H 1 Y 7 H 1 Y 1 Y 1 Y 1 Y 1 Y 2 Y.

Definition cf333 := Config 25
  H 9 H 1 Y 7 H 1 H 8 H 1 Y 7 H 1 H 1 Y 1 Y 1 Y 4 H 1 Y 4 H 1 Y 3 Y 1 Y.

Definition cf334 := Config* 24
  H 9 H 1 Y 3 H 9 Y 3 H 8 Y 4 H 6 H 1 Y 2 Y 3 Y 1 Y 1 Y 2 Y.

Definition cf335 := Config 6
  H 2 H 10 Y 8 H 1 Y 4 H 4 H 8 H 8 H 8 Y 7 Y 5 Y Y Y 3 Y 1 Y.

Definition cf336 := Config 18
  H 9 H 1 Y 7 H 2 H 9 Y 6 H 2 H 8 Y 6 H 1 Y 5 Y Y 3 Y Y 2 Y.

Definition cf337 := Config 6
  H 2 H 10 Y 8 H 1 Y 6 H 2 H 8 Y 6 H 7 Y 5 Y Y 4 H 4 Y 2 Y Y.

Definition cf338 := Config 27
  H 2 H 10 Y 8 H 1 Y 5 H 3 H 8 H 8 Y 7 H 7 Y 5 Y Y 2 Y 2 Y 1 Y.

Definition cf339 := Config 12
  H 2 H 10 Y 4 H 8 H 1 Y 3 H 2 H 8 Y 2 Y 5 H 1 Y 5 Y 1 Y 2 Y 2 Y.

Definition cf340 := Config 6
  H 2 H 10 Y 8 H 1 Y 7 H 1 Y 5 H 7 Y 5 Y 5 H 1 Y 4 H 1 Y 3 Y 1 Y.

Definition cf341 := Config* 26
  H 8 H 1 H 1 Y 3 H 9 Y 5 H 6 H 1 H 1 Y 2 Y 3 Y 1 Y 1 Y 1 Y 2 Y.

Definition cf342 := Config 12 13 28
  H 9 H 1 Y 8 H 1 Y 7 H 1 Y 6 H 6 H 1 Y 5 Y 4 H 5 Y Y 1 Y 2 Y.

Definition cf343 := Config* 1 2 8 9
  H 2 H 11 Y 3 H 10 Y 3 H 4 H 7 H 1 H 1 Y 6 H 1 Y 1 Y 1 Y 1 Y 1 Y 2 Y 1 Y.

Definition cf344 := Config 6
  H 2 H 9 Y 7 H 1 Y 4 H 7 Y 4 H 1 Y 4 H 1 H 1 Y H 4 Y Y 1 Y.

Definition cf345 := Config 25
  H 10 H 1 Y 9 H 9 H 1 Y 7 H 2 H 9 Y 4 H 8 Y Y Y Y 4 H 1 Y 3 Y 1 Y.

Definition cf346 := Config 28
  H 2 H 11 Y 4 H 2 H 10 Y 4 H 8 H 1 Y 5 H 1 H 1 Y 1 Y 1 Y 1 Y 1 Y 2 Y 1 Y.

Definition cf347 := Config 4 5 24 29
  H 2 H 11 Y 3 H 10 Y 3 H 3 H 8 H 1 Y 2 H 1 H 1 Y 1 Y 1 Y 1 Y 1 Y 2 Y 1 Y.

Definition cf348 := Config 25
  H 4 H 9 H 1 H 1 Y 3 H 2 H 10 Y 3 H 9 Y 7 H 8 Y Y Y Y 4 H 1 Y 3 Y 1 Y.

Definition cf349 := Config* 24
  H 8 H 2 H 10 Y 8 H 6 H 3 H 9 H 9 Y 8 H 8 Y Y Y Y 4 H 4 Y 2 Y Y.

Definition cf350 := Config 18
  H 8 H 2 H 10 Y 6 H 8 H 1 Y 8 H 8 Y Y Y 4 H 1 H 1 Y H 4 Y Y 1 Y.

Definition cf351 := Config 34
  H 2 H 11 Y 3 H 2 H 10 Y 4 H 1 H 7 H 1 H 1 Y 2 H 8 Y 2 Y Y 1 Y 1 Y 2 Y 1 Y.

Definition cf352 := Config 21
  H 10 H 1 Y 8 H 9 H 1 Y 8 H 9 H 2 H 9 Y 8 H 1 Y 7 Y 1 Y Y 4 H 1 Y 3 Y 1 Y.

Definition cf353 := Config 29
  H 10 H 1 Y 9 H 9 H 1 Y 7 H 1 H 8 H 1 Y 8 H 1 Y 1 Y 1 Y 5 Y 4 H 4 Y 2 Y Y.

Definition cf354 := Config 11
  H 10 H 1 Y 8 H 2 H 10 Y 6 H 1 H 8 H 1 Y 8 H 1 Y 1 Y 2 H 6 Y 5 Y 3 Y Y 2 Y.

Definition cf355 := Config 25
  H 9 H 1 Y 7 H 1 H 8 H 1 Y 7 H 1 H 1 Y 1 Y 1 Y 3 H 1 H 1 Y H 4 Y Y 1 Y.

Definition cf356 := Config 27
  H 3 H 11 H 11 Y 9 H 1 Y 7 H 2 H 9 Y 7 H 1 Y 7 Y 5 Y Y Y 2 Y 2 Y.

Definition cf357 := Config 12 13 29
  H 10 H 1 Y 9 H 1 Y 8 H 1 Y 6 H 2 H 8 Y 6 H 1 Y 5 Y 3 Y Y 3 Y Y.

Definition cf358 := Config 16 17 28
  H 2 H 11 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 6 H 7 Y 5 Y 4 H 5 Y 3 Y Y Y.

Definition cf359 := Config 19
  H 2 H 11 Y 9 H 1 Y 8 H 1 Y 6 H 2 H 8 Y 7 H 7 Y 5 Y 2 Y 2 Y 2 Y Y.

Definition cf360 := Config 6
  H 2 H 11 Y 9 H 1 Y 6 H 8 H 1 Y 8 Y 5 H 1 Y 6 H 1 Y 5 H 1 Y 4 Y Y 1 Y.

Definition cf361 := Config 26
  H 10 H 1 Y 6 H 4 H 10 H 10 H 10 Y 8 H 1 Y 7 H 1 Y 6 Y Y Y 3 Y 1 Y 1 Y.

Definition cf362 := Config 28
  H 2 H 11 Y 9 H 1 Y 7 H 2 H 9 Y 7 H 8 H 8 Y 6 Y Y 5 H 5 Y Y 2 Y Y.

Definition cf363 := Config 6
  H 2 H 10 Y 8 H 1 Y 4 H 4 H 8 H 8 H 8 Y 7 Y 5 Y Y 4 H 1 Y 3 Y 1 Y.

Definition cf364 := Config 6
  H 2 H 11 Y 9 H 1 Y 6 H 3 H 9 H 9 Y 7 H 8 Y 6 Y Y 4 H 1 Y 4 Y 2 Y Y.

Definition cf365 := Config 21
  H 2 H 11 Y 9 H 1 Y 8 H 6 H 3 H 9 H 9 Y 8 Y 5 H 1 Y 6 Y 1 Y 3 Y 2 Y Y.

Definition cf366 := Config 29
  H 3 H 11 H 11 Y 9 H 1 Y 5 H 4 H 9 H 9 H 9 Y 8 Y 6 Y Y Y Y 3 Y 1 Y.

Definition cf367 := Config 32
  H 10 H 1 Y 7 H 3 H 10 H 10 Y 8 H 1 Y 7 H 1 Y 7 H 7 Y Y Y Y 2 Y 2 Y.

Definition cf368 := Config 6
  H 2 H 10 Y 8 H 1 Y 7 H 1 Y 5 H 7 Y 5 Y 4 H 1 H 1 Y H 4 Y Y 1 Y.

Definition cf369 := Config 31
  H 2 H 11 Y 9 H 1 Y 8 H 1 Y 5 H 8 Y 6 Y 5 H 1 H 5 H 1 Y 2 Y Y 3 Y 1 Y.

Definition cf370 := Config 6
  H 2 H 11 Y 9 H 1 Y 7 H 2 H 9 Y 6 H 8 Y 6 Y 4 H 1 H 1 Y 1 Y Y 3 Y 1 Y.

Definition cf371 := Config* 4 5 24 29
  H 10 H 1 Y 9 H 1 Y 8 H 6 H 3 H 9 H 9 Y 8 H 8 Y Y Y Y 4 H 4 Y 2 Y Y.

Definition cf372 := Config 4 5 18 23
  H 10 H 1 Y 9 H 1 Y 6 H 8 H 1 Y 8 H 8 Y Y Y 4 H 1 H 1 Y H 4 Y Y 1 Y.

Definition cf373 := Config 33
  H 2 H 12 Y 3 H 2 H 11 Y 3 H 2 H 10 Y 2 H 1 H 1 Y 2 H 1 Y 7 Y 1 Y 1 Y 1 Y 2 Y 1
  Y.

Definition cf374 := Config 30
  H 11 H 1 Y 10 H 10 H 1 Y 8 H 9 H 1 Y 9 H 9 Y 8 H 8 Y 2 Y Y Y 4 H 1 Y 3 Y 1 Y.

Definition cf375 := Config 37
  H 2 H 11 Y 3 H 2 H 10 Y 4 H 2 H 6 H 1 H 2 H 9 Y 1 H 1 Y 1 Y Y 1 Y 1 Y 2 Y 1 Y.

Definition cf376 := Config 21
  H 10 H 1 Y 8 H 9 H 1 Y 8 H 8 H 3 H 8 H 1 Y H 8 Y Y 1 Y Y 4 H 1 Y 3 Y 1 Y.

Definition cf377 := Config 29
  H 2 H 12 Y 10 H 1 Y 8 H 2 H 10 Y 8 H 8 H 1 Y 8 Y 6 Y Y 5 H 5 Y 2 Y 3 Y 1 Y.

Definition cf378 := Config 18
  H 11 H 1 Y 9 H 2 H 11 Y 8 H 2 H 10 Y 8 H 1 Y 7 H 1 Y 6 Y Y 3 Y 3 Y 3 Y 1 Y.

Definition cf379 := Config 30
  H 11 H 1 Y 10 H 1 Y 7 H 3 H 10 H 10 Y 8 H 1 Y 7 H 1 Y 6 Y Y Y 3 Y 1 Y 1 Y.

Definition cf380 := Config 30 33
  H 3 H 12 H 12 Y 10 H 1 Y 8 H 2 H 10 Y 7 H 2 H 9 Y 8 Y 6 Y Y Y 3 Y 2 Y Y.

Definition cf381 := Config 31
  H 3 H 12 H 12 Y 10 H 1 Y 9 H 1 Y 6 H 3 H 9 H 9 Y 8 Y 6 Y Y Y Y 3 Y 1 Y.

Definition cf382 := Config 25
  H 2 H 12 Y 10 H 1 Y 8 H 2 H 10 Y 6 H 3 H 9 H 9 Y 8 Y 6 Y 6 Y 4 Y 3 Y Y Y.

Definition cf383 := Config 14
  H 10 H 1 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 7 H 1 Y 5 H 1 H 1 Y H 5 Y Y Y 1 Y.

Definition cf384 := Config 33
  H 11 H 1 Y 7 H 4 H 11 H 11 H 11 Y 9 H 1 Y 8 H 1 Y 6 Y Y Y 2 H 1 Y 1 Y 1 Y 1 Y.

Definition cf385 := Config 32
  H 11 H 1 Y 7 H 4 H 11 H 11 H 11 Y 9 H 1 Y 7 H 1 H 1 Y 7 Y Y Y Y 3 Y 1 Y 1 Y.

Definition cf386 := Config 29
  H 11 H 1 Y 8 H 3 H 11 H 11 Y 8 H 2 H 10 Y 8 H 1 Y 8 H 8 Y Y Y Y 3 Y 2 Y Y.

Definition cf387 := Config 6
  H 2 H 11 Y 7 H 3 H 10 H 10 Y 6 H 3 H 9 H 9 Y 8 Y 6 H 7 Y Y 1 Y 3 Y 2 Y Y.

Definition cf388 := Config 6
  H 2 H 11 Y 9 H 1 Y 4 H 5 H 9 H 9 H 9 H 9 Y 8 Y 5 H 7 Y 2 Y Y 3 Y 2 Y Y.

Definition cf389 := Config 18
  H 2 H 11 Y 5 H 2 H 10 Y 3 H 9 Y 2 Y 5 H 1 Y 1 Y 4 H 1 H 1 Y H 4 Y Y 1 Y.

Definition cf390 := Config* 25
  H 10 H 1 Y 9 H 9 H 1 Y 7 H 1 H 8 H 1 Y 2 H 8 Y Y Y 4 H 1 H 1 Y H 4 Y Y 1 Y.

Definition cf391 := Config* 36
  H 2 H 11 Y 3 H 2 H 10 Y 6 H 9 H 7 H 1 H 1 H 1 H 1 Y 1 Y Y 1 Y 1 Y 4 H 4 Y Y 1 
  Y.

Definition cf392 := Config 27
  H 10 H 1 Y 9 H 7 H 3 H 10 H 10 Y 7 H 1 H 1 H 9 H 9 Y Y 1 Y Y Y 4 H 4 Y 2 Y Y.

Definition cf393 := Config 21
  H 10 H 1 Y 7 H 9 H 1 Y 7 H 1 H 1 H 9 H 9 Y Y 1 Y Y 4 H 1 H 1 Y H 4 Y Y 1 Y.

Definition cf394 := Config 16 17 32
  H 2 H 13 Y 11 H 1 Y 10 H 1 Y 9 H 1 Y 8 H 8 H 1 Y 8 Y 6 Y 5 H 6 Y 3 Y Y 3 Y 1
  Y.

Definition cf395 := Config 30
  H 2 H 12 Y 5 H 9 H 1 H 1 Y 3 H 10 Y 3 H 9 Y 2 H 1 Y 2 Y 1 Y 5 H 5 Y Y Y 1 Y.

Definition cf396 := Config 18
  H 11 H 1 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 7 H 1 Y 6 H 1 Y H 5 Y Y Y 1 Y.

Definition cf397 := Config 34
  H 11 H 1 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 6 H 1 H 7 H 7 Y Y Y 1 Y 1 Y 2 Y.

Definition cf398 := Config 33
  H 12 H 1 Y 10 H 2 H 12 Y 9 H 2 H 11 Y 9 H 1 Y 8 H 1 Y 6 Y Y 2 H 1 Y 4 Y 3 Y 1 
  Y 1 Y.

Definition cf399 := Config 18
  H 12 H 1 Y 11 H 1 Y 10 H 9 H 2 H 11 Y 9 H 1 Y 8 H 1 Y 5 H 1 Y 1 Y Y 3 Y 3 Y 3 
  Y 1 Y.

Definition cf400 := Config 26
  H 11 H 1 Y 10 H 10 H 1 Y 9 H 9 H 1 Y 8 H 9 Y 2 H 8 Y Y Y 4 H 1 H 1 Y H 4 Y Y 1
  Y.

Definition cf401 := Config 6
  H 2 H 13 Y 9 H 3 H 12 H 12 Y 10 H 1 Y 7 H 3 H 10 H 10 Y 9 Y 7 H 8 Y 4 Y 4 Y Y 
  1 Y Y Y.

Definition cf402 := Config 27
  H 2 H 10 Y 5 H 7 H 1 H 1 Y 3 H 8 Y 3 H 7 Y 3 Y 1 Y 1 Y 2 Y 1 Y.

Definition cf403 := Config 26
  H 9 H 1 Y 3 H 9 Y 4 H 2 H 8 Y 2 Y 4 H 6 Y 2 H 5 Y 2 Y Y 2 Y.

Definition cf404 := Config 0 23
  H 9 H 1 Y 3 H 9 Y 4 H 7 H 1 Y 3 H 7 Y 5 Y 1 Y 3 H 1 Y 3 Y 1 Y.

Definition cf405 := Config 6
  H 2 H 10 Y 8 H 1 Y 4 H 8 Y 5 H 1 Y 6 H 1 Y 4 H 1 H 1 Y 3 Y 1 Y 1 Y.

Definition cf406 := Config 21
  H 8 H 3 H 11 H 11 Y 7 H 9 H 1 Y 9 H 9 Y Y Y Y 4 H 1 H 1 Y 3 Y 1 Y 1 Y.

Definition cf407 := Config 18
  H 9 H 2 H 11 Y 6 H 9 H 1 Y 9 H 9 Y Y Y 6 H 1 Y 4 H 1 H 1 Y 3 Y 1 Y 1 Y.

Definition cf408 := Config 34
  H 3 H 10 H 1 Y 3 H 10 Y 5 H 9 H 2 H 9 Y 2 H 8 Y Y 6 H 1 Y 2 Y 1 Y 2 Y 1 Y.

Definition cf409 := Config 25
  H 10 H 1 Y 8 H 1 H 9 H 1 Y 8 H 1 H 1 Y 1 Y 1 Y 5 H 1 Y 4 H 1 H 1 Y 3 Y 1 Y 1
  Y.

Definition cf410 := Config 1 2 28
  H 10 H 1 Y 3 H 10 Y 5 H 7 H 1 H 1 Y 3 H 8 Y 2 Y 3 Y 1 Y 1 Y 2 Y 1 Y.

Definition cf411 := Config 27
  H 2 H 11 Y 3 H 10 Y 4 H 8 H 1 Y 3 H 8 Y 3 H 7 Y 3 Y 1 Y 1 Y 2 Y 1 Y.

Definition cf412 := Config 28
  H 10 H 1 Y 3 H 10 Y 3 H 9 Y 3 H 2 H 8 Y 2 Y 3 Y 2 H 1 Y 4 Y 1 Y 2 Y.

Definition cf413 := Config 25
  H 2 H 11 Y 6 H 7 H 1 H 1 H 1 Y 3 H 9 Y 3 H 8 Y 3 Y 1 Y 1 Y 2 Y 1 Y 1 Y.

Definition cf414 := Config 27
  H 2 H 11 Y 5 H 8 H 1 H 1 Y 3 H 9 Y 3 H 8 Y 4 Y 1 Y 1 Y 4 H 4 Y Y 1 Y.

Definition cf415 := Config 6
  H 2 H 11 Y 9 H 1 Y 6 H 8 H 1 Y 8 Y 5 H 1 Y 6 H 1 Y 5 H 1 Y 3 Y 1 Y 1 Y.

Definition cf416 := Config 6
  H 2 H 11 Y 9 H 1 Y 4 H 5 H 9 H 9 H 9 H 9 Y 8 Y 6 Y Y Y 3 Y 1 Y 1 Y.

Definition cf417 := Config 31
  H 3 H 11 H 11 Y 6 H 4 H 10 H 10 H 10 Y 8 H 1 Y 8 Y 6 Y Y Y 2 Y 2 Y 1 Y.

Definition cf418 := Config 32
  H 8 H 3 H 11 H 11 Y 9 H 1 Y 8 H 1 Y 6 H 1 H 1 Y 6 Y Y Y 3 Y Y 2 Y.

Definition cf419 := Config 29
  H 10 H 1 Y 3 H 10 Y 4 H 2 H 9 Y 2 H 1 Y 4 H 7 Y 2 H 6 Y 3 Y Y Y 2 Y.

Definition cf420 := Config 32
  H 10 H 1 Y 8 H 2 H 10 Y 7 H 2 H 9 Y 6 H 2 H 8 Y 6 Y Y 4 Y Y Y 2 Y.

Definition cf421 := Config 6
  H 2 H 11 Y 9 H 1 Y 7 H 2 H 9 Y 6 H 8 Y 6 Y Y 4 H 5 Y 2 H 4 Y 2 Y Y.

Definition cf422 := Config 31
  H 10 H 1 Y 7 H 3 H 10 H 10 Y 7 H 2 H 9 Y 7 H 1 Y 6 Y Y 3 Y Y 2 Y 1 Y.

Definition cf423 := Config 26
  H 2 H 11 Y 4 H 9 H 1 Y 3 H 9 Y 3 H 2 H 8 Y 3 Y 1 Y 3 H 1 Y 1 Y 3 Y 1 Y.

Definition cf424 := Config 26
  H 9 H 1 Y 3 H 9 Y 4 H 7 H 1 Y 2 H 1 H 1 Y 3 Y 1 Y 2 H 1 Y 1 Y Y.

Definition cf425 := Config 26
  H 2 H 10 Y 4 H 8 H 1 Y 3 H 8 Y 4 H 6 H 1 Y 3 Y 1 Y 4 H 4 Y Y 1 Y.

Definition cf426 := Config 30
  H 10 H 1 Y 3 H 10 Y 5 H 7 H 1 H 1 Y 3 H 8 Y 5 Y 1 Y 4 H 1 Y 3 Y 1 Y 1 Y.

Definition cf427 := Config 28
  H 9 H 1 Y 3 H 9 Y 4 H 2 H 8 Y 2 Y 5 H 6 H 6 Y 1 H 1 Y 1 Y Y 2 Y.

Definition cf428 := Config 19
  H 2 H 11 Y 3 H 2 H 10 Y 4 H 8 H 1 Y 3 H 8 Y 4 H 7 Y 2 Y Y 3 Y 1 Y Y.

Definition cf429 := Config 27
  H 10 H 1 Y 3 H 10 Y 3 H 2 H 9 Y 3 H 1 Y 4 H 7 Y 2 Y Y 2 H 1 Y 1 Y Y.

Definition cf430 := Config 6
  H 2 H 11 Y 9 H 1 Y 8 H 1 Y 5 H 8 Y 6 Y 6 H 1 Y 4 H 1 H 1 Y 3 Y 1 Y 1 Y.

Definition cf431 := Config 30
  H 2 H 11 Y 5 H 8 H 1 H 1 Y 3 H 9 Y 4 H 8 H 8 Y 3 Y 1 Y 1 Y 1 Y 2 Y 1 Y.

Definition cf432 := Config 31
  H 10 H 1 Y 8 H 2 H 10 Y 8 H 1 Y 7 H 7 H 1 Y 6 Y 4 H 6 Y Y 1 Y 2 Y 1 Y.

Definition cf433 := Config 6
  H 10 H 1 Y 3 H 10 Y 3 H 9 Y 3 H 8 Y 3 H 1 Y 3 Y 4 H 1 Y H 4 Y Y 1 Y.

Definition cf434 := Config 1 2 9 22
  H 2 H 11 Y 3 H 10 Y 3 H 9 Y 4 H 2 H 8 Y 3 Y 3 H 1 H 1 Y 1 Y Y 3 Y 1 Y.

Definition cf435 := Config 11 12 30
  H 9 H 2 H 11 Y 9 H 9 H 1 Y 8 H 1 Y 7 H 1 Y 4 H 1 Y 1 Y Y 3 Y Y 2 Y.

Definition cf436 := Config 22
  H 10 H 2 H 12 Y 8 H 10 H 1 Y 9 H 1 Y 9 H 9 Y Y Y 6 H 1 Y 5 H 1 Y 3 Y 1 Y 1 Y.

Definition cf437 := Config 28
  H 10 H 2 H 12 Y 10 H 8 H 3 H 11 H 11 Y 9 H 1 Y 9 H 9 Y Y Y Y Y 3 Y 1 Y 1 Y.

Definition cf438 := Config 25
  H 11 H 1 Y 10 H 10 H 1 Y 8 H 2 H 10 Y 4 H 9 Y Y Y Y 4 H 1 H 1 Y 3 Y 1 Y 1 Y.

Definition cf439 := Config 35
  H 3 H 11 H 1 Y 3 H 11 Y 5 H 2 H 10 Y 9 H 1 Y 2 H 8 Y Y 6 H 1 Y 2 Y 1 Y 2 Y 1
  Y.

Definition cf440 := Config 12 28 32 35
  H 10 H 2 H 12 Y 10 H 1 Y 9 H 1 Y 7 H 1 H 8 H 1 Y 8 H 1 Y 1 Y 1 Y 5 Y 2 Y 2 Y 1
  Y.

Definition cf441 := Config 29
  H 11 H 1 Y 10 H 1 Y 8 H 1 H 9 H 1 Y 8 H 1 H 1 Y 1 Y 1 Y 5 H 1 Y 5 H 1 Y 3 Y 1 
  Y 1 Y.

Definition cf442 := Config 32
  H 2 H 11 Y 5 H 8 H 1 H 1 Y 4 H 9 H 2 H 9 Y 2 H 8 Y Y Y 2 Y 2 H 1 Y 1 Y Y.

Definition cf443 := Config 35
  H 2 H 11 Y 3 H 10 Y 6 H 9 H 2 H 9 Y 2 H 8 Y Y 5 H 1 H 1 Y 2 Y 4 H 4 Y Y 1 Y.

Definition cf444 := Config 6
  H 11 H 1 Y 3 H 11 Y 6 H 7 H 1 H 1 H 1 Y 3 H 9 Y 2 Y 3 Y 1 Y 1 Y 2 Y 1 Y 1 Y.

Definition cf445 := Config 23
  H 2 H 12 Y 10 H 1 Y 6 H 4 H 10 H 10 H 10 Y 8 H 1 Y 8 Y 6 Y Y Y 3 Y 1 Y 1 Y.

Definition cf446 := Config 8
  H 10 H 1 H 1 Y 5 H 9 H 1 H 1 Y 3 H 10 Y 3 H 9 Y 2 Y 3 Y 1 Y 1 Y 3 Y 3 Y 2 Y.

Definition cf447 := Config 8 9 30 32
  H 11 H 1 Y 9 H 2 H 11 Y 8 H 2 H 10 Y 8 H 1 Y 7 H 1 Y 6 Y Y 4 Y Y Y 2 Y.

Definition cf448 := Config 32
  H 2 H 12 Y 10 H 1 Y 8 H 2 H 10 Y 8 H 8 H 1 Y 8 Y 6 Y Y 3 Y 2 H 1 Y 3 Y 1 Y.

Definition cf449 := Config 33
  H 11 H 1 Y 3 H 11 Y 5 H 8 H 1 H 1 Y 4 H 8 H 1 Y 2 Y 3 Y 1 Y 2 Y 2 Y 3 Y 2 Y.

Definition cf450 := Config 30
  H 2 H 12 Y 10 H 1 Y 7 H 3 H 10 H 10 Y 8 H 1 Y 8 H 8 Y 6 Y Y 2 Y 2 Y 1 Y 1 Y.

Definition cf451 := Config 27
  H 10 H 1 Y 3 H 10 Y 4 H 8 H 1 Y 4 H 7 H 1 Y 2 Y 3 Y 1 Y 2 H 1 Y 1 Y Y.

Definition cf452 := Config 0 27
  H 2 H 11 Y 4 H 9 H 1 Y 3 H 9 Y 3 H 8 Y 3 H 7 Y 3 Y 1 Y 4 H 4 Y Y 1 Y.

Definition cf453 := Config 27
  H 10 H 1 Y 3 H 10 Y 4 H 8 H 1 Y 3 H 8 Y 2 H 1 Y 3 Y 1 Y 3 H 1 Y 3 Y 1 Y.

Definition cf454 := Config 15 30 33
  H 2 H 12 Y 3 H 11 Y 5 H 8 H 1 H 1 Y 3 H 9 Y 3 H 8 Y 3 Y 1 Y 1 Y 2 Y 1 Y 1 Y.

Definition cf455 := Config 27
  H 2 H 12 Y 3 H 11 Y 4 H 9 H 1 Y 3 H 9 Y 3 H 8 Y 4 Y 1 Y 1 Y 4 H 4 Y Y 1 Y.

Definition cf456 := Config 31
  H 2 H 12 Y 10 H 1 Y 9 H 1 Y 7 H 8 H 1 Y 8 Y 6 Y 6 H 1 Y 5 H 1 Y 3 Y 1 Y 1 Y.

Definition cf457 := Config 30
  H 2 H 12 Y 10 H 1 Y 9 H 1 Y 5 H 4 H 9 H 9 H 9 Y 8 Y 6 Y Y Y 3 Y 1 Y 1 Y.

Definition cf458 := Config 30
  H 10 H 1 H 1 Y 3 H 11 Y 4 H 9 H 1 Y 3 H 9 Y 2 H 1 Y 3 Y 1 Y 1 Y 4 Y 3 Y 1 Y.

Definition cf459 := Config 31
  H 10 H 1 H 1 Y 3 H 11 Y 5 H 8 H 1 H 1 Y 3 H 9 Y 2 Y 3 Y 1 Y 1 Y 1 Y 2 Y 1 Y.

Definition cf460 := Config 16 17 32
  H 2 H 12 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 6 H 8 Y 6 Y 4 H 6 Y 2 H 5 Y 3 Y Y Y.

Definition cf461 := Config 31
  H 2 H 12 Y 3 H 11 Y 4 H 9 H 1 Y 3 H 9 Y 4 H 8 H 8 Y 3 Y 1 Y 1 Y 1 Y 2 Y 1 Y.

Definition cf462 := Config 16 17 32
  H 2 H 11 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 7 H 7 H 7 Y 5 Y 4 H 5 Y Y 1 Y 2 Y.

Definition cf463 := Config 12 13 32
  H 10 H 1 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 5 H 2 H 7 Y 5 Y 2 H 1 Y 1 Y Y 2 Y.

Definition cf464 := Config 1 2 32
  H 11 H 1 Y 3 H 11 Y 4 H 9 H 1 Y 3 H 2 H 9 Y 2 Y 3 Y 3 H 6 Y Y 1 Y 2 Y 1 Y.

Definition cf465 := Config 26
  H 10 H 1 Y 3 H 10 Y 5 H 7 H 1 H 1 Y 3 H 8 Y 2 Y 3 Y 2 H 5 Y 2 Y Y 2 Y.

Definition cf466 := Config 23
  H 2 H 12 Y 4 H 10 H 1 Y 3 H 10 Y 4 H 8 H 1 Y 3 H 8 Y 3 Y 5 Y 1 Y 3 Y Y 2 Y.

Definition cf467 := Config 32
  H 2 H 12 Y 10 H 1 Y 8 H 2 H 10 Y 8 H 1 Y 7 H 8 Y 6 Y 4 H 6 Y Y 1 Y 2 Y 1 Y.

Definition cf468 := Config 33
  H 11 H 1 Y 3 H 11 Y 3 H 10 Y 3 H 9 Y 4 H 1 Y 3 Y 4 H 6 H 6 Y 3 Y 1 Y Y Y.

Definition cf469 := Config 1 2 13 23
  H 11 H 1 Y 3 H 11 Y 3 H 10 Y 3 H 9 Y 4 H 1 Y 3 Y 3 H 1 H 1 Y 1 Y Y 3 Y 1 Y.

Definition cf470 := Config 11 12 33
  H 10 H 2 H 12 Y 9 H 2 H 11 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 5 Y 1 Y 3 Y Y 3 Y Y.

Definition cf471 := Config 19 20 33
  H 11 H 1 Y 4 H 10 H 1 Y 3 H 10 Y 3 H 9 Y 3 H 1 Y 4 Y Y 3 H 1 Y 1 Y Y Y.

Definition cf472 := Config 33
  H 2 H 12 Y 5 H 9 H 1 H 1 Y 3 H 10 Y 2 H 1 H 1 H 1 Y 6 Y 1 Y 1 Y 3 Y Y 1 Y 1 Y.

Definition cf473 := Config 18
  H 11 H 1 Y 7 H 10 H 1 Y 9 H 1 Y 9 Y 7 H 8 H 8 H 8 H 8 Y Y 1 Y 4 Y Y Y Y.

Definition cf474 := Config 21
  H 2 H 12 Y 10 H 1 Y 9 H 6 H 4 H 10 H 10 H 10 Y 9 Y 6 H 1 Y 7 Y 1 Y 3 Y 1 Y 2 Y
  Y.

Definition cf475 := Config 8 33 36
  H 9 H 3 H 12 H 12 Y 10 H 1 Y 9 H 9 H 1 Y 8 H 1 Y 3 H 8 Y 3 Y Y Y 3 Y 1 Y Y.

Definition cf476 := Config 33
  H 3 H 12 H 12 Y 10 H 1 Y 5 H 5 H 10 H 10 H 10 H 10 Y 9 Y 7 Y Y Y Y 3 Y 1 Y 1 Y.

Definition cf477 := Config 33 36
  H 11 H 1 Y 9 H 2 H 11 Y 9 H 1 Y 8 H 7 H 1 H 1 Y 7 Y 4 H 7 Y Y 1 Y 2 Y 2 Y Y.

Definition cf478 := Config 30 32 36
  H 2 H 12 Y 4 H 10 H 1 Y 3 H 10 Y 4 H 9 H 9 Y 8 Y 5 H 7 H 7 Y Y 1 Y 2 Y 1 Y 1 Y.

Definition cf479 := Config 15 16 33
  H 11 H 1 Y 4 H 10 H 1 Y 3 H 3 H 9 H 1 Y 2 H 1 Y 5 H 8 Y Y 1 Y 3 Y 1 Y 3 Y 2 Y.

Definition cf480 := Config 20 24 36
  H 2 H 12 Y 9 H 2 H 11 Y 9 H 7 H 3 H 10 H 10 Y 9 Y 5 H 1 Y 1 Y Y 3 Y 1 Y 2 Y Y.

Definition cf481 := Config 35
  H 11 H 1 Y 10 H 1 Y 9 H 1 Y 5 H 1 H 1 H 1 H 1 Y 5 H 1 Y 1 Y Y 3 Y Y 3 Y Y.

Definition cf482 := Config 30
  H 10 H 1 Y 5 H 8 H 1 H 1 Y 3 H 9 Y 3 H 1 Y 3 H 1 Y 1 Y Y 2 H 1 Y 1 Y Y.

Definition cf483 := Config 32
  H 9 H 1 H 1 H 1 Y 3 H 11 Y 6 H 7 H 1 H 1 H 1 Y 2 Y 4 Y Y 5 Y 1 Y Y Y Y.

Definition cf484 := Config 23
  H 10 H 1 Y 8 H 9 H 1 Y 7 H 2 H 9 Y 8 Y 3 Y Y 3 H 5 H 1 H 1 Y 1 Y Y Y.

Definition cf485 := Config 30
  H 8 H 3 H 11 H 11 Y 9 H 9 H 1 Y 8 H 1 Y 8 Y 4 H 7 Y Y 1 Y 2 H 1 Y 1 Y Y.

Definition cf486 := Config 36
  H 11 H 2 H 13 Y 8 H 11 H 1 Y 10 H 1 Y 10 H 10 Y Y Y 6 H 1 H 1 Y 5 H 1 Y 1 Y 3 
  Y 1 Y 1 Y.

Definition cf487 := Config 36
  H 9 H 4 H 13 H 13 H 13 Y 11 H 1 Y 10 H 10 H 1 Y 10 H 1 Y 9 H 1 Y 1 Y 1 Y 6 Y Y
  3 Y 1 Y 1 Y.

Definition cf488 := Config 10 11 40
  H 10 H 3 H 13 H 13 Y 11 H 1 Y 10 H 1 Y 8 H 1 H 9 H 1 Y 9 H 1 Y 1 Y 1 Y 6 Y Y 3
  Y 1 Y 1 Y.

Definition cf489 := Config 8 31 35 37
  H 11 H 2 H 13 Y 11 H 1 Y 9 H 2 H 11 Y 8 H 1 H 9 H 1 Y 9 H 1 Y 1 Y 1 Y 6 Y 2 Y 
  2 Y 1 Y 1 Y.

Definition cf490 := Config 19
  H 2 H 13 Y 4 H 2 H 12 Y 4 H 10 H 1 Y 4 H 1 Y 8 H 1 H 1 Y 1 Y 2 H 7 Y 2 Y Y 3 Y
  1 Y Y.

Definition cf491 := Config 6
  H 2 H 11 Y 9 H 1 Y 8 H 1 Y 5 H 8 Y 4 H 2 H 7 Y H 1 Y 4 H 5 Y 3 H 4 Y Y 1 Y.

Definition cf492 := Config 34
  H 9 H 1 H 1 H 1 Y 3 H 11 Y 3 H 10 Y 3 H 9 Y 2 H 1 Y 2 H 1 Y 4 Y 1 Y 3 Y 1 Y Y.

Definition cf493 := Config 26 27 37
  H 10 H 3 H 13 H 13 Y 11 H 1 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 8 H 8 Y Y Y 4 Y 2 Y 3 Y
  Y.

Definition cf494 := Config 37
  H 2 H 13 Y 3 H 12 Y 3 H 11 Y 5 H 8 H 1 H 1 Y 3 H 9 Y 2 H 8 Y 2 Y 3 Y 1 Y 2 Y Y
  2 Y.

Definition cf495 := Config 37
  H 12 H 1 Y 11 H 1 Y 10 H 1 Y 9 H 1 Y 6 H 3 H 9 H 9 Y 8 H 8 Y 2 Y 3 Y Y 3 Y Y 2
  Y.

Definition cf496 := Config 35
  H 2 H 13 Y 3 H 12 Y 3 H 11 Y 3 H 10 Y 3 H 9 Y 2 H 1 H 1 H 1 Y 5 Y 1 Y 1 Y 2 Y 
  1 Y 1 Y.

Definition cf497 := Config 8
  H 11 H 1 H 1 Y 5 H 10 H 1 H 1 Y 4 H 10 H 1 Y 3 H 10 Y 2 Y 3 Y 1 Y 1 Y 3 Y 4 Y 
  2 Y 1 Y.

Definition cf498 := Config 29 34 36
  H 3 H 12 H 1 Y 3 H 12 Y 3 H 11 Y 3 H 10 Y 4 H 8 H 1 Y 2 H 1 Y 1 Y 6 Y 5 Y 3 Y 
  1 Y 2 Y.

Definition cf499 := Config 36
  H 11 H 1 H 1 Y 5 H 10 H 1 H 1 Y 3 H 11 Y 4 H 9 H 1 Y 2 Y 3 Y 1 Y 6 Y 3 Y 3 Y 3
  Y 1 Y.

Definition cf500 := Config 34 37
  H 12 H 1 Y 11 H 1 Y 9 H 2 H 11 Y 9 H 1 Y 8 H 9 H 9 Y 3 H 8 Y 3 Y Y Y 4 Y Y Y.

Definition cf501 := Config 33
  H 12 H 1 Y 11 H 1 Y 8 H 3 H 11 H 11 Y 8 H 2 H 10 Y 8 H 1 Y 7 Y Y Y 3 Y 1 Y 1 Y
  1 Y.

Definition cf502 := Config 34
  H 11 H 1 H 1 Y 3 H 12 Y 6 H 8 H 1 H 1 H 1 Y 3 H 10 Y 2 Y 3 Y 1 Y 1 Y 1 Y 2 Y 1
  Y 1 Y.

Definition cf503 := Config 34
  H 3 H 13 H 13 Y 11 H 1 Y 7 H 4 H 11 H 11 H 11 Y 9 H 1 Y 9 Y 7 Y Y Y Y 3 Y 1 Y 
  1 Y.

Definition cf504 := Config 35
  H 11 H 1 H 1 Y 3 H 12 Y 3 H 11 Y 3 H 3 H 9 H 1 Y 2 Y 3 Y 3 H 1 Y 5 Y 1 Y 1 Y 2
  Y 1 Y.

Definition cf505 := Config 8
  H 11 H 1 H 1 Y 4 H 11 H 1 Y 3 H 2 H 11 Y 3 H 10 Y 2 Y 3 Y 3 H 7 Y Y 1 Y 3 Y 3 
  Y 2 Y.

Definition cf506 := Config 36
  H 2 H 13 Y 4 H 11 H 1 Y 3 H 11 Y 5 H 8 H 1 H 1 Y 3 H 9 Y 3 Y 2 Y 4 Y Y 3 Y 3 Y
  Y.

Definition cf507 := Config 37
  H 11 H 1 H 1 Y 3 H 12 Y 3 H 11 Y 3 H 3 H 9 H 1 Y 2 Y 3 Y 3 H 7 Y 4 Y 1 Y Y Y
  Y.

Definition cf508 := Config 6
  H 10 H 1 Y 3 H 10 Y 3 H 9 Y 3 H 8 Y 3 H 1 Y 3 Y 3 H 2 H 5 Y H 1 Y 3 Y 1 Y.

Definition cf509 := Config 35
  H 12 H 1 Y 3 H 12 Y 4 H 10 H 1 Y 3 H 10 Y 4 H 1 Y 3 Y 4 H 1 H 1 Y 1 Y Y 3 Y 1 
  Y 1 Y.

Definition cf510 := Config 8 9 30 37
  H 12 H 1 Y 11 H 10 H 2 H 12 Y 10 H 1 Y 8 H 2 H 10 Y 9 Y 4 Y Y Y 3 H 1 Y 1 Y Y 
  Y.

Definition cf511 := Config 21 25 37
  H 2 H 13 Y 11 H 1 Y 10 H 1 Y 9 H 7 H 3 H 10 H 10 Y 9 Y 5 H 1 Y 1 Y Y 3 Y 1 Y 2
  Y Y.

Definition cf512 := Config 31
  H 10 H 2 H 12 Y 10 H 1 Y 9 H 9 H 1 Y 8 H 1 Y 8 Y 4 H 7 Y Y 1 Y 3 H 1 Y 3 Y 1
  Y.

Definition cf513 := Config 37 39
  H 2 H 13 Y 4 H 11 H 1 Y 3 H 11 Y 5 H 8 H 1 H 1 Y 3 H 1 Y 8 H 8 Y Y 1 Y 4 Y 4 Y
  1 Y 2 Y.

Definition cf514 := Config 36
  H 2 H 12 Y 5 H 9 H 1 H 1 Y 5 H 8 H 1 H 1 Y 3 H 9 Y 4 H 1 Y 7 Y 1 Y 4 Y Y 1 Y
  Y.

Definition cf515 := Config 34
  H 2 H 12 Y 3 H 11 Y 4 H 2 H 10 Y 3 H 9 Y 6 H 1 H 8 H 8 Y Y 1 Y 1 Y 4 H 4 Y Y 1
  Y.

Definition cf516 := Config 37
  H 12 H 1 Y 11 H 1 Y 10 H 8 H 3 H 11 H 11 Y 2 H 10 Y 8 H 1 H 1 Y 1 Y 1 Y 1 Y 4 
  H 1 Y 3 Y 1 Y 1 Y.

Definition cf517 := Config 37
  H 12 H 1 Y 11 H 1 Y 8 H 10 H 1 Y 2 H 1 H 10 H 10 Y 8 H 1 H 1 Y 1 Y 1 Y 1 Y 4 H
  1 Y 3 Y 1 Y 1 Y.

Definition cf518 := Config 25
  H 11 H 1 Y 9 H 10 H 1 Y 8 H 1 H 9 H 1 Y 2 H 9 Y Y Y 4 H 1 H 1 H 1 Y H 5 Y 4 Y 
  1 Y 1 Y.

Definition cf519 := Config 6
  H 12 H 1 Y 3 H 12 Y 7 H 7 H 1 H 1 H 1 H 1 Y 3 H 10 Y 2 Y 4 H 1 Y 7 Y 1 Y 3 Y 4
  Y 2 Y 1 Y.

Definition cf520 := Config 1 2 31
  H 2 H 12 Y 10 H 1 Y 7 H 3 H 10 H 10 Y 7 H 2 H 9 Y 8 Y 6 Y Y Y 3 Y 1 Y 1 Y.

Definition cf521 := Config 2 31
  H 2 H 12 Y 10 H 1 Y 7 H 3 H 10 H 10 Y 7 H 2 H 9 Y 8 Y 6 Y Y 2 Y 3 Y Y 1 Y.

Definition cf522 := Config 31
  H 2 H 12 Y 3 H 11 Y 3 H 10 Y 3 H 2 H 9 Y 3 H 8 Y 3 Y 3 H 6 Y Y 1 Y 2 Y 1 Y.

Definition cf523 := Config 34
  H 10 H 1 Y 8 H 2 H 10 Y 8 H 1 Y 7 H 1 Y 6 H 1 H 1 Y H 6 Y 2 Y Y 3 Y Y.

Definition cf524 := Config 3 36
  H 3 H 11 H 1 Y 3 H 11 Y 4 H 9 H 1 Y 4 H 8 H 1 Y 2 H 8 Y Y 2 Y 1 Y 2 Y 1 Y 2 Y.

Definition cf525 := Config 35
  H 2 H 12 Y 3 H 11 Y 3 H 2 H 10 Y 5 H 7 H 1 H 1 Y 7 Y 1 Y 6 H 6 Y 2 Y Y 3 Y Y.

Definition cf526 := Config 34
  H 11 H 1 Y 9 H 2 H 11 Y 9 H 1 Y 5 H 1 H 1 H 2 H 9 Y 6 Y 1 Y Y Y 4 Y Y Y.

Definition cf527 := Config 27
  H 2 H 12 Y 4 H 2 H 11 Y 5 H 8 H 1 H 1 Y 2 Y 6 Y 1 Y 1 Y 4 H 5 Y 2 H 4 Y Y 1 Y.

Definition cf528 := Config 31
  H 10 H 1 Y 3 H 10 Y 4 H 2 H 9 Y 2 H 1 Y 5 H 7 H 7 Y 1 H 1 Y 2 Y Y Y 2 Y.

Definition cf529 := Config* 35
  H 2 H 12 Y 5 H 9 H 1 H 1 Y 3 H 10 Y 5 H 9 H 9 H 9 Y 4 Y Y 1 Y 1 Y 1 Y 2 Y 1 Y.

Definition cf530 := Config 35
  H 11 H 1 Y 10 H 1 Y 8 H 2 H 10 Y 8 H 1 Y 7 H 1 Y 7 H 1 Y H 6 Y 2 Y Y 3 Y Y.

Definition cf531 := Config 34
  H 3 H 13 H 13 Y 11 H 1 Y 10 H 1 Y 8 H 9 H 1 Y 9 Y 7 Y 6 H 1 Y 6 H 1 Y 4 Y Y 1 
  Y 1 Y.

Definition cf532 := Config 37
  H 12 H 1 Y 10 H 2 H 12 Y 10 H 1 Y 9 H 1 Y 6 H 1 H 1 H 1 Y 6 Y 1 Y Y Y 4 Y Y Y.

Definition cf533 := Config 12 33 37
  H 2 H 13 Y 3 H 12 Y 4 H 10 H 1 Y 3 H 10 Y 2 H 1 H 1 H 1 Y 6 Y 1 Y 1 Y 3 Y Y 1 
  Y 1 Y.

Definition cf534 := Config 13 20 30
  H 4 H 13 H 13 H 13 Y 11 H 1 Y 10 H 1 Y 9 H 9 H 1 Y 9 Y 6 Y 1 Y 5 H 1 Y 4 Y Y 1
  Y 1 Y.

Definition cf535 := Config 7
  H 3 H 13 H 13 Y 9 H 3 H 12 H 12 Y 10 H 1 Y 8 H 2 H 10 Y 9 Y 7 Y Y Y 3 Y 1 Y 2 
  Y Y.

Definition cf536 := Config 35
  H 11 H 2 H 13 Y 10 H 2 H 12 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 8 H 8 Y Y Y Y 2 Y 2 Y 1
  Y.

Definition cf537 := Config 6
  H 2 H 12 Y 10 H 1 Y 8 H 2 H 10 Y 6 H 3 H 9 H 9 Y 8 Y 6 Y Y 3 Y 2 H 4 Y 2 Y Y.

Definition cf538 := Config 33
  H 2 H 12 Y 5 H 9 H 1 H 1 Y 3 H 10 Y 3 H 9 Y 3 H 8 Y 3 Y 1 Y 2 Y 3 H 4 Y Y 1 Y.

Definition cf539 := Config 6
  H 11 H 1 Y 3 H 11 Y 5 H 8 H 1 H 1 Y 3 H 9 Y 2 H 1 Y 3 Y 1 Y 2 Y 2 H 1 Y 3 Y 1 
  Y.

Definition cf540 := Config 35
  H 10 H 1 H 1 Y 3 H 11 Y 3 H 10 Y 5 H 7 H 1 H 1 Y 2 Y 3 Y 3 H 1 Y 4 Y 1 Y 1 Y 2
  Y.

Definition cf541 := Config 37
  H 12 H 1 Y 10 H 2 H 12 Y 10 H 1 Y 8 H 2 H 10 Y 7 H 2 H 9 Y 7 Y 4 Y Y Y 3 Y 1 Y
  Y.

Definition cf542 := Config 34
  H 3 H 12 H 1 Y 3 H 12 Y 4 H 10 H 1 Y 3 H 10 Y 4 H 9 H 9 Y 3 Y 2 Y Y 1 Y 1 Y 2 
  Y 1 Y.

Definition cf543 := Config 34
  H 12 H 1 Y 11 H 1 Y 10 H 10 H 1 Y 9 H 1 Y 7 H 1 H 1 Y 7 Y 6 H 1 Y 1 Y Y 3 Y Y 
  2 Y.

Definition cf544 := Config 34
  H 10 H 1 H 1 H 1 Y 3 H 12 Y 5 H 9 H 1 H 1 Y 3 H 10 Y 2 Y 4 Y Y 1 Y 1 Y 1 Y 2 Y
  1 Y.

Definition cf545 := Config 4 5 36
  H 4 H 10 H 1 H 1 Y 3 H 11 Y 3 H 10 Y 4 H 8 H 1 Y 2 Y 6 Y 1 Y 4 H 5 Y Y 1 Y 2
  Y.

Definition cf546 := Config 36
  H 5 H 13 H 13 H 13 H 13 Y 11 H 1 Y 7 H 4 H 11 H 11 H 11 Y 10 Y 6 Y 1 Y 1 Y 3 Y
  1 Y Y 1 Y 1 Y.

Definition cf547 := Config 34
  H 12 H 1 Y 11 H 11 H 1 Y 8 H 3 H 11 H 11 Y 8 H 2 H 10 Y 7 H 1 Y 7 Y 1 Y 1 Y 4 
  Y Y Y 2 Y.

Definition cf548 := Config 38
  H 2 H 13 Y 6 H 9 H 1 H 1 H 1 Y 3 H 11 Y 5 H 10 H 10 H 10 Y 4 Y Y 1 Y 1 Y 1 Y 2
  Y 1 Y 1 Y.

Definition cf549 := Config 33
  H 4 H 13 H 13 H 13 Y 11 H 1 Y 10 H 1 Y 7 H 3 H 10 H 10 Y 9 Y 6 Y 1 Y 3 Y Y 2 H
  1 Y 3 Y 1 Y.

Definition cf550 := Config 38
  H 2 H 13 Y 11 H 1 Y 10 H 1 Y 7 H 9 H 1 Y 9 Y 7 Y 7 H 7 H 7 H 2 H 7 Y 2 Y Y 3 Y
  1 Y 1 Y.

Definition cf551 := Config 6
  H 2 H 12 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 6 H 8 Y 6 Y 4 H 1 H 1 H 1 Y H 5 Y 4 Y 1 Y 
  1 Y.

Definition cf552 := Config 19 20 40
  H 2 H 13 Y 3 H 12 Y 4 H 10 H 1 Y 6 H 7 H 1 H 1 H 1 Y 2 Y 8 H 8 Y 7 Y 1 Y 1 Y 3
  Y Y 2 Y.

Definition cf553 := Config 36
  H 4 H 13 H 13 H 13 Y 11 H 1 Y 6 H 5 H 11 H 11 H 11 H 11 Y 10 Y 6 Y 1 Y 1 Y 6 H
  6 Y 5 Y Y 1 Y 1 Y.

Definition cf554 := Config 40
  H 12 H 1 Y 11 H 1 Y 10 H 1 Y 9 H 1 Y 5 H 1 H 3 H 9 H 9 Y 2 H 8 Y 7 H 1 Y 1 Y 2
  Y 3 Y Y 1 Y.

Definition cf555 := Config 37
  H 12 H 1 Y 9 H 3 H 12 H 12 Y 10 H 1 Y 9 H 1 Y 7 H 1 H 1 Y 7 Y 7 H 7 Y 2 Y Y 3 
  Y Y 2 Y.

Definition cf556 := Config 30
  H 10 H 1 Y 7 H 3 H 10 H 10 Y 8 H 1 Y 6 H 2 H 8 Y 6 Y Y Y 4 Y Y Y.

Definition cf557 := Config 10 31
  H 10 H 1 Y 8 H 9 H 1 Y 8 H 1 Y 7 H 1 Y 5 H 1 Y 6 H 1 Y 5 Y 1 Y 3 Y Y.

Definition cf558 := Config 27
  H 11 H 1 Y 8 H 3 H 11 H 11 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 6 Y Y Y 4 Y Y Y.

Definition cf559 := Config 32
  H 2 H 12 Y 10 H 1 Y 8 H 9 H 1 Y 8 H 1 Y 8 Y 5 H 1 Y 6 H 1 Y 4 Y 1 Y 1 Y 2 Y.

Definition cf560 := Config 23
  H 2 H 11 Y 9 H 1 Y 7 H 2 H 9 Y 7 H 1 Y 3 Y Y 3 H 1 H 1 Y H 4 Y Y 1 Y.

Definition cf561 := Config 29
  H 10 H 1 Y 8 H 2 H 10 Y 8 H 1 Y 5 H 3 H 8 H 8 Y 6 Y Y 2 H 1 Y 2 Y Y Y.

Definition cf562 := Config* 33
  H 2 H 13 Y 11 H 1 Y 10 H 1 Y 9 H 9 H 1 Y 8 H 1 Y 8 Y 6 Y 4 Y 2 H 1 Y 4 Y 1 Y 2
  Y.

Definition cf563 := Config 31
  H 2 H 13 Y 3 H 2 H 12 Y 3 H 11 Y 3 H 2 H 10 Y 2 Y 7 H 1 Y 6 Y 1 Y 1 Y 4 H 4 Y 
  Y 1 Y.

Definition cf564 := Config 8 9 34
  H 12 H 1 Y 11 H 1 Y 10 H 10 H 1 Y 9 H 1 Y 7 H 1 H 1 Y 7 Y 6 H 7 Y 3 Y Y Y 3 Y 
  Y.

Definition cf565 := Config 34
  H 2 H 12 Y 8 H 3 H 11 H 11 Y 9 H 1 Y 7 H 2 H 9 Y 8 Y 6 H 7 Y Y 1 Y 4 H 4 Y Y 1
  Y.

Definition cf566 := Config 17
  H 11 H 1 Y 9 H 2 H 11 Y 9 H 1 Y 8 H 1 Y 8 H 1 Y 6 H 1 H 1 Y H 6 Y 5 Y Y 1 Y 1 
  Y.

Definition cf567 := Config* 6
  H 2 H 9 Y 7 H 1 Y 7 H 7 H 7 H 7 H 7 Y 5 Y Y Y Y Y.

Definition cf568 := Config* 24
  H 8 H 2 H 10 Y 8 H 6 H 3 H 9 H 9 Y 8 H 8 Y Y Y Y Y Y Y.

Definition cf569 := Config* 23
  H 6 H 4 H 10 H 10 H 10 Y 7 H 9 H 9 H 9 Y Y Y Y Y 4 H 1 Y 3 Y 1 Y.

Definition cf570 := Config 27
  H 9 H 1 Y 3 H 9 Y 6 H 5 H 1 H 1 H 1 Y 2 Y 3 Y 1 Y 1 Y 1 Y 2 Y.

Definition cf571 := Config 27
  H 9 H 1 Y 3 H 9 Y 5 H 6 H 1 H 1 Y 2 H 1 Y 3 Y 1 Y 1 Y 3 Y Y.

Definition cf572 := Config 6
  H 2 H 10 Y 8 H 1 Y 4 H 8 Y 5 H 1 Y 6 H 1 Y 5 H 1 Y 4 H 1 Y 3 Y 1 Y.

Definition cf573 := Config 24
  H 7 H 4 H 11 H 11 H 11 Y 8 H 9 H 1 Y 9 H 9 Y Y Y Y Y 4 H 1 Y 3 Y 1 Y.

Definition cf574 := Config 33
  H 3 H 10 H 1 Y 7 H 10 H 2 H 10 Y 2 H 9 Y Y 6 H 1 H 1 Y 2 Y 1 Y 2 H 1 Y 1 Y Y.

Definition cf575 := Config 12 13 28
  H 2 H 11 Y 9 H 1 Y 6 H 3 H 9 H 9 Y 7 H 1 Y 7 Y 5 Y Y Y 2 Y 2 Y.

Definition cf576 := Config* 27
  H 10 H 1 Y 3 H 10 Y 3 H 9 Y 5 H 6 H 1 H 1 Y 2 Y 3 Y 1 Y 1 Y 1 Y 2 Y.

Definition cf577 := Config 6
  H 2 H 11 Y 9 H 1 Y 4 H 5 H 9 H 9 H 9 H 9 Y 8 Y 6 Y Y Y Y 3 Y 1 Y.

Definition cf578 := Config 6
  H 2 H 11 Y 9 H 1 Y 6 H 3 H 9 H 9 Y 7 H 8 Y 6 Y Y Y 4 H 4 Y 2 Y Y.

Definition cf579 := Config 30
  H 2 H 11 Y 4 H 9 H 1 Y 5 H 7 H 1 H 1 Y 3 H 8 Y 3 Y 1 Y 1 Y 1 Y 2 Y 1 Y.

Definition cf580 := Config 6
  H 2 H 11 Y 9 H 1 Y 7 H 2 H 9 Y 6 H 8 Y 6 Y Y 5 H 1 Y 4 H 1 Y 3 Y 1 Y.

Definition cf581 := Config* 31
  H 9 H 1 H 1 Y 4 H 9 H 1 Y 4 H 8 H 1 Y 2 H 1 Y 3 Y 1 Y 1 Y 1 Y 3 Y Y.

Definition cf582 := Config 6
  H 2 H 11 Y 9 H 1 Y 8 H 1 Y 5 H 8 Y 6 Y 6 H 1 Y 5 H 1 Y 4 H 1 Y 3 Y 1 Y.

Definition cf583 := Config 6
  H 2 H 10 Y 8 H 1 Y 4 H 8 Y 5 H 1 Y 6 H 1 Y 4 H 1 H 1 Y H 4 Y Y 1 Y.

Definition cf584 := Config 8 9 33
  H 2 H 12 Y 3 H 11 Y 4 H 9 H 1 Y 3 H 2 H 9 Y 2 Y 6 H 1 Y 6 Y 1 Y 2 Y 3 Y Y.

Definition cf585 := Config 30
  H 2 H 12 Y 10 H 1 Y 9 H 1 Y 5 H 4 H 9 H 9 H 9 Y 8 Y 6 Y Y Y Y 3 Y 1 Y.

Definition cf586 := Config 30
  H 3 H 12 H 12 Y 10 H 1 Y 7 H 3 H 10 H 10 Y 8 H 1 Y 8 Y 6 Y Y Y Y 2 Y 2 Y.

Definition cf587 := Config 27
  H 2 H 12 Y 10 H 1 Y 9 H 1 Y 7 H 2 H 9 Y 7 H 8 Y 6 Y Y Y 4 H 4 Y 2 Y Y.

Definition cf588 := Config 24
  H 2 H 12 Y 10 H 1 Y 9 H 1 Y 8 H 7 H 2 H 9 Y 8 Y 6 Y 6 H 6 Y 2 Y Y 2 Y 2 Y.

Definition cf589 := Config 16 17 31
  H 11 H 1 Y 3 H 11 Y 3 H 10 Y 3 H 9 Y 3 H 1 H 1 Y 3 Y 3 H 1 Y 4 Y 1 Y 1 Y 2 Y.

Definition cf590 := Config 7
  H 3 H 12 H 12 Y 7 H 4 H 11 H 11 H 11 Y 8 H 2 H 10 Y 9 Y 7 Y Y Y Y 3 Y 2 Y Y.

Definition cf591 := Config 6
  H 2 H 11 Y 9 H 1 Y 7 H 2 H 9 Y 8 H 8 H 8 H 8 Y 6 Y Y 4 H 5 Y 3 Y Y Y.

Definition cf592 := Config 6
  H 2 H 11 Y 9 H 1 Y 8 H 1 Y 5 H 8 Y 6 Y 6 H 1 Y 4 H 1 H 1 Y H 4 Y Y 1 Y.

Definition cf593 := Config 15
  H 11 H 1 Y 10 H 1 Y 8 H 2 H 10 Y 7 H 8 H 1 Y 7 Y 5 H 7 H 7 Y Y 1 Y 2 Y 2 Y Y.

Definition cf594 := Config 6
  H 2 H 12 Y 10 H 1 Y 9 H 1 Y 5 H 9 Y 3 H 1 H 1 H 1 Y 1 Y Y Y 4 H 4 Y 2 Y Y.

Definition cf595 := Config 41
  H 2 H 12 Y 3 H 2 H 11 Y 4 H 1 H 8 H 1 H 1 Y 3 H 9 H 9 Y 1 H 1 Y 1 Y Y 1 Y 1 Y 
  2 Y 1 Y.

Definition cf596 := Config 16 17 24
  H 2 H 12 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 6 H 8 Y 6 Y Y 4 H 1 H 1 Y H 4 Y Y 1 Y.

Definition cf597 := Config* 19 20 36
  H 2 H 13 Y 11 H 1 Y 10 H 1 Y 9 H 9 H 1 Y 8 H 9 Y 5 H 1 Y 1 Y Y 4 H 5 Y 3 Y Y Y.

Definition cf598 := Config 31
  H 2 H 11 Y 6 H 7 H 1 H 1 H 1 Y 3 H 9 Y 3 H 8 Y 3 Y 1 Y 1 Y 1 Y 2 Y 1 Y.

Definition cf599 := Config 30
  H 10 H 1 Y 3 H 10 Y 5 H 2 H 9 Y 2 Y 4 H 7 Y 2 H 6 Y 2 H 5 Y 2 Y Y 2 Y.

Definition cf600 := Config 31
  H 10 H 1 Y 3 H 10 Y 4 H 2 H 9 Y 2 H 1 Y 4 H 7 Y 2 H 6 Y 2 Y Y 3 Y Y.

Definition cf601 := Config 1 2 26 32
  H 2 H 12 Y 10 H 1 Y 6 H 4 H 10 H 10 H 10 Y 8 H 1 Y 8 Y 6 Y Y Y 2 Y 2 Y 1 Y.

Definition cf602 := Config 31
  H 11 H 1 Y 3 H 11 Y 5 H 8 H 1 H 1 Y 3 H 9 Y 2 H 1 Y 3 Y 1 Y 1 Y 4 Y 3 Y 1 Y.

Definition cf603 := Config 31
  H 2 H 12 Y 3 H 11 Y 5 H 8 H 1 H 1 Y 3 H 9 Y 3 H 8 Y 3 Y 1 Y 1 Y 1 Y 2 Y 1 Y.

Definition cf604 := Config 31
  H 11 H 1 Y 3 H 11 Y 3 H 10 Y 4 H 2 H 9 Y 2 Y 3 Y 2 H 6 Y 2 H 5 Y 2 Y Y 2 Y.

Definition cf605 := Config 6
  H 2 H 12 Y 10 H 1 Y 7 H 3 H 10 H 10 Y 7 H 9 Y 7 Y Y Y 4 H 5 Y 2 H 4 Y 2 Y Y.

Definition cf606 := Config 30
  H 2 H 11 Y 5 H 8 H 1 H 1 Y 3 H 9 Y 4 H 7 H 1 Y 3 Y 1 Y 1 Y 4 H 4 Y Y 1 Y.

Definition cf607 := Config 31
  H 11 H 1 Y 3 H 11 Y 4 H 2 H 10 Y 3 H 1 Y 4 H 8 Y 2 H 7 Y 2 Y Y 2 H 1 Y 1 Y Y.

Definition cf608 := Config 35
  H 2 H 12 Y 5 H 9 H 1 H 1 Y 3 H 2 H 10 Y 3 H 9 Y 3 Y 1 Y 3 H 6 Y Y 1 Y 2 Y 1 Y.

Definition cf609 := Config 27
  H 11 H 1 Y 3 H 11 Y 4 H 9 H 1 Y 3 H 9 Y 3 H 1 Y 3 Y 1 Y 4 H 1 Y H 4 Y Y 1 Y.

Definition cf610 := Config 29
  H 10 H 1 Y 3 H 10 Y 4 H 8 H 1 Y 2 H 1 H 1 H 1 Y 3 Y 1 Y 5 Y 3 H 1 Y 1 Y Y.

Definition cf611 := Config 23
  H 10 H 1 Y 3 H 10 Y 4 H 8 H 1 Y 3 H 8 Y 6 Y 1 Y 3 H 1 H 1 Y H 4 Y Y 1 Y.

Definition cf612 := Config 23
  H 11 H 1 Y 4 H 10 H 1 Y 3 H 10 Y 5 H 1 Y 4 Y Y 2 H 1 H 1 H 1 Y 1 Y Y Y Y.

Definition cf613 := Config 16 17 32
  H 12 H 1 Y 3 H 12 Y 3 H 11 Y 3 H 10 Y 3 H 2 H 9 Y 2 Y 3 Y 3 H 1 Y 4 Y 1 Y 1 Y 
  2 Y.

Definition cf614 := Config 11 12 33
  H 3 H 13 H 13 Y 10 H 2 H 12 Y 8 H 3 H 11 H 11 Y 9 H 1 Y 9 Y 7 Y Y Y Y 2 Y 2 Y 
  1 Y.

Definition cf615 := Config 12 13 30 36
  H 2 H 13 Y 11 H 1 Y 9 H 2 H 11 Y 8 H 2 H 10 Y 8 H 1 Y 5 Y Y 3 H 6 Y 3 Y Y Y 2 
  Y.

Definition cf616 := Config 30
  H 11 H 1 Y 3 H 11 Y 4 H 9 H 1 Y 3 H 9 Y 2 H 1 H 1 Y 3 Y 1 Y 5 Y 4 H 1 Y 3 Y 1 
  Y.

Definition cf617 := Config 30
  H 2 H 12 Y 3 H 11 Y 4 H 9 H 1 Y 3 H 9 Y 4 H 7 H 1 Y 3 Y 1 Y 1 Y 4 H 4 Y Y 1 Y.

Definition cf618 := Config 35
  H 2 H 13 Y 3 H 12 Y 5 H 9 H 1 H 1 Y 3 H 10 Y 4 H 9 H 9 Y 3 Y 1 Y 1 Y 1 Y 1 Y 2
  Y 1 Y.

Definition cf619 := Config 35
  H 12 H 1 Y 3 H 12 Y 4 H 10 H 1 Y 3 H 2 H 10 Y 2 H 1 Y 3 Y 3 H 7 Y Y 1 Y 4 Y 3 
  Y 1 Y.

Definition cf620 := Config* 31
  H 12 H 1 Y 3 H 12 Y 3 H 11 Y 3 H 10 Y 3 H 2 H 9 Y 2 Y 3 Y 2 H 6 Y 1 H 1 Y 1 Y 
  Y 2 Y.

Definition cf621 := Config 34
  H 2 H 13 Y 3 H 12 Y 5 H 9 H 1 H 1 Y 3 H 10 Y 4 H 8 H 1 Y 3 Y 1 Y 1 Y 1 Y 2 Y 1
  Y 1 Y.

Definition cf622 := Config* 6
  H 2 H 10 Y 8 H 1 Y 8 H 8 H 8 H 8 H 8 H 8 Y 6 Y Y Y Y Y Y.

Definition cf623 := Config 31
  H 10 H 1 Y 3 H 10 Y 7 H 5 H 1 H 1 H 1 H 1 Y 2 Y 3 Y 1 Y 1 Y 1 Y 1 Y 2 Y.

Definition cf624 := Config 31
  H 10 H 1 Y 3 H 10 Y 6 H 6 H 1 H 1 H 1 Y 2 H 1 Y 3 Y 1 Y 1 Y 1 Y 3 Y Y.

Definition cf625 := Config 12 13 32
  H 2 H 12 Y 10 H 1 Y 6 H 4 H 10 H 10 H 10 Y 8 H 1 Y 8 Y 6 Y Y Y Y 2 Y 2 Y.

Definition cf626 := Config 31
  H 11 H 1 Y 3 H 11 Y 4 H 9 H 1 Y 5 H 7 H 1 H 1 Y 2 Y 3 Y 1 Y 1 Y 1 Y 1 Y 2 Y.

Definition cf627 := Config* 30
  H 11 H 1 Y 3 H 11 Y 3 H 10 Y 6 H 6 H 1 H 1 H 1 Y 2 Y 3 Y 1 Y 1 Y 1 Y 1 Y 2 Y.

Definition cf628 := Config 6
  H 2 H 12 Y 10 H 1 Y 6 H 4 H 10 H 10 H 10 Y 8 H 9 Y 7 Y Y Y Y 4 H 4 Y 2 Y Y.

Definition cf629 := Config 35
  H 11 H 1 Y 3 H 11 Y 4 H 9 H 1 Y 3 H 1 H 1 H 1 Y 3 Y 1 Y 2 H 1 Y 5 Y 1 Y 3 Y Y.

Definition cf630 := Config 27
  H 2 H 13 Y 11 H 1 Y 9 H 2 H 11 Y 9 H 8 H 2 H 10 Y 9 Y 7 Y Y 6 H 6 Y 2 Y Y 2 Y 
  2 Y.

Definition cf631 := Config 31
  H 11 H 1 Y 3 H 11 Y 6 H 7 H 1 H 1 H 1 Y 3 H 9 Y 5 Y 1 Y 1 Y 1 Y 3 H 1 Y 3 Y 1 
  Y.

Definition cf632 := Config 35
  H 11 H 1 Y 3 H 11 Y 5 H 2 H 10 Y 2 H 1 Y 4 H 8 Y 2 H 7 Y 2 H 6 Y 2 Y Y 3 Y Y.

Definition cf633 := Config* 6
  H 2 H 11 Y 9 H 1 Y 9 H 9 H 9 H 9 H 9 H 9 H 9 Y 7 Y Y Y Y Y Y Y.

Definition the_configs := @seqn config 633
      cf001 cf002 cf003 cf004 cf005 cf006 cf007 cf008 cf009 cf010 cf011 cf012
      cf013 cf014 cf015 cf016 cf017 cf018 cf019 cf020 cf021 cf022 cf023 cf024
      cf025 cf026 cf027 cf028 cf029 cf030 cf031 cf032 cf033 cf034 cf035 cf036
      cf037 cf038 cf039 cf040 cf041 cf042 cf043 cf044 cf045 cf046 cf047 cf048
      cf049 cf050 cf051 cf052 cf053 cf054 cf055 cf056 cf057 cf058 cf059 cf060
      cf061 cf062 cf063 cf064 cf065 cf066 cf067 cf068 cf069 cf070 cf071 cf072
      cf073 cf074 cf075 cf076 cf077 cf078 cf079 cf080 cf081 cf082 cf083 cf084
      cf085 cf086 cf087 cf088 cf089 cf090 cf091 cf092 cf093 cf094 cf095 cf096
      cf097 cf098 cf099 cf100 cf101 cf102 cf103 cf104 cf105 cf106 cf107 cf108
      cf109 cf110 cf111 cf112 cf113 cf114 cf115 cf116 cf117 cf118 cf119 cf120
      cf121 cf122 cf123 cf124 cf125 cf126 cf127 cf128 cf129 cf130 cf131 cf132
      cf133 cf134 cf135 cf136 cf137 cf138 cf139 cf140 cf141 cf142 cf143 cf144
      cf145 cf146 cf147 cf148 cf149 cf150 cf151 cf152 cf153 cf154 cf155 cf156
      cf157 cf158 cf159 cf160 cf161 cf162 cf163 cf164 cf165 cf166 cf167 cf168
      cf169 cf170 cf171 cf172 cf173 cf174 cf175 cf176 cf177 cf178 cf179 cf180
      cf181 cf182 cf183 cf184 cf185 cf186 cf187 cf188 cf189 cf190 cf191 cf192
      cf193 cf194 cf195 cf196 cf197 cf198 cf199 cf200 cf201 cf202 cf203 cf204
      cf205 cf206 cf207 cf208 cf209 cf210 cf211 cf212 cf213 cf214 cf215 cf216
      cf217 cf218 cf219 cf220 cf221 cf222 cf223 cf224 cf225 cf226 cf227 cf228
      cf229 cf230 cf231 cf232 cf233 cf234 cf235 cf236 cf237 cf238 cf239 cf240
      cf241 cf242 cf243 cf244 cf245 cf246 cf247 cf248 cf249 cf250 cf251 cf252
      cf253 cf254 cf255 cf256 cf257 cf258 cf259 cf260 cf261 cf262 cf263 cf264
      cf265 cf266 cf267 cf268 cf269 cf270 cf271 cf272 cf273 cf274 cf275 cf276
      cf277 cf278 cf279 cf280 cf281 cf282 cf283 cf284 cf285 cf286 cf287 cf288
      cf289 cf290 cf291 cf292 cf293 cf294 cf295 cf296 cf297 cf298 cf299 cf300
      cf301 cf302 cf303 cf304 cf305 cf306 cf307 cf308 cf309 cf310 cf311 cf312
      cf313 cf314 cf315 cf316 cf317 cf318 cf319 cf320 cf321 cf322 cf323 cf324
      cf325 cf326 cf327 cf328 cf329 cf330 cf331 cf332 cf333 cf334 cf335 cf336
      cf337 cf338 cf339 cf340 cf341 cf342 cf343 cf344 cf345 cf346 cf347 cf348
      cf349 cf350 cf351 cf352 cf353 cf354 cf355 cf356 cf357 cf358 cf359 cf360
      cf361 cf362 cf363 cf364 cf365 cf366 cf367 cf368 cf369 cf370 cf371 cf372
      cf373 cf374 cf375 cf376 cf377 cf378 cf379 cf380 cf381 cf382 cf383 cf384
      cf385 cf386 cf387 cf388 cf389 cf390 cf391 cf392 cf393 cf394 cf395 cf396
      cf397 cf398 cf399 cf400 cf401 cf402 cf403 cf404 cf405 cf406 cf407 cf408
      cf409 cf410 cf411 cf412 cf413 cf414 cf415 cf416 cf417 cf418 cf419 cf420
      cf421 cf422 cf423 cf424 cf425 cf426 cf427 cf428 cf429 cf430 cf431 cf432
      cf433 cf434 cf435 cf436 cf437 cf438 cf439 cf440 cf441 cf442 cf443 cf444
      cf445 cf446 cf447 cf448 cf449 cf450 cf451 cf452 cf453 cf454 cf455 cf456
      cf457 cf458 cf459 cf460 cf461 cf462 cf463 cf464 cf465 cf466 cf467 cf468
      cf469 cf470 cf471 cf472 cf473 cf474 cf475 cf476 cf477 cf478 cf479 cf480
      cf481 cf482 cf483 cf484 cf485 cf486 cf487 cf488 cf489 cf490 cf491 cf492
      cf493 cf494 cf495 cf496 cf497 cf498 cf499 cf500 cf501 cf502 cf503 cf504
      cf505 cf506 cf507 cf508 cf509 cf510 cf511 cf512 cf513 cf514 cf515 cf516
      cf517 cf518 cf519 cf520 cf521 cf522 cf523 cf524 cf525 cf526 cf527 cf528
      cf529 cf530 cf531 cf532 cf533 cf534 cf535 cf536 cf537 cf538 cf539 cf540
      cf541 cf542 cf543 cf544 cf545 cf546 cf547 cf548 cf549 cf550 cf551 cf552
      cf553 cf554 cf555 cf556 cf557 cf558 cf559 cf560 cf561 cf562 cf563 cf564
      cf565 cf566 cf567 cf568 cf569 cf570 cf571 cf572 cf573 cf574 cf575 cf576
      cf577 cf578 cf579 cf580 cf581 cf582 cf583 cf584 cf585 cf586 cf587 cf588
      cf589 cf590 cf591 cf592 cf593 cf594 cf595 cf596 cf597 cf598 cf599 cf600
      cf601 cf602 cf603 cf604 cf605 cf606 cf607 cf608 cf609 cf610 cf611 cf612
      cf613 cf614 cf615 cf616 cf617 cf618 cf619 cf620 cf621 cf622 cf623 cf624
      cf625 cf626 cf627 cf628 cf629 cf630 cf631 cf632 cf633.
