Require Import Cring.
From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory.

Section Terre.

(* Un corps quelconque                                                        *)
Variable R : fieldType.

(* Le nombre Pi                                                               *)

Variable Pi : R.

Hypothesis NZPi : Pi != 0.
Hypothesis NZP2 : 2%:R != 0 :> R.

Definition length (r : R) := 2%:R * Pi * r.

Definition delta := 1 / (2%:R * Pi).

Lemma delta_length r1 r2 k  : length r1 - length r2 = k -> r1 = r2 + k * delta.
Proof.
rewrite /length /delta => Hd.
have P2D0 : 2%:R * Pi != 0 by rewrite mulf_eq0 negb_or NZP2.
apply: (mulfI P2D0); rewrite mulrDr [k * _]mulrA mulr1.
by rewrite [X in _ = _ + X]mulrC divfK // addrC -Hd subrK.
Qed.

Fact result r1 r2 :  length r1 - length r2 = 6%:R -> r1 = r2 + 3%:R / Pi.
Proof.
have->: 6%:R = (3%:R * 2%:R) :> R by rewrite -natrM.
by move/delta_length->; rewrite !mulrA mulr1 invfM mulrA mulfK.
Qed.

End Terre.