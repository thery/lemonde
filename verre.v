Require Import Cring.
From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory.

Section Verre.

(* Comme Coq ne connait rien en géométrie on va poser des hypothèses          *)

(* Le corps des coordonnées                                                   *)
Variable R : rcfType.

(* Le nombre Pi                                                               *)

Variable Pi : R.

Hypothesis NZPi : Pi != 0.

(* La racine carrée                                                           *)

Definition sqrt (x : R) := Num.sqrt x.

(* La racine cubique                                                          *)

Variable sqrt3 : R -> R.
Hypothesis sqrt3E : forall x,  0 <= x -> (sqrt3 x) ^+ 3 = x.

(* Le rayon du verre                                                          *)

Variable r : R.

Hypothesis NZr : r != 0.

(* La hauteur du verre                                                        *)

Variable h : R.

Hypothesis NZh : h != 0.

(* Formule du volume pour un cylindre                                         *)

Definition lvol h1 := Pi * r ^+ 2 * h1.

(* Le coefficient pour un cône                                                *)

Definition ccoef := r / h.

(* Formule du volume pour un cône                                             *)

Definition cvol h1 := Pi/ 3%:R * ccoef ^+ 2 * h1 ^+ 3.

(* Rapport entre le volume d'un cylindre et d'un cone                         *)

Fact lcrap : cvol h / lvol h = 1 / 3%:R.
Proof.
rewrite /cvol /ccoef /lvol expr_div_n mulf_div -mulrA mulf_div.
have->: 3%:R * h ^+ 2 * (Pi * r ^+ 2 * h) = h ^+ 3 * r ^+ 2 * Pi * 3%:R.
  rewrite !exprS !mulr1 !mulrA mulrC -!mulrA; congr (_ * _).
  rewrite mulrC -!mulrA; congr (_ * (_ * _)); rewrite !mulrA; congr (_ * _).
  by rewrite -!mulrA mulrC !mulrA.
by rewrite !invfM !exprS !mulr1 !mulrA !mulfK ?divff.
Qed.

(* La hauteur pour avoir la moitié du volume                                   *)

Definition chalf := h / sqrt3 2%:R.

Fact chalfV : cvol chalf = cvol h / 2%:R.
Proof.
by rewrite /cvol !expr_div_n sqrt3E ?(mulrA, Num.Theory.ler_nat _ 0). 
Qed.

(* Le coefficient pour un paraboloïde                                          *)

Definition pcoef := h / r ^+ 2.

(* Formule du volume pour un paraboloïde                                       *)

Definition pvol h1 := Pi/ (2%:R * pcoef) * h1 ^+ 2.

(* Rapport entre le volume d'un cylindre et d'un paraboloïde                   *)

Fact lprap : pvol h / lvol h = 1 / 2%:R.
Proof.
rewrite /pvol /pcoef /lvol.
have->: Pi / (2%:R * (h / r ^+ 2)) = Pi * r ^+ 2 / (2%:R * h).
  rewrite -!mulrA; congr (_ * _); rewrite !invfM !invrK.
  by rewrite mulrA mulrC -!mulrA.
rewrite -mulrA mulf_div.
have->: 2%:R * h * (Pi * r ^+ 2 * h) = h ^+ 2 * r ^+ 2 * Pi * 2%:R.
  rewrite [X in _ = X]mulrC -!mulrA; congr (_ * (_ * _)).
  by rewrite mulrC !mulrA; congr (_ * _); rewrite mulrC mulrA.
by rewrite !invfM !exprS !mulr1 !mulrA !mulfK ?divff.
Qed.

(* La hauteur pour avoir la moitié du volume                                   *)

Definition phalf := h / sqrt 2%:R.

Fact phalfV : pvol phalf = pvol h / 2%:R.
Proof.
pose F := Num.Theory.sqr_sqrtr.
by rewrite /pvol /phalf !expr_div_n  ?(mulrA, F, Num.Theory.ler_nat _ 0). 
Qed.

End Verre.
