From mathcomp Require Import all_ssreflect all_algebra.

Import GRing.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Chapeau.

(* Les personnes                                                              *)

Definition person := 'I_3.
Definition albert : person := 0%R.
Definition  marie : person := 1%R.
Definition sophie : person := 2%:R%R.

(* Les couleurs                                                               *)

Definition colour := bool.
Definition white : colour := true.
Definition black : colour := false.

Lemma WNB (c : colour) : (c == white) = (c != black).
Proof. by case: c. Qed.

(* Une configuration associe à une personne une couleur de chapeau            *)

Definition config := person -> colour.

(* Un maximum de 2 chapeaux blancs                                            *)

Hypothesis max_white : forall (c : config), 
  (c albert == white) + (c marie == white) + (c sophie == white)  <= 2.

Lemma max_whileP (c : config) : 
  [|| c albert == black, c marie == black | c sophie == black].
Proof. by have := max_white c; rewrite !WNB; do 3 case: (_ == _). Qed.

(* Albert sait si il voit deux chapeaux blancs                                *)

Definition Aknows (c : config) := (c marie == white) && (c sophie == white).

(* Si albert sait, il a un chapeau noir                                       *)

Lemma AknowsB c : Aknows c -> c albert = black.
Proof.
rewrite /Aknows.
by have /or3P[/eqP//||] := max_whileP c; rewrite !WNB => -> //; rewrite andbC.
Qed.

(* Marie sait si elle voit que sophie a un chapeau blanc                      *)

Definition Mknows (c : config) := (c sophie == white).

(* Si albert ne sait pas et marie sait alors marie a un chapeau noir          *)

Lemma MknowsB c : ~ Aknows c -> Mknows c -> c marie = black.
Proof.
move/negP; rewrite negb_and; rewrite /Mknows.
by case: (boolP (c sophie == _)) => // _; rewrite orbF WNB negbK => /eqP.
Qed.

(* Si ni albert ni marie ne savent, alors sophie a un chapeau noir            *)

Fact result c : ~ Aknows c -> ~ Mknows c -> c sophie = black.
Proof.
move/negP; rewrite negb_and => /orP[SB|]; last by rewrite WNB negbK => /eqP.
by move/negP; rewrite /Mknows WNB negbK=> /eqP.
Qed.

End Chapeau.
