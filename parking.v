From mathcomp Require Import all_ssreflect all_algebra.

Import GRing.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Parking.

(* Une grille est une fonction qui prend deux nombres et retourne un booléen  *)

Definition grid n := 'I_n -> 'I_n -> bool.

(* La somme sur une ligne                                                     *)

Definition sumL n (g : grid n) i := \sum_(j < n) g i j.

(* La somme sur une colonne                                                   *)

Definition sumC n (g : grid n) j := \sum_(i < n) g i j.

(* Deux petites propriétés pour pouvoir utiliser des arguments d'injectivité  *)

Lemma leq_sumL n (g : grid n) i : sumL g i < n.+1.
Proof.
have {2}<-: \sum_(i < n) 1 = n by rewrite -[X in _ = X]card_ord sum1_card.
by apply: leq_sum => k; case: (g _ _).
Qed.

Lemma leq_sumC n (g : grid n) j : sumC g j < n.+1.
Proof.
have {2}<-: \sum_(i < n) 1 = n by rewrite -[X in _ = X]card_ord sum1_card.
by apply: leq_sum => k; case: (g _ _).
Qed.

(* Dans une grille non vide, deux lignes ou deux colonnes, ou une ligne et une
   colonne ont la même somme                                                  *)

Lemma inl_inj {A B} : injective (@inl A B). Proof. by move=> ?? []. Qed.
Lemma inr_inj {A B} : injective (@inr A B). Proof. by move=> ?? []. Qed.

Lemma result n (g : grid n) : 0 < n ->
  exists i, exists j,
   [\/  (i != j) /\ (sumL g i = sumL g j),
        (i != j) /\ (sumC g i = sumC g j) | sumL g i = sumC g j].
Proof.
case: n g => [//|[|n]] g _.
  by exists ord0, ord0; apply: Or33; rewrite /sumL /sumC !big_ord1.
pose sLC i := match i with | inl i => Ordinal (leq_sumL g i)
                          | inr i => Ordinal (leq_sumC g i) end.
have [sC_inj|/injectivePn] := altP (injectiveP sLC).
  have := max_card (mem (codom sLC)); rewrite card_codom // card_sum !card_ord.
  by rewrite !addnS !addSn !ltnS -ltn_subRL subnn ltn0.
move=> [[i|i] [[j|j] //=]]; [| |move: i j => j i|];
rewrite ?(inj_eq inj_inl, inj_eq inj_inr) => neq_ij [];
by exists i, j; do ?[exact: Or31|exact: Or32|exact: Or33].
Qed.

End Parking.
