From mathcomp Require Import all_ssreflect all_algebra all_fingroup.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Grid.

(******************************************************************************)
(*                                                                            *)
(*                           MODELISATION                                     *)
(*                                                                            *)
(******************************************************************************)

(* Une grille c'est 9 entiers                                                 *)
(*     0 1 2                                                                  *)
(*     3 4 5                                                                  *)
(*     6 7 8                                                                  *)

Definition grid := (nat * nat * nat * nat * nat * nat * nat * nat * nat)%type.

(* Les index pour les cases                                                   *)

Definition index := 'I_9.

(* Grille initiale                                                            *)

Definition grid0 : grid := (0, 0, 0, 0, 0, 0, 0, 0, 0).

(* Retourne la valeur d'une case                                              *)

Definition get (g : grid)  (i : index) : nat :=
  let: (a0, a1, a2, a3, a4, a5, a6, a7, a8) := g in
  if i == 0 :> nat then a0 else
  if i == 1 :> nat then a1 else
  if i == 2 :> nat then a2 else
  if i == 3 :> nat then a3 else
  if i == 4 :> nat then a4 else
  if i == 5 :> nat then a5 else
  if i == 6 :> nat then a6 else
  if i == 7 :> nat then a7 else a8.

(* Calcule la somme des éléments voisins pour un index donné                  *)

Definition sum (g : grid)  (i : index) : nat :=
  let: (a0, a1, a2, a3, a4, a5, a6, a7, a8) := g in
  if i == 0 :> nat then a1 + a3 + a4 else
  if i == 1 :> nat then a0 + a2 + a3 + a4 + a5 else
  if i == 2 :> nat then a1 + a4 + a5 else
  if i == 3 :> nat then a0 + a1 + a4 + a6 + a7 else
  if i == 4 :> nat then a0 + a1 + a2 + a3 + a5 + a6 + a7 + a8 else
  if i == 5 :> nat then a1 + a2 + a4 + a7 + a8 else
  if i == 6 :> nat then a3 + a4 + a7 else
  if i == 7 :> nat then a3 + a4 + a5 + a6 + a8
                   else a4 + a5 + a7.

(* Fonction de mise à jour générique, la fonction f donne la valeur à mettre  *)

Definition update (g : grid) f (i : index) :=
let: (a1, a2, a3, a4, a5, a6, a7, a8, a9) := g in
let b := f g i in 
   if i == 0 :> nat then ( b, a2, a3, a4, a5, a6, a7, a8, a9) else
   if i == 1 :> nat then (a1,  b, a3, a4, a5, a6, a7, a8, a9) else
   if i == 2 :> nat then (a1, a2,  b, a4, a5, a6, a7, a8, a9) else
   if i == 3 :> nat then (a1, a2, a3,  b, a5, a6, a7, a8, a9) else
   if i == 4 :> nat then (a1, a2, a3, a4,  b, a6, a7, a8, a9) else
   if i == 5 :> nat then (a1, a2, a3, a4, a5,  b, a7, a8, a9) else
   if i == 6 :> nat then (a1, a2, a3, a4, a5, a6,  b, a8, a9) else
   if i == 7 :> nat then (a1, a2, a3, a4, a5, a6, a7,  b, a9)
                    else (a1, a2, a3, a4, a5, a6, a7, a8,  b).

(* Ajouter un 1 en position i                                                 *)

Definition o_update g i := update g (fun g i => 1) i.

(* Ajouter la somme des voisins en position i                                 *)

Definition s_update g i := update g sum i.

(* Un parcours dans la grille c'est une permutation de toutes les cases       *)

Definition walk := 'S_9.

(* Calcule la grille pour le parcours w                                       *)

Definition w_update g (w : index -> index) :=
 (* on ajoute tous d'abord deux 1                                             *)
 (let g0 := o_update g  (w 0%:R) in
  let g1 := o_update g0 (w 1%:R) in
 (* et ensuite des sommes                                                     *)
  let g2 := s_update g1 (w 2%:R) in
  let g3 := s_update g2 (w 3%:R) in
  let g4 := s_update g3 (w 4%:R) in
  let g5 := s_update g4 (w 5%:R) in
  let g6 := s_update g5 (w 6%:R) in
  let g7 := s_update g6 (w 7%:R) in
  let g8 := s_update g7 (w 8%:R) in
  g8)%R.

Definition w_val w :=
  let g1 := w_update grid0 w in get g1 (w 8%:R)%R.

(* Ce que l'on veut prouver \max_(w : path) (w_val w) = 53, on fait cela par  *)
(* du calcul prouvé                                                           *)

Check \max_(w : walk) (w_val w).

(******************************************************************************)
(*                                                                            *)
(*                           CALCUL                                           *)
(*                                                                            *)
(******************************************************************************)

(* Toutes les façons d'insérer un élements dans une liste                     *)

Fixpoint insertl A (i : A) (l : seq A) : seq (seq A) :=
  (i :: l) ::
    if l is a :: l' then [seq a :: l | l <- insertl i l']
   else [::].

(* Calcul le max de f sur toutes les permutations.                            *)

Fixpoint get_max (n m : nat) (max : nat) f (l : seq 'I_m.+2)  :=
  if n is n1.+1 then
  let ls := insertl (n1%:R)%R l in
  foldr (fun l max => get_max n1 max f l) max ls
  else maxn max (f l).

Definition f_of_l n (l : seq 'I_n) (i : 'I_n) := nth i l i.

(* Calcul du maximum                                                          *)

Definition all_max :=
  get_max 9 0 (fun l => w_val (f_of_l l)) [::].

Lemma all_max_57 : all_max = 57.
Proof. Time by vm_compute. Qed.

(******************************************************************************)
(*                                                                            *)
(*                           PREUVE                                           *)
(*                                                                            *)
(******************************************************************************)

Lemma mem_insertl (A : eqType) (i : A) (l l1 : seq A) :
  l1 \in insertl i l -> l1 =i i :: l.
Proof.
elim: l l1 => //= [|a l IH] l1; rewrite in_cons => /orP[/eqP->|] //.
case/mapP=> l2 /IH l2Iil -> i1.
rewrite !in_cons; case: (i1 == _); first by rewrite orbT.
by rewrite l2Iil !orFb.
Qed.

Lemma size_insertl (A : eqType) (i : A) (l l1 : seq A) :
  l1 \in insertl i l -> size l1 = (size l).+1.
Proof.
elim: l l1 => //= [|a l IH] l1; rewrite in_cons => /orP[/eqP->|] //.
by case/mapP=> l2 /IH <- ->.
Qed.

(* Une liste ordonnée par rapport à une permutation                           *)

Definition ordLS (n : nat) (p : 'S_n) l := 
  sorted (fun x y => p^-1%g x < p^-1%g y) l.

Lemma ordLSE n p a b (l : seq 'I_n) : 
  ordLS p [:: a, b & l] = (p^-1 a < p^-1 b)%g && ordLS p [:: b & l].
Proof. by []. Qed.

Lemma ordLS_in n p a b (l : seq 'I_n) : 
  ordLS p (a :: l) -> b \in l -> p^-1%g a < p^-1%g b.
Proof.
move=> oC bIl.
have /subseq_path/(_ oC) : subseq [:: b] l by rewrite sub1seq.
by rewrite /= andbT => -> // x y z; apply: ltn_trans.
Qed.

Lemma ordLS_nth n p (l : seq 'I_n.+1) i j :
  ordLS p l -> i < j < size l -> p^-1%g (nth ord0 l i) < p^-1%g (nth ord0 l j).
Proof.
elim: l i j => // [i [|j]| a l IH [|i] [|j] Ol iLj] //; try by rewrite andbC.
  by apply: (ordLS_in Ol); apply: mem_nth; case/andP: iLj.
by apply: IH => //; case: (l) Ol => // a1 l1 /andP[].
Qed.

Lemma ordLS_nth_ge n p (l : seq 'I_n.+1) i :
  ordLS p l -> i < size l -> i <= p^-1%g (nth ord0 l i).
Proof.
move=> Ol; elim: i => // i IH iLs.
have /(ordLS_nth Ol) : i < i.+1 < size l by rewrite leqnn.
by apply/leq_trans/IH/(leq_trans _ iLs).
Qed.

Lemma ordLS_nth_le n p (l : seq 'I_n.+1) i :
  ordLS p l -> i < size l -> p^-1%g (nth ord0 l i) <= n - (size l - i.+1).
Proof.
case: l => // a l Ol.
rewrite [size _]/= ltnS subSS => /subKn -{1}<-.
elim: (_ - i) (leq_subr i (size l)) => [_|i1 IH i1Ls].
  by rewrite !subn0 -ltnS ltn_ord.
rewrite -ltnS.
have /(leq_trans _)-> // :  n -i1 <= (n - i1.+1).+1.
  case: (ltnP i1 n)=> [HH|]; first by rewrite -subSn //.
  by rewrite -subn_eq0 => /eqP->.
apply: leq_trans (IH (ltnW i1Ls)).
apply: ordLS_nth => //; rewrite ltn_sub2l //.
by apply: (leq_trans (leq_subr _ _)).
Qed.

Lemma ordLS_enum n p (l : seq 'I_n.+1) :
  ordLS p l -> (size l == n.+1) = (l == [seq p i | i <- enum 'I_n.+1]).
Proof.
move=> Ol; apply/eqP/eqP=> [sE|->]; last by rewrite size_map size_enum_ord.
apply: (@eq_from_nth _ ord0) => [|i iLs].
   by rewrite size_map size_enum_ord.
rewrite (nth_map ord0) ?size_enum_ord -1?sE //.
apply: (@perm_inj _ p^-1%g); rewrite permK.
apply/val_eqP => /=.
rewrite eqn_leq !nth_enum_ord -1?sE // ordLS_nth_ge //.
have {2}->: i = n - (size l - i.+1).
  by rewrite sE subSS subKn // -ltnS -sE.
by rewrite ordLS_nth_le.
Qed.

Lemma insertl_ordLS n (p : 'S_n.+2) i (l : seq 'I_n.+2) :
  i \notin l -> ordLS p l -> exists l1, (l1 \in insertl i l) && ordLS p l1.
Proof.
elim: l i => [i _ _|a l IH i iNal Oal] //.
- by exists [:: i]; rewrite mem_head.
have Ol : ordLS p l.
  by case: (l) Oal => //= b l1; rewrite /ordLS /= => /andP[].
have oNl : i \notin l.
  by apply: contra iNal; rewrite in_cons orbC => ->.
case: (ltnP (p^-1%g i) (p^-1%g a)) => [iLa|].
  by exists [:: i, a & l]; rewrite mem_head /ordLS /= iLa.
rewrite leq_eqVlt=> /orP[|aLi].
  by move/val_eqP/perm_inj=> aLi; move: iNal; rewrite aLi in_cons eqxx.
have [l1 /andP[l1I ppl1]] := IH _ oNl Ol.
exists (a :: l1).
rewrite in_cons mem_map ?l1I ?orbT; last by move=> i1 j1 [].
case: (l1) ppl1 (mem_insertl l1I) => // a1 l2.
rewrite ordLSE => -> a1l2Iil; rewrite andbT andTb.
case: (boolP (a1 == i)) => [/eqP-> //|a1Di].
have := a1l2Iil i; rewrite !in_cons eqxx => /= /idP /orP[/eqP<- //|iIL2].
apply: ordLS_in Oal _.
by have := a1l2Iil a1; rewrite !in_cons eqxx (negPf a1Di) /= => <-.
Qed.

Lemma w_val_eq (f1 f2 : index -> index) : f1 =1 f2 -> w_val f1 = w_val f2.
Proof.
move=> f1Ef2.
congr (get _ _); last by rewrite f1Ef2.
by rewrite /w_update !f1Ef2.
Qed.

Lemma leq_get_max m k v f (l : seq 'I_m.+2) : v <= get_max k v f l.
Proof.
elim: k v l => /= [|k IH] v l; first by apply: leq_maxl.
by elim: insertl => //= a l1 IH1; apply: leq_trans (IH _ _).
Qed.

(* On peut enfin prouver le résultat voulu                                    *)

Lemma result : \max_(w : walk) (w_val w) = 57.
Proof.
apply/eqP; rewrite eqn_leq; apply/andP; split; last first.
  pose l : seq 'I_9 := ([::0%:R;2%:R;1%:R;3%:R;4%:R;6%:R;7%:R;5%:R;8%:R])%R.
  have Il :  injectiveb [ffun i => f_of_l l i].
    apply: perm_proof => [].
    by (do 10 try case => //) => i; (do 10 try case => //) => j;
    rewrite /f_of_l //= => /val_eqP /= HH; apply/val_eqP.
  have<-: w_val (f_of_l l) = 57 by vm_compute.
  have/w_val_eq<- : Perm Il =1 f_of_l l.
    by move=> x; rewrite [@fun_of_perm]unlock /= ffunE.
  by exact: (@leq_bigmax _ (fun p : 'S_9 => w_val p) (Perm Il)).
apply/bigmax_leqP=> /= p _; rewrite -all_max_57 /all_max.
have: (forall i : 'I_9 , i \in [::] -> 9 <= i) by [].
have: ordLS p [::] by [].
have: size ([::] : seq 'I_9) + 9 = 9 by [].
suff F n l m : 
  size l + n = 9 -> ordLS p l -> (forall i : 'I_9, i \in l -> n <= i) ->
  w_val p <= get_max n m (fun l0 : seq 'I_9 => w_val (f_of_l l0)) l.
    by apply: F.
elim: n l m => /= [|k IH] l v Es Ol Ltk.
  move/eqP: Es; rewrite addn0 (ordLS_enum Ol) => /eqP->.
  set f := f_of_l _; suff /w_val_eq-> : f =1 p by apply: leq_maxr.
  by move=> i; rewrite /f /f_of_l (nth_map ord0) ?size_enum_ord // nth_ord_enum.
have kE : (k%:R : 'I_9)%R = k :> nat.
  have kL9 : k < 9 by rewrite -Es addnS ltnS leq_addl.
  by rewrite (natr_Zp (Ordinal kL9)).
have kNIl : (k%:R)%R \notin l by apply/negP => /Ltk; rewrite kE ltnn.
have [l1 /andP[l1Ii Ol1]] := insertl_ordLS kNIl Ol.
have HH  : forall v,  w_val p <= get_max k v (fun l => w_val (f_of_l l)) l1.
  move=> v1; apply: IH => //.
    by rewrite (size_insertl l1Ii) -[X in _ = X]Es addnS.
  move=> i; rewrite (mem_insertl l1Ii) in_cons => /orP[/eqP->|] //.
    by rewrite kE.
  by move=> iIl; apply/ltnW/Ltk.
elim: insertl l1Ii => //= a1 l2 IH1.
rewrite in_cons => /orP[/eqP<-|l1Il2] /=; first by apply: HH.
by apply: leq_trans (IH1 _) (leq_get_max _ _ _ _).
Qed.

End Grid.
