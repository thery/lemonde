From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Définition d'un palindrome comme un type                                   *)

Section Def.

Variables (n : nat).

(* Un palindrome est un sous-type de n.-tuple                                 *)

(* Predicat qui définit la propriété d'être un palindrome                     *)

Definition is_pal (pval : n.-tuple 'I_10) :=
  ((n == 1) || (nth ord0 pval 0 != ord0)) && (rev pval == pval).

(* Le sous-type                                                               *)

Inductive  pal_type : predArgType := 
   Pal (pval : n.-tuple 'I_10) & is_pal pval.

Coercion pval p := let: Pal f _ := p in f.

(* Les structures canoniques associées                                        *)

Canonical pal_subType := Eval hnf in [subType for pval].
Definition pal_eqMixin := Eval hnf in [eqMixin of pal_type by <:].
Canonical pal_eqType := Eval hnf in EqType pal_type pal_eqMixin.
Definition pal_choiceMixin := [choiceMixin of pal_type by <:].
Canonical pal_choiceType := Eval hnf in ChoiceType pal_type pal_choiceMixin.
Definition pal_countMixin := [countMixin of pal_type by <:].
Canonical pal_countType := Eval hnf in CountType pal_type pal_countMixin.
Canonical pal_subCountType := Eval hnf in [subCountType of pal_type].
Definition pal_finMixin := [finMixin of pal_type by <:].
Canonical pal_finType := Eval hnf in FinType pal_type pal_finMixin.
Canonical pal_for_subFinType := Eval hnf in [subFinType of pal_type].

End Def.

(* Une notation pour le type                                                  *)

Notation "n .-palindrome" := (pal_type n)
  (at level 2, format "n .-palindrome") : type_scope.

(* Une notation pour les palindromes explicites                               *)

Notation "[ 'palindrome' x1 ; .. ; xn ]" := 
  (@Pal _ [tuple of (inZp x1) :: .. [:: (inZp xn)] ..] is_true_true)
  (at level 0, format "[ 'palindrome' '['  x1 ; '/'  .. ; '/'  xn ']' ]")
  : form_scope.

(* Un exemple                                                                 *)

Check [palindrome 1; 2; 3; 3; 2; 1].

(* Ceci échoue                                                                *)
(* Check [palindrome 1; 4; 3; 3; 2; 1].                                       *)

(* Ceci échoue                                                                *)
(* Check [palindrome 0; 2; 3; 3; 2; 0].                                       *)

(******************************************************************************)
(* On s'intéresse tout d'abord  à la cardinalité                              *)
(******************************************************************************)

Lemma card_p0 : #|{:0.-palindrome}| = 0.
Proof. by apply: eq_card0=> [[[[]]]]. Qed.

Lemma card_p1 : #|{:1.-palindrome}| = 10.
Proof. 
have P (x : 'I_10) : is_pal [tuple of [:: x]] by apply/andP.
rewrite -[X in _ = X]card_ord.
have /card_codom<- : injective (fun x => Pal (P x)) by move=> x y [].
apply: eq_card=> [[[[|u []]]]] // i i0; rewrite !inE codomE.
apply/sym_eq/idP/mapP; exists u; first by rewrite mem_enum.
by apply/val_eqP.
Qed.

(******************************************************************************)
(* Construction d'un palindrome à 2 * (n + 1) éléments à partir d'un élément  *)
(* de 0 .. 8 et d'un n.tuple de chiffres                                      *)
(******************************************************************************)

Definition mk_2n1 n (h : 'I_9) (t : n.-tuple 'I_10) :=
   let x := lift ord0 h in [tuple of (x :: t) ++ rev (x :: t)].

(* On construit bien un palindrome                                            *)

Lemma Pmk_2n1 n h (t : n.-tuple _) : is_pal (mk_2n1 h t).
Proof.
by rewrite /is_pal orbT /= rev_cons rev_cat revK rcons_cat rev_cons.
Qed.

(* C'est une fonction injective                                               *)

Lemma mk_2n1_inj n : injective (fun x => Pal (@Pmk_2n1 n x.1 x.2)).
Proof.
move=> [x1 x2] [y1 y2] [/ord_inj <-] /eqP.
by rewrite eqseq_cat ?size_tuple // => /andP[/val_eqP->] /=.
Qed.

(* C'est une fonction surjective                                              *)

Lemma mk_2n1E n (p : (n.+1 + n.+1).-palindrome) : {x | mk_2n1 x.1 x.2 = p}.
Proof.
pose u := thead p; pose t := behead p.
have/unlift_some[u' Hu' Hlu']: ord0 != u.
  rewrite /u; case: (p) => [[[] //= a p' i /andP[/=]]].
  by rewrite {1}addnS orFb eq_sym.
pose l := mktuple (fun i : 'I_n => nth ord0 t i).
exists (u' , l) => /=.
rewrite /mk_2n1 -Hu'.
have Hr : rev p = p by apply/eqP; case: (p) => u1 /= /andP[].
apply: eq_from_tnth=> i; rewrite !(tnth_nth ord0).
have F (j : 'I_ n.+1) : nth ord0 p j = nth ord0 (u :: l) j.
  case: (splitP (j : 'I_(1 + n)))=> [[[] //= _ ->]|k ->].
    by rewrite /u; case: (p)=> [[[|]]].
  rewrite [X in _ = X]/=.
  have kLn : k < n by rewrite -ltnS [_ < _]ltn_ord.
  by rewrite (nth_map k) ?size_enum_ord // nth_enum_ord // nth_behead.
have Hs : size (u :: l) = n.+1 by rewrite /= size_map size_enum_ord.
case: (splitP i)=> j Hj.
  by rewrite Hj F [X in X = _]/= -cat_cons nth_cat Hs ltn_ord.
rewrite nth_cat Hs {1}Hj ltnNge leq_addr /=.
rewrite Hj addKn nth_rev ?Hs // -Hr nth_rev size_tuple ?ltn_add2l //.
rewrite -[(_ + j).+1]addnS subnDl.
apply/sym_equal/(F (Ordinal (_ : _ - _ < _))).
by rewrite subSS (leq_ltn_trans (leq_subr _ _)).
Qed.

(* On en déduit la cardinalité pour les pairs non nuls                        *)

Lemma card_p2n1 n : #|{:n.+1.*2.-palindrome}| = 9 * 10 ^ n.
Proof.
rewrite -addnn -[10]card_ord -{1}[9]card_ord -card_tuple -card_prod /=.
rewrite -(card_codom (@mk_2n1_inj n)).
apply: eq_card=> p.
rewrite !inE codomE /=.
apply/sym_eq/idP/mapP.
by case: (mk_2n1E p) => x Hx; exists x; [rewrite mem_enum | apply/val_eqP/eqP].
Qed.


(******************************************************************************)
(* Construction d'un palindrome à 2 * (n + 1) + 1 éléments à partir d'un      *)
(* chiffre de 0 .. 8 d'un n tuple et d'un chiffre                             *)
(******************************************************************************)

Definition mk_1n2 n (h : 'I_9) (m : n.-tuple 'I_10) (t : 'I_ 10) := 
   let x := lift ord0 h in [tuple of (x :: m) ++ t :: rev (x :: m)].

(* On construit bien un palindrome                                            *)

Lemma Pmk_1n2 n h (m : n.-tuple _) t : is_pal (mk_1n2 h m t).
Proof.
rewrite /is_pal orbT /= !(rev_cons, rev_cat, rev_rcons, revK).
by rewrite rcons_cat rcons_cons /= cat_rcons.
Qed.

(* C'est une fonction injective                                               *)

Lemma mk_1n2_inj n : injective (fun x => Pal (@Pmk_1n2 n x.1.1 x.1.2 x.2)).
Proof.
move=> [[h1 m1] t1] [[h2 m2] t2] [/ord_inj<- /eqP].
rewrite eqseq_cat ?size_tuple // => /andP[/eqP Hm /eqP[<- _]].
by congr (_,_,_); apply/val_eqP/eqP.
Qed.

(* C'est une fonction surjective                                              *)

Lemma mk_1n2E n (p : (n.+1 + n.+2).-palindrome) :
  {x | mk_1n2 x.1.1 x.1.2 x.2 = p}.
Proof.
pose h := thead p; pose s := behead p.
have/unlift_some[h' Hh' Hlh']: ord0 != h.
  rewrite /h; case: (p) => [[[] //= a p' i /andP[/=]]].
  by rewrite {1}addnS orFb eq_sym.
pose m := mktuple (fun i : 'I_n => nth ord0 s i).
pose t := nth ord0 p n.+1.
exists (h', m, t) => /=.
rewrite /mk_1n2 -Hh'.
have Hr : rev p = p by apply/eqP; case: (p) => u1 /= /andP[].
apply: eq_from_tnth=> i; rewrite !(tnth_nth ord0).
have F (j : 'I_ n.+1) : nth ord0 p j = nth ord0 (h :: m) j.
  case: (splitP (j : 'I_(1 + n)))=> [[[] //= _ ->]|k ->].
    by rewrite /h; case: (p)=> [[[|]]].
  rewrite [X in _ = X]/=.
  have kLn : k < n by rewrite -ltnS [_ < _]ltn_ord.
  by rewrite (nth_map k) ?size_enum_ord // nth_enum_ord // nth_behead.
have Hs : size (h :: m) = n.+1 by rewrite /= size_map size_enum_ord.
case: (splitP i)=> j Hj.
  by rewrite Hj F [X in X = _]/= -cat_cons nth_cat Hs ltn_ord.
rewrite nth_cat Hs {1}Hj ltnNge leq_addr /=.
rewrite Hj addKn -Hr nth_rev size_tuple; last by rewrite -Hj.
rewrite {3}addnS subSS subnDl.
case: (splitP (j : 'I_(1 + n.+1)))=> [[[] //= _ ->]|k ->].
  by rewrite subn0.
rewrite /= nth_rev /= size_map size_enum_ord //.
set v := _ - _; suff vLn : v < n.+1 by rewrite (F (Ordinal vLn)).
by rewrite /v subSS sub_ord_proof.
Qed.

(* On en déduit la cardinalité pour les impairs à plus d'un chiffre           *)

Lemma card_p1n2 n : #|{:n.+1.*2.+1.-palindrome}| = 9 * 10 ^ n.+1.
Proof.
have->: n.+1.*2.+1 = n.+1 + n.+2 by rewrite addnS addnn.
rewrite expnS [10 * _]mulnC mulnA .
rewrite -{1}[9]card_ord -[10]card_ord -card_tuple -!card_prod /=.
rewrite -(card_codom (@mk_1n2_inj n)).
apply: eq_card=> p.
rewrite !inE codomE /=.
apply/sym_eq/idP/mapP.
by case: (mk_1n2E p) => x Hx; exists x; [rewrite mem_enum | apply/val_eqP/eqP].
Qed.

(* La solution du problème                                                    *)

Fact card_p351 : #|{:351.-palindrome}| = 9 * 10 ^ 175.
Proof. exact: (card_p1n2 174). Qed.

(******************************************************************************)
(* On définit la traduction d'un palindrome vers une valeur entière           *)
(******************************************************************************)

Section Number.

Variable b : nat.
Let number := seq 'I_b.

Fixpoint num2nat (n : number) :=
   if n is i :: n' then i + b * num2nat n' else 0.

Local Notation "`[ n ]" := (num2nat n).

Lemma num2nat_rcons i n : 
  `[rcons n i] = num2nat n + b ^ size n * i.
Proof.
elim: n => /= [|j n ->]; first by rewrite muln0 mul1n addn0.
by rewrite mulnDr addnA mulnA expnS.
Qed.

Lemma num2nat_lt_size n : `[n] <  b ^ size n.
Proof.
elim: n => /= [//|j n IH].
have bP : 0 < b by case: (b) j => // [[]].
rewrite -(leq_pmul2l bP) -expnS mulnS in IH.
by apply/(leq_trans _ IH); rewrite ltn_add2r.
Qed.

Lemma num2nat_rcons_lt (i1 i2 : 'I_b) n1 n2 :
  i1 < i2 -> size n1 = size n2 -> `[rcons n1 i1] < `[rcons n2 i2].
Proof.
move=> i1Li2 sE; rewrite num2nat_rcons.
have bP : 0 < b by case: (b) (i1) => // [[]].
rewrite num2nat_rcons -sE.
apply: leq_trans (_ : b ^ size n1 * i1.+1 <= _).
  by rewrite mulnS ltn_add2r num2nat_lt_size.
apply: leq_trans (leq_addl _ _).
by rewrite leq_mul2l orbC i1Li2.
Qed.

End Number.

Notation "`[ n ]" := (num2nat n).

(* On décompose un palindrome par une paire de sa tête et son corps           *)

Lemma rev_tupleE m (n : m.+2.-tuple 'I_10) (Hr : rev n = n) :
  {p : _ * m.-tuple _ | 
    let (a,n1) := p in n = [tuple of a :: rcons n1 a] /\ rev n1 = n1}.
Proof.
case: n Hr => [[|a [|b n1]]] //= i.
rewrite {1 2}[b :: n1]lastI rev_cons rev_rcons => [[aE /eqP]].
rewrite aE eqseq_rcons => /andP[/eqP Hr _].
have Sb : size (belast b n1) == m by rewrite size_belast.
exists (a, Tuple Sb); split => //=.
by apply/val_eqP; rewrite /= -{3}aE -lastI.
Qed.

(* Une première borne pour tous les tuples >= 2                               *)

Lemma lbound_2p m (n1 n2 : m.+2.-tuple 'I_10) : 
  rev n1 = n1 -> rev n2 = n2 -> `[n1] < `[n2] ->  9 + `[n1] < `[n2].
Proof.
move/rev_tupleE=> [[a n3] [-> Rn3]].
move/rev_tupleE=> [[b n4] [-> Rn4]].
case: (ltngtP a b)=> [aLb _|bLa| /= aEb].
- rewrite /=.
  apply: leq_trans (_ : a.+1 + 10 * `[rcons n3 a].+1 <= _); last first.
    by rewrite leq_add // leq_mul2l num2nat_rcons_lt ?size_tuple.
  by rewrite mulnS 2!addnA ltn_add2r [_ + 10]addnC addnS ltn_add2l.
- have  /(num2nat_rcons_lt bLa): size(b :: n4) = size (a :: n3).
    by rewrite !size_tuple.
  by rewrite ltnNge ltn_neqAle andbC => /negPf->.
rewrite -aEb ltn_add2l !num2nat_rcons  -aEb !mulnDr !size_tuple.
rewrite ltn_add2r ltn_mul2l andTb => n3Ln4.
rewrite 2![X in X < _]addnA [X in _ < X]addnA ltn_add2r.
rewrite [_ + a]addnC -addnA ltn_add2l.
apply: leq_trans (_ :  10 * `[n3].+1 <= _); last by rewrite leq_mul2l.
by rewrite mulnS ltn_add2r.
Qed.

(* La même preuve avec une borne de 1 plus large                              *)

Lemma lbound_2p1 m (n1 n2 : m.+2.-tuple 'I_10) : 
  rev n1 = n1 -> rev n2 = n2 -> `[n1] < `[n2] ->  9 + (m != 1) + `[n1] < `[n2].
Proof.
move/rev_tupleE=> [[a n3] [-> Rn3]].
move/rev_tupleE=> [[b n4] [-> Rn4]].
case: (ltngtP a b)=> [aLb _|bLa| /= aEb].
- rewrite /=.
  apply: leq_trans (_ : a.+1 + 10 * `[rcons n3 a].+1 <= _); last first.
    by rewrite leq_add // leq_mul2l num2nat_rcons_lt ?size_tuple.
  by case: eqP; rewrite mulnS 2!addnA ltn_add2r [_ + 10]addnC addnS -addnS.
- have  /(num2nat_rcons_lt bLa): size(b :: n4) = size (a :: n3).
    by rewrite !size_tuple.
  by rewrite ltnNge ltn_neqAle andbC => /negPf->.
rewrite -aEb ltn_add2l !num2nat_rcons  -aEb !mulnDr !size_tuple.
rewrite ltn_add2r ltn_mul2l andTb.
case: (m) n3 n4 Rn3 Rn4=> [[[]] //= _ [[]] // | [|m1]] n3 n4 Rn3 Rn4 n3Ln4.
  rewrite 2![X in X < _]addnA [X in _ < X]addnA ltn_add2r.
  rewrite [_ + a]addnC -addnA ltn_add2l.
  apply: leq_trans (_ :  10 * (`[n3].+1) <= _); last by rewrite leq_mul2l.
  by rewrite mulnS ltn_add2r.
rewrite 2![X in X < _]addnA [X in _ < X]addnA ltn_add2r.
rewrite [_ + a]addnC -addnA ltn_add2l.
apply: leq_trans (_ :  10 * (9 + `[n3]) <= _).
  by rewrite mulnDr ltn_add2r.
by rewrite leq_mul2l ltnW // lbound_2p.
Qed.

(* Propriété d'être un palindrome pour a.+1 b ... b a.+1                      *)

Lemma pmk_prop n (a : 'I_9) b :
  let a' := lift ord0 a in is_pal [tuple of a' :: rcons (nseq n b) a'].
Proof.
apply/eqP; rewrite rev_cons rev_rcons /=.
congr (_ :: rcons _ _).
apply: (@eq_from_nth _ ord0)=> [|i]; first exact: size_rev.
rewrite size_rev size_nseq nth_nseq => iLn.
rewrite nth_rev ?size_nseq // nth_nseq.
by case: n iLn => // n ->; rewrite subSS sub_ord_proof.
Qed.

(******************************************************************************)
(* Distance entre deux palindromes                                            *)
(******************************************************************************)

Definition dist_pal n (p1 p2 : n.-palindrome) := `[p2] - `[p1].
Notation " `d[ p1 , p2 ] " := (dist_pal p1 p2).

Compute `d[[palindrome 1; 3; 3; 1], [palindrome 2; 4; 4; 2]].

(* Pour calculer la distance minimale, on exhibe d'abord deux palindromes qui *)
(* se trouvent à cette distance                                               *)

(* Premier palindrome défini par cas:                                         *)
(* [palindrome 1]                : 1.-palindrome                              *)
(* [palindrome 1; 1]             : 2.-palindrome                              *)
(* [palindrome 1; 0; 1]          : 3.-palindrome                              *)
(* [palindrome 1; 9; 9 ; 1]      : 4.-palindrome                              *)
(* [palindrome 1; 9; ...; 9 ; 1] : n.-palindrome                              *)

Definition p1 n : n.+1.-palindrome :=
  if n is n1.+1 then 
    Pal (pmk_prop n1 (inZp 0) (inZp (9 * (n != 2)))) else [palindrome 1].

(* Deuxième palindrome défini par cas:                                        *)
(* [palindrome 2]                : 1.-palindrome                              *)
(* [palindrome 2; 2]             : 2.-palindrome                              *)
(* [palindrome 1; 1; 1]          : 3.-palindrome                              *)
(* [palindrome 2; 0; 0 ; 2]      : 4.-palindrome                              *)
(* [palindrome 2; 0; ...; 0 ; 2] : n.-palindrome                              *)

Definition p2 n : n.+1.-palindrome :=
  if n is n1.+1 then 
    Pal (pmk_prop n1 (inZp (n != 2)) (inZp (n == 2))) else [palindrome 2].

(* Distance entre p1 et p2:                                                   *)
(*  pour le 1.-palindrome  =  1                                               *)
(*  pour le 2.-palindrome  = 11                                               *)
(*  pour le 3.-palindrome  = 10                                               *)
(*  pour le k.-palindrome  = 11                                               *)

Lemma dist_p1_p2E n :
  `d[p1 n, p2 n] = if n is n1.+1 then if n != 2 then 11 else 10 else 1.  
Proof.
case: n => //= [[| [|n]]] //=.
rewrite /dist_pal /= /bump /= !div.modn_small // !add0n !addn0.
set u := `[_]; set v := `[_]; suff->: u = v + 1.
  by rewrite [v+1]addnC 6!mulnDr 3!addnA subnDr.
rewrite {}/u {}/v; elim : n => //= n ->.
set u := `[_]; rewrite !div.modn_small // mulnDr !muln1 [9 + _]addnC.
by rewrite add0n -addnA.
Qed.

(* La distance entre p1 et p2 est bien la distance minimale                  *)

Lemma dist_pal_max_min_bound n (p q : n.+1.-palindrome) :
  0 < `d[p, q] ->  `d[p1 n, p2 n] <= `d[p, q].
Proof.
have Rp : rev p = p by case (p)=> /= i /andP[_ /eqP].
have Rq : rev q = q by case (q)=> /= i /andP[_ /eqP].
rewrite subn_gt0 dist_p1_p2E.
case: n p q Rp Rq => [|[|[|n]]] p q Rp Rq /=; first by rewrite -subn_gt0.
- by rewrite ltn_subRL; move/(lbound_2p1 Rp Rq); rewrite addn1 addnC.
- by rewrite ltn_subRL; move/(lbound_2p Rp Rq); rewrite addnC.
by rewrite ltn_subRL; move/(lbound_2p1 Rp Rq); rewrite addn1 addnC.
Qed.

(* La solution                                                                *)

Fact dist351 :
  (exists p q : 351.-palindrome, `d[p, q] = 11) /\
  (forall p q : 351.-palindrome, 0 < `d[p, q] -> 11 <= `d[p, q]).
Proof.
have Hd := dist_p1_p2E 350.
split; last by rewrite -{4}[11]Hd; exact: dist_pal_max_min_bound.
exists (p1 350); exists (p2 350); exact: Hd.
Qed.

