From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Nombre.

(* Convertir une liste d'entiers en un entier                                 *)

Definition l2nat l := foldl (fun v i => i + 10 * v) 0 l.

Lemma l2nat_rcons l n : l2nat (rcons l n) = l2nat l * 10 + n.
Proof.
rewrite /l2nat -[rcons _ _]revK rev_rcons foldl_rev.
by rewrite /= -foldl_rev revK addnC mulnC.
Qed.

Compute l2nat [:: 1; 2; 3].


(* Convertir un entier en une liste d'entiers                                 *)

Fixpoint nat2l2 m n := 
   if n < 10 then [:: n] else
   if m is m1.+1 then rcons (nat2l2 m1 (n %/ 10)) (n %% 10) else [::n].

Compute nat2l2 100 123.

Definition nat2l n := nat2l2 n n.

Compute nat2l 123.

Lemma nat2l2K m n : n < 10 ^ m -> l2nat (nat2l2 m n) = n.
Proof.
elim: m n => [[]|m IH n nLD] //=.
case: leqP => _ /=; last by rewrite /l2nat /= addnC.
rewrite l2nat_rcons IH -1?divn_eq //.
rewrite -(ltn_pmul2r (_ : 0 < 10)) // -expnSr (leq_ltn_trans _ nLD) //.
by rewrite {2}(divn_eq n 10) leq_addr.
Qed.

Lemma nat2l2_eq m1 m2 n :
  n < 10 ^ m1 ->  n < 10 ^ m2 -> nat2l2 m1 n = nat2l2 m2 n.
Proof.
wlog : m1 m2 / m1 <= m2 => [H nLm1 nLm2|].
  case: (leqP m1 m2)=> [m1Lm2|m2Lm1]; first by apply: H.
  by apply: sym_equal; apply: H => //; apply: ltnW.
elim: m1 m2 n => [[|m2] [] |] //= m1 IH [|m2] //= n.
rewrite ltnS => m1Lm2 nLm1 nLm2.
case: leqP=> // _; congr rcons.
apply: IH => //.
  rewrite -(ltn_pmul2r (_ : 0 < 10)) // -expnSr (leq_ltn_trans _ nLm1) //.
  by rewrite {2}(divn_eq n 10) leq_addr.
rewrite -(ltn_pmul2r (_ : 0 < 10)) // -expnSr (leq_ltn_trans _ nLm2) //.
by rewrite {2}(divn_eq n 10) leq_addr.
Qed.

Lemma nat2lK n : l2nat (nat2l n) = n.
Proof. by apply: nat2l2K; apply: ltn_expl. Qed.

(******************************************************************************)
(*                                                                            *)
(*              Modélisation des différentes propositions                     *)
(*                                                                            *)
(******************************************************************************)

(* Chiffres décroissants                                                      *)

Definition prop1 l := (1 \in l) == sorted (fun x y => x >= y) l.

Compute prop1 [:: 4; 3; 2; 1; 1; 0].
Compute prop1 [:: 7; 5; 2; 2; 1; 0].

(* Au moins deux chiffres impairs                                             *)

Definition prop2 l := (2 \in l) == (count odd l >= 2).

Compute prop2 [:: 5; 2; 6; 1; 0].
Compute prop2 [:: 1; 1; 3; 2].

(* Tous les chiffres différents                                               *)

Definition prop3 l := (3 \in l) == uniq l.

Compute prop3 [:: 3; 1; 2].
Compute prop3 [:: 4; 4; 3].

(* Quatrième chiffre en partant de la gauche est pair                         *)

Definition prop4 l := (4 \in l) == ~~ odd (nth 0 l 3).

Compute prop4 [:: 4; 3; 1; 6; 0].

(* Produit non divisible par 5                                                *)

Definition prop5 l := (5 \in l) == ~~ (5 %| foldr muln 1 l).

Compute prop5 [:: 4; 2].
Compute prop5 [:: 3; 7].

(* Trois chiffres impairs à la suite                                          *)

Fixpoint todd l := if l is a :: l1 then
                     if l1 is b :: c :: l2 then 
                              [&& odd a, odd b & odd c] || todd l1
                     else false
                   else false.

Definition prop6 l := (6 \in l) == todd l.

Compute prop6 [:: 1; 3; 7; 6].
Compute prop6 [:: 6; 2; 1; 1; 1; 3; 4].

(* Est un nombre premier                                                      *)

Definition prop7 l := (7 \in l) == prime (l2nat l).

Compute prop7 [:: 7].
Compute prop7 [:: 3; 7].

(* Pas plus 2 nombres pairs à la suite                                        *)

Fixpoint teven l := if l is a :: l1 then
                     if l1 is b :: c :: _ then 
                              [&& ~~ odd a, ~~ odd b & ~~ odd c] || teven l1
                     else false
                   else false.

Definition prop8 l := (8 \in l) == ~~ teven l.

Compute prop8 [:: 8; 2; 2].
Compute prop8 [:: 4; 8; 2; 1].

(* Produit des impairs est un carré parfait                                   *)

Definition perfect_square n :=
   all (fun p => ~~ odd p.2) (prime_decomp n).

Compute perfect_square 47.

Definition iprod l := foldr (fun i v => if odd i then i * v else v) 1 l.

Compute iprod [:: 9; 2; 3].

Definition prop9 l := (9 \in l) == perfect_square (iprod l).


(* Un élément distinct est la somme des autres                                *)

Definition prop0 l := (0 \in l) == 
                        (let sum := foldr addn 0 l in
                         ~~ odd sum && (count (pred1 sum./2) l == 1)).

Compute prop0 [:: 5; 7; 2; 0; 0].
Compute prop0 [:: 1; 0; 1; 3; 1].
Compute prop0 [:: 4; 4; 0].

(* Toutes les propositions                                                    *)

Definition check_prop n :=
  let l := nat2l n in
  [&& prop1 l, prop2 l, prop3 l, prop4 l, prop5 l,
      prop6 l, prop7 l, prop8 l, prop9 l& prop0 l].

(* Une version plus rapide                                                    *)
Definition fcheck_prop n := 
  let l := nat2l n in
  if prop9 l then if prop8 l then if prop0 l then if prop6 l then if prop5 l 
  then if prop4 l then if prop3 l then if prop2 l then if prop1 l then prop7 l 
  else false else false else false else false else false else false else false 
  else false else false.

Lemma Pfcheck_prop n : fcheck_prop n = check_prop n.
Proof.
rewrite /check_prop /fcheck_prop.
case: prop9 => //; case prop8 => //; case: prop0; rewrite ?andbF //.
case: prop6 => //; case prop5 => //; case: prop4; rewrite ?andbF //.
case: prop3 => //; case prop2  => //; case: prop1 => //; case: prop7 => //.
Qed.

(* Le résultat                                                                *)

Definition result := l2nat [:: 9; 4; 2; 2; 1; 0].

(* Le résultat vérifie les 10 propositions                                    *)

Fact Presult : check_prop result.
Proof. by vm_compute. Qed.

(******************************************************************************)
(*                                                                            *)
(*     Tester tous les nombres plus petits que 942210                         *)
(*                                                                            *)
(******************************************************************************)


(* Test à zero sur une liste                                                  *)

Definition is_zero l := all (pred1 0) l.

Lemma is_zero_rcons l a : is_zero (rcons l a) = (is_zero l && (a == 0)).
Proof.
elim: l a => [a| b l IH a] /=; first by rewrite andbT.
by rewrite IH andbA.
Qed.

Lemma head_nat2l2_eq0 m n :
   n < 10 ^ m -> (nth 1 (nat2l2 m n) 0  == 0) == (n == 0).
Proof.
elim: m n => [[]|m IH n nLD] //.
rewrite [nat2l2 _ _]/=.
case: leqP=> [DLn|nLN //].
rewrite nth_rcons.
have->: 0 < size (nat2l2 m (n %/ 10)).
  by case: (m) => /=; case: (_ < 10) => // s; rewrite size_rcons.
rewrite (eqP (IH _ _)); last first.
  rewrite -(ltn_pmul2r (_ : 0 < 10)) // -expnSr (leq_ltn_trans _ nLD) //.
  by rewrite {2}(divn_eq n 10) leq_addr.
by move: (DLn); rewrite -divn_gt0 //; case: (n) DLn => // n1; case: (_ %/ _).
Qed.

Lemma is_zero_nat2l2 m n : n < 10 ^ m -> is_zero (nat2l2 m n) == (n == 0).
Proof.
elim: m n => [[]|m IH n nLD] //=.
case: leqP=> [DLn|nLN /=]; last by rewrite andbT.
rewrite is_zero_rcons (eqP (IH _ _)); last first.
  rewrite -(ltn_pmul2r (_ : 0 < 10)) // -expnSr (leq_ltn_trans _ nLD) //.
  by rewrite {2}(divn_eq n 10) leq_addr.
by rewrite {3}(divn_eq n 10) addn_eq0 muln_eq0 orbF.
Qed.

(* Remplacer tous les chiffres par des 9                                    *)

Definition to_nine l := map (fun i : nat => 9) l.

(* Décrémenter de 1 une liste                                               *)

Fixpoint decrr l := 
  if l is a :: l1 then
     if is_zero l1 then
        if a == 0 then to_nine l else a.-1 :: to_nine l1  
     else a :: decrr l1
  else [::].

Definition decr l := 
  if is_zero l then [:: 0] else
  let l1 := decrr l in 
  if l1 is 0 :: a :: l2 then a :: l2 else l1.

Compute decr [:: 1; 2; 3].
Compute decr [:: 1].

Lemma decrr_rcons l a : 
  decrr (rcons l a) = 
     if (a == 0) then rcons (decrr l) 9 else rcons l a.-1.
Proof.
elim: l => //= b l IH.
rewrite is_zero_rcons; case: (boolP (is_zero l)) => [zZ|zNZ] /=; last first.
  by rewrite {}IH; case: (a =P 0) => //.
case: (b =P 0) => [-> | bNZ] /=.
  by rewrite /to_nine map_rcons {}IH; case: (_ == _).
by rewrite /to_nine map_rcons {}IH; case: (_ == _).
Qed.

Lemma Pdecrr m n : n < 10 ^ m -> 0 < n ->
  let l1 := decrr (nat2l2 m n) in 
  (if l1 is 0 :: a :: l2 then a :: l2 else l1)  = nat2l2 m n.-1.
Proof.
elim: m n => [[]|m IH [|n] nLm _] //=.
case: (leqP 10  n.+1) => [DLm|] /= ; last first.
  case: (n) nLm => // n1 nLm nLD.
  by rewrite (leq_ltn_trans _ nLD).
rewrite decrr_rcons.
case: (_ =P 0) => [modZ|modNZ] /=; last first.
  have : n %% 10 < 10 by apply: ltn_pmod.
  rewrite leq_eqVlt ltnS => /orP[/eqP nE10 | mL9].
    by case: modNZ; rewrite -addn1 -modnDml addn1 nE10.
  have /= := head_nat2l2_eq0 nLm.
  rewrite ltnNge DLm /=.
  move: DLm mL9; rewrite ltnS leq_eqVlt => /orP[/eqP<-|] //.
  rewrite ltnNge -ltnS => /negPf-> mL9.
  have [-> -> /=]: (n.+1 %/ 10) = (n %/ 10) /\ (n.+1 %% 10) = (n %% 10).+1.
    have ->: n.+1 = n %/ 10 * 10 + (n %% 10).+1.    
      by rewrite addnS -divn_eq.
    rewrite divnMDl // [_.+1 %/ _]divn_small ?addn0 //.
    by rewrite modnMDl  // modn_small.
  by case: nat2l2=> [|[|a] l] //=; case: modn.
have nLSD : n.+1 %/ 10 < 10 ^ m.
  rewrite -(ltn_pmul2r (_ : 0 < 10)) // -expnSr (leq_ltn_trans _ nLm) //.
  by rewrite {2}(divn_eq n.+1 10) leq_addr.
move: DLm modZ; rewrite ltnS leq_eqVlt => /orP[/eqP<-|DLm] //=.
  by case: (m).
rewrite leqNgt ltnS DLm /= => modD0.
have posD : 0 < n %/ 10 by rewrite divn_gt0.
have modD9 : n %% 10 = 9.
  move: modD0.
  have : n %% 10 < 10 by apply: ltn_pmod.
  rewrite leq_eqVlt eqSS ltnS => /orP[/eqP-> //| DD].
  by rewrite -addn1 -modnDml modn_small addnC.
have posSD : 0 < n.+1 %/ 10.
  by rewrite divn_gt0 // (leq_trans DLm).
rewrite modD9; move: (IH _ nLSD posSD).
have [-> /=]: (n.+1 %/ 10) = (n %/ 10).+1.
  by rewrite {1}[n](divn_eq n 10) -addnS modD9 divnMDl ?addn1.
case: decrr => [|[[HH |a1 l1 <-]|a l <-]] //=.
  by case: (m) => [|m1] //=; case: (_ < _) => //; case: nat2l2.
have nLD : n %/ 10 < 10 ^ m.
  by apply/(leq_ltn_trans _ nLSD)/leq_div2r.
have := nat2l2K nLD; rewrite -HH /l2nat/= muln0.
by case: (_ %/ _) posD.
Qed.

Lemma Pdecr n : decr (nat2l n) = nat2l n.-1.
Proof.
suff {n}H : forall m n, n < 10 ^ m -> decr (nat2l2 m n) = nat2l2 m n.-1.
  suff->: nat2l n.-1 = nat2l2 n n.-1; first by apply/H/ltn_expl.
  apply: nat2l2_eq; first by apply: ltn_expl.
  by apply: leq_trans (leq_ltn_trans (leq_pred _) _) (ltn_expl _ _).
move=> [|m] [|n] // nLD.
rewrite /decr (eqP (is_zero_nat2l2 _)) //=.
by apply: (Pdecrr nLD).
Qed.

(* Une version plus efficace pour vérifier les propositions                   *)

Definition check_propl l :=
  if prop9 l then
    if prop8 l then 
     if prop0 l then
     if prop6 l then
     if prop5 l then
     if prop4 l then
     if prop3 l then
     if prop2 l then
     if prop1 l then prop7 l else false
     else false else false else false else false else false else false 
     else false else false.

Lemma Pcheck_propl n : check_prop n = check_propl (nat2l n).
Proof.
rewrite /check_prop /check_propl.
case: prop9 => //; case prop8 => //; case: prop0; rewrite ?andbF //.
case: prop6 => //; case prop5 => //; case: prop4; rewrite ?andbF //.
case: prop3 => //; case prop2  => //; case: prop1 => //; case: prop7 => //.
Qed.

(* Vérifier en décrémentant progressivement                                   *)
Fixpoint check_less l n := 
  let l1 := decr l in
  if n is n1.+1 then check_propl l1 || check_less l1 n1 
                         else false.

Lemma Pcheck_less n m :
  check_less (nat2l n) m = false ->  forall k, n - m <= k < n -> ~ check_prop k.
Proof.
elim: m n => [m _ k|m IH [|n]] //=.
  by rewrite subn0 leqNgt; case: (_ <= _).
rewrite Pdecr /= subSS -Pcheck_propl.
case: (boolP (check_prop _)) => //= /negP cP /IH H k.
rewrite [k < _]leq_eqVlt eqSS ltnS; case: eqP=> [->|kDl] //=.
by exact: H.
Qed.

(* Tous les nombres plus petits ne vérifient pas les 10 propositions          *)

Fact Lresult : forall m, m < result -> ~ check_prop m.
Proof.
move=> m mLr.
have: result - result <= m < result by rewrite subnn leq0n.
move: {mLr}m.
have F : check_less (nat2l result) result = false
  by vm_cast_no_check (refl_equal false).
apply: (Pcheck_less F).
Qed.

End Nombre.
