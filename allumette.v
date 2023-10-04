From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.

Import GRing.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Allumette.

(******************************************************************************)
(*                                                                            *)
(*                                                                            *)
(*                          MODÉLISATION                                      *)
(*                                                                            *)
(*                                                                            *)
(******************************************************************************)

(* Les tas d'allumette sont représentés par une suite de nombres              *)

Definition val := nat.
Definition heaps := seq val.

(* L'exemple                                                                  *)

Definition heaps0 : heaps := [:: 5; 6 ; 4].

(* Une suite de tas vides                                                     *)

Definition empty (h : heaps) := h == nseq (size h) 0.

Compute empty heaps0.

(* Un coup est représenté par un numéro de tas et le nombre d'allumettes      *)
(* restante                                                                   *)
 
Definition move := (nat * val)%type.

(* Laisser 4 allumettes dans le deuxième tas                                  *)

Definition move0 : move := (1, 4).

(* Effectuer un coup                                                          *)

Definition make_move (h : heaps) (m : move) : heaps :=
  let (i, v) := m in take i h ++ v :: drop i.+1 h.

Compute make_move heaps0 move0.

(* Un coup est valide si le nombre d'allumettes restantes diminue strictement *)

Definition valid_move (h : heaps) (m : move) := 
  let (i, v) := m in v <  nth 0 h i.

Compute valid_move heaps0 move0.

(* Une partie est une suite de coups                                          *)

Definition game := seq move.

Definition game0 := [:: (0, 0); (1, 1); (1, 0); (2, 0)].

(* Une partie est valide si chacun de ses coups est valide et se termine par  *)
(* un tas vide                                                                *)

Fixpoint valid_game (h : heaps) (g : game) :=
  if g is m :: g1 then valid_move h m && valid_game (make_move h m) g1
  else empty h.

Compute valid_game heaps0 game0.

(* Une strategie est une fonction qui retourne un coup valide                 *)

Inductive strategy := 
  Strategy (f : heaps -> move) of forall h, ~~ empty h -> valid_move h (f h).

Definition fun_of_strategy s := let: Strategy f _ := s in f.

Coercion fun_of_strategy : strategy >-> Funclass.

(* La stratégie qui vide le premier tas non vide                              *)

Definition pick_first (h : heaps) : move := (find (predC1 0) h, 0). 

Lemma valid_pick_first h : ~~ empty h -> valid_move h (pick_first h).
Proof. by elim: h => //= [] [|a]. Qed.

Definition strat0 := Strategy valid_pick_first.

Compute strat0 heaps0.

(* On s'intéresse au premier joueur. Une partie suit une stratégie si tout    *)
(* coup pair est effectué par la stratégie                                    *)

Fixpoint follow_strategy (s : strategy) (h : heaps) (g : game) :=
  if g is m1 :: g1 then (m1 == s h) && 
       if g1 is m2 :: g2 then 
          let h2 := make_move (make_move h m1) m2 in follow_strategy s h2 g2 
       else true
   else true.

Compute follow_strategy strat0 heaps0 game0.

(* Une stratégie est gagnante si, en suivant la stratégie, toutes les parties *)
(* sont de longueur impaire                                                   *)

Definition winning_strategy s h :=
  forall g, valid_game h g -> follow_strategy s h g -> odd (size g).

Lemma nw_strat0 : ~ winning_strategy strat0 heaps0.
Proof. by move=> Hs; suff: false by []; apply: (Hs game0). Qed.

(* Une stratégie gagnante va se servir de la représentation binaire des       *)
(* nombres                                                                    *)

(******************************************************************************)
(*                                                                            *)
(*                      NOMBRES BINAIRES                                      *)
(*                                                                            *)
(******************************************************************************)

Section Nombre.

Variable n : nat.

(* On utilise la représentation des nombres comme un tuple de booléens        *)

Local Notation number := (n.-tuple bool).

(* Un ou exclusif sur les nombres                                             *)

Definition addm (m1 m2 : number) :=
   [tuple of [seq x.1 (+) x.2 | x <- zip m1 m2]].

Notation  "%[+]" := addm (at level 0).
Notation  "x  [+]  y" := (addm x y) (at level 10).

(* Le nombre zéro                                                             *)

Definition falsem := [tuple of nseq n false].

Notation  F :=  falsem.

Lemma diffF m : m != F -> true \in m.
Proof.
move=> mDF; apply: contraR mDF => /negP nI; apply/eqP/val_eqP.
have: all (pred1 false) m by apply/allP=> [[]].
by move/all_pred1P; rewrite size_tuple /= => ->.
Qed.

(* Un ensemble de règles de réécriture                                        *)

Definition rewL := 
  ((fun n => @tnth_nth n _ false), nth_map (false,false), nth_zip,
          nth_nseq, ltn_ord, size_nseq, size_tuple, size_zip, minnn).

(* Propriétés génériques du ou exclusif sur les nombres                       *)

Lemma addFm : left_id F %[+].
Proof.  by move=> x; apply: eq_from_tnth => i; rewrite !rewL. Qed.

Lemma addmm : self_inverse F %[+].
Proof. by move=> x; apply: eq_from_tnth => i; rewrite !rewL ?addbb. Qed.

Lemma addmC : commutative %[+].
Proof. by move=> x y; apply: eq_from_tnth => i; rewrite !rewL 1?addbC. Qed.

Lemma addmA : associative %[+].
Proof. by move=> x y z; apply: eq_from_tnth => i; rewrite !rewL ?addbA. Qed.

HB.instance Definition _ := 
  GRing.isZmodule.Build number addmA addmC addFm addmm.

(* Conversion `[_] de nombre vers entier naturel                              *)

Fixpoint num2nat (n : nat) (l : seq bool) :=
  if n is m1.+1 then 2^ m1 * head false l + num2nat m1 (behead l)
  else 0.

Notation "`[ m ]_ n" := (num2nat n m) (at level 40).

Lemma num2natE (m : n.-tuple bool) :
  `[m]_n =  \sum_(i < n) 2 ^ (n.-1 - i) * tnth m i.
Proof.
elim: n m => /= [l|n1 IH l]; first by rewrite big_ord0.
rewrite (IH [tuple of behead l]) [l]tuple_eta /= /num2nat.
rewrite big_ord_recl /=; congr (_ + _).
  by rewrite subn0 (tnth_nth false).
apply: eq_bigr=> i _; rewrite !rewL lift0 /=.
by rewrite /bump /=  add1n -subn1 -subnDA add1n.
Qed.

Lemma num2natF : `[F]_n = 0.
Proof. by rewrite num2natE big1 => // i; rewrite !rewL muln0. Qed.

Lemma num2nat_eqF0 (m : number) :  (`[m]_n  == 0) = (m == F).
Proof.
apply/eqP/eqP=> [|->]; last by rewrite num2natF.
rewrite /falsem.
elim: n m => [m _ /= |n1 IH m /eqP]; first by rewrite [m]tuple0; apply/val_eqP.
rewrite /= addn_eq0 muln_eq0 expn_eq0 //= => /andP[F1].
move/eqP/(IH [tuple of behead m]) => /val_eqP /eqP /= F2.
rewrite [m]tuple_eta; apply/val_eqP/eqP=> /=; congr (_ :: _) => //.
rewrite [m]tuple_eta /= /thead !rewL /=.
by case: (m) F1=> [[]] //= [].
Qed.

(* Conversion `{_} de nombre vers entier naturel                              *)

Fixpoint nat2num (m : nat) (v : nat) : m.-tuple bool :=
  if m is m1.+1 then [tuple of rcons (nat2num m1 v./2) (odd v)]
  else [tuple of [::]].

Notation "`{ m }_ n " := (@nat2num n m) (at level 10).

Lemma nth_nat2num m (v : nat) i :
   tnth (`{v}_m) i = odd (v %/ (2 ^ (m.-1 - i)))%N.
Proof.
elim: m v i => //= [v [] //|m IH v i].
rewrite !rewL nth_rcons size_tuple.
move: (ltn_ord i); rewrite ltnS leq_eqVlt => /orP[/eqP iEm|iLm].
  by rewrite ltnNge iEm leqnn eqxx subnn divn1.
have Nd : m.-1.+1 = m.
  by rewrite prednK // (leq_ltn_trans _ iLm).
rewrite -{8}Nd iLm subSn -1?ltnS ?Nd // expnS divnMA divn2.
by move: (IH v./2 (Ordinal iLm)); rewrite !rewL.
Qed.

Lemma nat2numE m v : 
  v < 2 ^ m -> `{v}_m.+1 = [tuple of false :: `{v}_m].
Proof.
move=> vL2n.
apply: eq_from_tnth=> i.
rewrite nth_nat2num /= (tnth_nth false) /=.
case: i=> [[|i]] /=; first by rewrite subn0 divn_small.
rewrite ltnS => iLm.
have ->: m - i.+1 = m.-1 - i.
  by rewrite -{1}[m]prednK ?subSS // (leq_trans _ iLm).
by move: (nth_nat2num v (Ordinal iLm)); rewrite (tnth_nth false) /= => ->.
Qed.

Lemma nat2num0 : `{0}_n = F.
Proof.
apply/val_eqP/eqP=> /=; elim: n => [|n1 /= ->] //=.
by elim: n1 => //= n1 ->.
Qed.

Lemma nat2numK v : v < 2 ^ n -> `[`{v}_n ]_n = v.
Proof.
rewrite num2natE; elim: n v => [[_|[|v]] |n1 IH v Hv] //=.
  by rewrite big_ord0.
rewrite big_ord_recr /= !rewL /= nth_rcons rewL ltnn eqxx subnn.
rewrite -[X in _ = X]odd_double_half [X in _ = X]addnC ?mul1n; congr (_ + _).
have/IH{4}<- : v./2 < 2 ^ n1.
  rewrite -(ltn_pmul2l (_ : 0 < 2)) // -expnS mul2n.
  apply: leq_ltn_trans Hv.
  by rewrite -{2}[v]odd_double_half; case: odd.
rewrite -mul2n big_distrr; apply: eq_bigr => i _ /=.
rewrite !rewL /= nth_rcons !rewL mulnA -expnS -subSn.
  by case: (n1) i => // [[]].
by  case: (n1) i => // [[]|n2 i] //=; rewrite -ltnS.
Qed.

(* Un lemme pour calculer les sommes de puissances de 2                       *)

Lemma sum_pow2 k n1 : \sum_(k <= j < n1) 2 ^ (n1.-1 - j) = (2 ^ (n1 - k)).-1.
Proof.
rewrite -{1}[k]add0n big_addn.
pose F i := 2 ^ ((n1 - k).-1 - i).
rewrite (eq_bigr _  (_ : forall i, _ -> _ = F i)) {}/F //; last first.
  by move=> i; rewrite addnC subnDA {}/F; case: n1 => //= n1; rewrite subSKn.
elim: (_ - _) => [|n2 IH]; first by rewrite big_geq.
rewrite big_nat_recr //= subnn expn0 big_nat_cond.
pose F i := 2 * 2 ^ (n2.-1 - i).
rewrite (eq_bigr _  (_ : forall i, _ -> _ = F i)) {}/F //; last first.
  move=> u; case: (n2) => //= n3; rewrite andbT ltnS => Hu.
  by rewrite -expnS subSn. 
rewrite -big_nat_cond -big_distrr /= IH -subn1 mulnBr muln1 -expnS.
have: 2 ^ 0 < 2 ^ n2.+1 by rewrite ltn_exp2l.
by case: (_ ^ _.+1) => // [[|n3]] //=; rewrite [_ - _]subn0 addn1.
Qed.

Lemma num2natK (v : number) : `{`[v]_n }_n = v.
Proof.
apply: eq_from_tnth => i.
have nPos : 0 < n by apply: leq_trans (ltn_ord i).
pose F (m : number) i :=  2 ^ (n.-1 - i) * nth false m i.
have sE : forall m : number, `[m]_n = \sum_(0 <= i < n) F m i.
  move=> m; rewrite big_mkord num2natE; apply: eq_bigr => // i1.
  by rewrite /num2nat /= rewL.
rewrite sE nth_nat2num.
rewrite (big_cat_nat _  _  _  (leq0n i.+1)) // /= big_nat_recr //= big_nat_cond.
have F1 (m : number) j : (0 <= j < i) && true ->
     F m j =  2 ^ (n.-1 - i) * (2 ^ (i - j) * nth false m j).
  rewrite andbT => /andP[_ jLi]; rewrite mulnA -expnD /F.
  rewrite -{1}(subnK (_ : i <= n.-1)); last by rewrite -ltnS prednK.
  by rewrite addnBA // ltnW.
rewrite (eq_bigr _ (F1 v)) -big_distrr /= -mulnDr mulnC divnMDl ?expn_gt0 //.
rewrite divn_small; last first.
  rewrite -subSS [n.-1.+1](ltn_predK (_ : 0 < _)) //.
  rewrite -[_ ^ _](ltn_predK (_ : 0 < _)) ?expn_gt0 // ltnS -sum_pow2.
  by apply: leq_sum=> j _; rewrite /F; case: nth; rewrite ?muln0 ?muln1.
have F2 (m : number) j : (0 <= j < i) && true ->
     2 ^ (i - j) * nth false m j =  2 * (2 ^ (i.-1 - j) * nth false m j).
  rewrite andbT => /andP[_ jLi].
  have iE : i.-1.+1 = i by rewrite prednK // (leq_trans _ jLi).
  rewrite mulnA -expnS -subSn -1?ltnS iE //.
rewrite (eq_bigr _ (F2 v)) -big_distrr /= addn0 oddD oddM /= rewL.
by case: nth.
Qed.

(* Bit de poids fort                                                          *)

Definition hbit (m : number) := index true m.

Lemma hbitF : hbit F = n.
Proof. by rewrite /hbit /falsem /=; elim: n => //= n1 ->. Qed.

Lemma hbit_ltn m : m != F -> hbit m < n.
Proof.
move=> mDF.
rewrite -(size_tuple m) -has_find.
apply/hasP; exists true => //=; exact: diffF.
Qed.

Lemma hbit_true m (i : 'I_n) : hbit m = i -> tnth m i = true.
Proof.
case: (boolP (m == F))=> [/eqP->|].
  by rewrite hbitF => nE; move: (ltn_ord i); rewrite -nE ltnn.
by rewrite rewL => mDF <-; rewrite nth_index // diffF.
Qed.

Lemma hbit_lt m (i : 'I_n) : i < hbit m -> tnth m i = false.
Proof. 
by rewrite /hbit /index rewL => /(before_find false); case: nth.
Qed.


(* Lemme clé qui va assurer que le nombre d'allumettes décroit                *)

Lemma ltn_num_addm m1 m2 (i : 'I_n) :
   hbit m1 = i -> tnth m2 i = true -> `[m1 [+] m2]_n < `[m2]_n.
Proof.
move=> hbE Tt.
pose F (m : number) i :=  2 ^ (n.-1 - i) * nth false m i.
have sE : forall m : number, `[m]_n = \sum_(0 <= i < n) F m i.
  move=> m; rewrite big_mkord num2natE; apply: eq_bigr => // i1.
  by rewrite /num2nat /= rewL.
pose F1 := big_cat_nat _  _  _  (leq0n i) (ltnW (ltn_ord i)).
 rewrite !{}sE !{}F1 /=.
have<-: \sum_(0 <= j < i) F m2 j = \sum_(0 <= j < i) F (m1 [+] m2) j.
  rewrite big_nat_cond [X in _ = X]big_nat_cond.
  apply: eq_bigr => j; rewrite andbT => /andP[_ jLi]; congr (_ * _).
  have jLn : j < n by apply: ltn_trans jLi _.
  move: (@hbit_lt m1 (Ordinal jLn)) => /=.
  by rewrite !rewL //= => -> //; rewrite hbE.
rewrite ltn_add2l.
rewrite big_ltn_cond // [X in _ < X]big_ltn_cond //.
move: Tt; rewrite /F !rewL //= => ->.
move/hbit_true: hbE; rewrite rewL => ->.
rewrite muln0 add0n muln1.
apply: ltn_addr.
apply: leq_ltn_trans (_ : \sum_(i.+1 <= j < n) 2 ^ (n.-1 - j) < _).
  by apply: leq_sum => i1 _; case: nth; rewrite (muln1, muln0).
rewrite sum_pow2 prednK ?expn_gt0  //.
by rewrite -[X in _ <= _ ^ X]subSS prednK // (leq_trans _ (ltn_ord i)).
Qed.

Lemma addm_nth_orb (m1 m2 : number) i : 
  tnth (m1 [+] m2) i -> tnth m1 i || tnth m2 i.
Proof. by rewrite !rewL //; case: nth. Qed.

Lemma addm_nth_exists (l : seq number) i : 
  tnth (\sum_(i <- l) i)%R i ->  {j | j < size l /\ tnth (nth F l j) i}.
Proof.
elim: l => /= [|a l IH]; first by rewrite big_nil !rewL.
rewrite big_cons => /addm_nth_orb.
by case: (boolP (tnth a i)) => [Ht _|_ /IH [j [H1j H2j]]];
   [exists 0 | exists j.+1].
Qed.

End Nombre.

Notation  "%[+]" := (@addm _).
Notation  "x  [+]  y" := (addm  x y) (at level 10).
Notation  F :=  (@falsem _).
Notation "`[ m ]_ n " := (num2nat n m) (at level 10).
Notation "`{ m }_ n " := (nat2num n m) (at level 10).

(******************************************************************************)
(*                                                                            *)
(*                      STRATÉGIE GAGNANTE                                    *)
(*                                                                            *)
(******************************************************************************)

Definition pick_best (h : heaps) : move :=
(* nombres de bits nécessaires pour coder les entiers dans la liste           *)
  let n := foldr maxn 0 h in 
(* conversion de la suite d'entiers en une suite de nombres binaires          *)
  let l := [seq (nat2num n i) | i <- h] in
(* le ou exclusif de tous les éléments de la suite                            *)
  let v := foldr %[+] F l in
(* Si le ou exclusif est nul, prendre la stratégie first_pick                 *)
  if v == F then pick_first h else
(* Sinon on cherche le tas dont le ou exclusif fait baisser la valeur         *)
  let i := find (fun a => `[v [+] a]_n <  `[a]_n) l in
  let x := `[v [+] (nth F l i)]_n in (i, x).

(* pick_best génère que des coups valides                                     *)

Lemma valid_pick_best h : ~~ empty h -> valid_move h (pick_best h).
Proof.
move=> NE; rewrite /valid_move /pick_best.
set n := foldr _ 0 _.
set l := [seq _ | i <- _].
set v := foldr _ F _.
pose f a := `[v [+] a]_n < `[a]_n.
have h2l i1 : nth F l i1 = nat2num n (nth 0 h i1).
  rewrite /l; move: nat2num (nat2num0 n) => f1 fE.
  by elim: (h) i1 => [i1|a h1 IH [|i1]] //=; rewrite !nth_nil fE.
case: (boolP (_ == _))=> [vF|vNF]; first by exact: valid_pick_first.
have vE : v = (\sum_(i <- l) i)%R.
  rewrite /v /=.
  by elim: (l) => [/= | a l1 /= ->]; [rewrite big_nil | rewrite big_cons].
pose i := Ordinal (hbit_ltn vNF).
have/addm_nth_exists[j [jLs tnthT]]: tnth (\sum_(i <- l) i)%R i.
  by apply: hbit_true; rewrite -vE.
have: `[v [+] (nth F l j)]_n < `[nth F l j]_n by apply: ltn_num_addm tnthT.
rewrite !h2l => vLn.
have: has f l.
  case: (leqP (size h) j)=> [shLj|jLsh].
    by rewrite (nth_default 0 shLj) nat2num0 num2natF in vLn.
  apply/hasP; exists (nat2num n (nth 0 h j)) => //.
  by apply/map_f/mem_nth.
move/(nth_find F); rewrite {1}/f h2l // nat2numK // /n.
elim: (h) (find _ _) => [k|a h1 IH [|k]] /=; first by rewrite nth_nil.
  apply: leq_trans (ltn_expl _ (_ : 1 < 2)) (leq_pexp2l _ (leq_maxl _ _)) => //.
by apply: leq_trans (IH _) (leq_pexp2l _ (leq_maxr _ _)).
Qed.

(* La stratégie gagnante                                                      *)

Definition strat_best := Strategy valid_pick_best.

Definition is_winning (h : heaps) := 
  let n := foldr maxn 0 h in 
  let l := [seq (nat2num n i) | i <- h] in
  let v := foldr %[+] F l in v != F.

Lemma is_winningE h :
  let n := foldr maxn 0 h in 
  is_winning h = (`[\sum_(i <- h) (nat2num (foldr maxn 0%N h) i)]_n != 0%N)%R.
Proof. by move=> n; rewrite num2nat_eqF0 /is_winning foldr_map unlock /=. Qed.

Lemma is_winning_not_empty h : is_winning h -> ~ empty h.
Proof.
move/eqP=> NISW /eqP IE; case: NISW; rewrite IE.
have ->: foldr maxn 0 (nseq (size h) 0) = 0 by elim: size => //= n ->.
elim: size => //= n ->.
have ->: [tuple] [+] F = ([tuple] + 0)%R by [].
by rewrite addr0 [F]tuple0.
Qed.

Lemma big_nat2num_eq n1 n2 h : 
  all (fun i => i < 2 ^ n1) h -> all (fun i => i < 2 ^ n2) h ->
 (`[\sum_(i <- h) `{i}_n1]_n1 = `[\sum_(i <- h) `{i}_n2]_n2)%R.
Proof.
wlog: n1 n2 h / n1 < n2 => [WH|].
  case: (ltngtP n1 n2)=> [||-> //]; first by exact: WH.
  by move=> *; apply: sym_equal; apply: WH.
move=> n1Ln2 aLn1 _; apply: sym_equal.
elim: n2 n1Ln2 => // n2 IH; rewrite ltnS => n1Ln2.
have->: (\sum_(i <- h) nat2num n2.+1 i =
      [tuple of false ::\sum_(i <- h) nat2num n2 i])%R.
  elim: (h) aLn1 => [_|a h1 IH1 /andP[aH aLn1]].
    by rewrite !big_nil; apply/val_eqP.
  rewrite !big_cons IH1 ?nat2numE //; first by apply/val_eqP.
  by apply: leq_trans aH (leq_pexp2l _ n1Ln2).
move: n1Ln2; rewrite /= muln0 leq_eqVlt => /orP[/eqP<-|nLm1] //.
by apply: IH.
Qed.

(* On peut évaluer la somme dans la position précédente                       *)

Lemma sum_make_move h m : 
 let h1 := make_move h m in
 let n1 := foldr maxn 0 h in let n2 := foldr maxn 0 h1 in 
 valid_move h m ->
 (`[\sum_(i <- h1) `{i}_n2 ]_n2 = `[\sum_(i <- h1) `{i}_n1]_n1)%R.
Proof.
case: m => i v h1 n1 n2 /=.
case: (leqP (size h) i)=>[/(nth_default 0)-> // | iLs vLn].
have n2Ln1 : n2 <= n1.
  suff : \max_(i <- h1) i <= \max_(i <- h) i by rewrite !unlock.
  have->: h = take i h ++ nth 0 h i :: drop i.+1 h.
    by rewrite -cat_rcons -take_nth // cat_take_drop.
  by rewrite !big_cat /= !big_cons !geq_max ?leq_max ?leqnn ?(ltnW vLn) ?orbT.
have aP : all (fun i : nat => i < 2 ^ n2) h1.
  apply/allP=> j iIh1; apply: (leq_trans (ltn_expl _ (_ : 1 < 2))) => //.
  apply: leq_pexp2l => //.
  rewrite {n2Ln1}/n2; elim: h1 iIh1 => //= a l IH.
  by rewrite in_cons => /orP[/eqP->|/IH/leq_trans->//]; 
                 [apply: leq_maxl|apply: leq_maxr]. 
apply: big_nat2num_eq => //.
apply/allP=> x /(allP aP)/leq_trans->//.
by apply: leq_pexp2l.
Qed.

(* Après un coup d'une position perdante on obtient une position gagnante     *)

Lemma nis_winning_is_winning h m : 
  valid_move h m -> ~ is_winning h -> is_winning (make_move h m).
Proof.
case: m => i v; rewrite [valid_move _ _]/= => vLi.
rewrite !is_winningE sum_make_move //=.
move/negP; rewrite negbK  !num2nat_eqF0 => /eqP <-.
set n := foldr _ _ _.
have iLs : i < size h.
  by case: leqP => // sLv; rewrite /= nth_default in vLi.
have{3}->: h = take i h ++ nth 0 h i :: drop i.+1 h.
  by rewrite -cat_rcons -take_nth // cat_take_drop.
rewrite !big_cat /= !big_cons addrCA [X in _ != X] addrCA.
apply/negP => /eqP /addIr Eq.
have nLn : nth 0 h i < 2 ^ n.
  apply: leq_trans (ltn_expl _ (_ : 1 < 2)) (leq_pexp2l _ _) => //.
  rewrite /n; elim: (h) (i) iLs => //= a h1 IH [_ |i1] /=.
     by apply: leq_maxl.
  by rewrite ltnS => /IH /leq_trans -> //; apply: leq_maxr.
move: (vLi).
by rewrite -[v](@nat2numK n) ?Eq ?nat2numK ?ltnn // (ltn_trans vLi).
Qed.

(* Après un coup d'une position gagne en suivant la stratégie on obtient une  *)
(* position perdante                                                          *)

Lemma is_winning_nis_winning h : 
  is_winning h -> ~ is_winning (make_move h (strat_best h)).
Proof.
rewrite !is_winningE => iW.
have vM:  valid_move h (pick_best h).
  by apply/valid_pick_best/negP/is_winning_not_empty; rewrite is_winningE.
rewrite sum_make_move //.
apply/negP; rewrite negbK /=.
set n := foldr _ _ _.
move: vM ; rewrite /pick_best.
set l := [seq _ | i <- _].
set u := find _ _.
have ->: foldr %[+] F l = (\sum_(i <- h) `{i }_ n)%R.
  by rewrite unlock foldr_map.
rewrite -num2nat_eqF0 (negPf iW) num2nat_eqF0 big_cat big_cons num2natK /=.
case: (leqP (size h) u)=> [sLu|uLs _].
  rewrite [X in _ < X -> _]nth_default //.
have{3}->: h = take u h ++ nth 0 h u :: drop u.+1 h.
  by rewrite -cat_rcons -take_nth // ?cat_take_drop.
rewrite big_cat big_cons /= !addrA !addrN !add0r.
rewrite (nth_map 0) // -/n [X in (X + _)%R == _]addrAC.
by rewrite addrN add0r addrN.
Qed.


(* En combinant les deux propriétés précédentes, la stratégie est gagnante!   *)

Lemma w_strat_best h : is_winning h -> winning_strategy strat_best h.
Proof.
move=> iW g.
have [n leMn] := ubnP (size g); elim: n => // n IH in h iW g leMn *.
case: g leMn => [_ /is_winning_not_empty |m1 [|m2 g]] //=.
rewrite negbK ltnS => sLn /and3P[H1 H2 H3] /andP[/eqP m1F FS].
apply: IH FS => //; last by rewrite ltnW.
apply: nis_winning_is_winning => //.
by rewrite m1F; apply: is_winning_nis_winning.
Qed.

(* Notre exemple est gagnant                                                  *)

Fact w_strat_best0 : winning_strategy strat_best heaps0.
Proof. by apply:  w_strat_best. Qed.

(* Pour finir, une petite partie                                              *)

Compute heaps0.

(* Premier coup                                                               *)

Definition m0 := strat_best heaps0.
Compute m0.

Definition heaps1 := make_move heaps0 m0.
Compute heaps1.

(* Deuxième coup : on laisse 3 allumettes dans le deuxième tas                *)

Definition m1 := (1, 3).

Definition heaps2 := make_move heaps1 m1.
Compute heaps2.

(* Troisième coup                                                             *)

Definition m2 := strat_best heaps2.
Compute m2.

Definition heaps3 := make_move heaps2 m2.
Compute heaps3.

(* Quatrième coup : on laisse 1 allumette dans le deuxième tas                *)

Definition m3 := (1, 1).

Definition heaps4 := make_move heaps3 m3.
Compute heaps4.

(* Cinquième coup                                                             *)

Definition m4 := strat_best heaps4.
Compute m4.

Definition heaps5 := make_move heaps4 m4.
Compute heaps5.

(* Sixième coup : on laisse 0 allumette dans le dernier tas                   *)

Definition m5 := (2, 0).

Definition heaps6 := make_move heaps5 m5.
Compute heaps6.

(* Dernier coup                                                               *)

Definition m6 := strat_best heaps5.
Compute m6.

Definition heaps7 := make_move heaps6 m6.

(* Gagné!                                                                     *)

Compute empty (heaps7).

End Allumette.

