From mathcomp Require Import all_ssreflect all_algebra all_fingroup.

Import GRing.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Corde.

(******************************************************************************)
(*                                                                            *)
(*                                                                            *)
(*                          MODÉLISATION                                      *)
(*                                                                            *)
(*                                                                            *)
(******************************************************************************)


(* Un ensemble de noeuds est une permutation dont tous les cycles sont de     *)
(* longueur 2                                                                 *)

Definition is_node n :=  
  [set p | [forall i : 'I_n,  ((p : 'S_n) (p i) == i) && (p i != i)]].

Notation " 'N[ n ] " := (@is_node n).

Lemma is_nodeK n (p : 'S_n) i : p \in 'N[n] -> p (p i) = i.
Proof. by rewrite inE => /forallP/(_ i)/andP[/eqP]. Qed.

Lemma is_node_diff n (p : 'S_n) i : p \in 'N[n] -> p i != i.
Proof. by rewrite inE => /forallP/(_ i)/andP[]. Qed.

Lemma is_node_flip n p i j : p \in 'N[n] -> p i = j -> p j = i.
Proof. by move=> pIN <-; rewrite is_nodeK. Qed.

(* Une configuration valide est une paire de permutation de 2-cycles          *)

Definition config n := ('S_n * 'S_n)%type.

Definition cvalid n : {set config n} := setX 'N[n] 'N[n].

Notation " 'N2[ n ] " := (cvalid n).

(* On suit la corde i pour m.*2 suivant la config c                          *)

Fixpoint follow m n (c : config n) x := 
  if m is m1.+1 then x :: c.1 x :: follow m1 c (c.2 (c.1 x)) else [::].

(* On obtient bien une liste de longuer 2m                                   *)
Lemma size_follow m n (c : config n) x : size (follow m c x) = m.*2.
Proof. by elim: m x => //= m IH x; rewrite IH. Qed.

(* Les cordes sont toutes liées entre elles, si en suivant la corde 0 on     *)
(* obtient toutes les cordes                                                 *)

Definition c2l n (c : config n.+1.*2) : seq 'I_n.+1.*2 := follow n.+1 c 0%R.

Definition one_cycle n := [set c | uniq (@c2l n c)].
Notation " 'O[ n ] " := (@one_cycle n).

(******************************************************************************)
(*                                                                            *)
(*                     NOMBRE DE CONFIGURATIONS                               *)
(*                                                                            *)
(******************************************************************************)


(* Les ordinaux plus petits qu'une certaine valeur                            *)

Definition lordinal n k :=  [set i | (i : 'I_n) < k].

Lemma card_lordinal n k : k <= n -> #|lordinal n k| = k.
Proof.
elim: k => /= [_|k IH kLn].
  by apply/eqP; rewrite cards_eq0; apply/eqP/setP=> i; rewrite inE.
rewrite (cardD1 (Ordinal kLn)) !inE leqnn /=; congr (_.+1).
rewrite -[X in _ = X]IH /=; last by rewrite -ltnS; apply/ltnW.
apply: eq_card => i; rewrite !inE /=.
have->: (i == Ordinal kLn) = (i == k :> nat).
  by apply/eqP/eqP=> [->|HH] //=; apply/val_eqP/eqP.
by rewrite ltnS -ltn_neqAle.
Qed.


(* Enlever les deux cycles (i, p i) et (j, p j)                               *)

Definition swap_node n (p : 'S_n) i j :=
    (p * tperm i (p i) * tperm j (p j) * tperm (p i) (p j))%g.

Lemma swap_nodeL n (p : 'S_n) i j :
  p i != i -> p (p j) = j ->  i != j -> swap_node p i j i = i.
Proof.
move=> piDi ppJ iDj; rewrite !permM tpermR.
case: (tpermP _ _ i)=> [iEj|->|_ /eqP iDpj]; first by have /eqP := iDj.
  by rewrite ppJ tpermL.
by rewrite tpermD // eq_sym.
Qed.

Lemma swap_nodeLp n (p : 'S_n) i j :
  p i != j -> p (p i) = i -> i != j -> swap_node p i j (p i) = p j.
Proof.
move=> piDj ppI iDj; rewrite !permM ppI tpermL.
case: (tpermP _ _ (p i)); rewrite ?tpermL //; first by have /eqP := piDj.
by move=> /perm_inj; have /eqP := iDj.
Qed.

Lemma swap_nodeR n (p : 'S_n) i j :
  p j != j -> p (p j) = j ->  i != j -> swap_node p i j j = j.
Proof.
move=> pjDj ppJ iDj; rewrite !permM.
case: (tpermP _ _ (p j))=> [<-|/perm_inj jEi|/eqP iDpj _].
- by rewrite ppJ tpermL tpermR.
- by have /eqP := iDj; rewrite jEi.
rewrite tpermR tpermD //.
by apply: contra iDpj; rewrite eq_sym -{1}ppJ  => /eqP /perm_inj ->.
Qed.

Lemma swap_nodeRp n (p : 'S_n) i j :
  p i != j -> p (p j) = j -> i != j -> swap_node p i j (p j) = p i.
Proof.
move=> piDj ppJ iDj; rewrite !permM ppJ [tperm _ _ j]tpermD //.
by rewrite tpermL tpermR.
Qed.

Lemma swap_nodeD n (p : 'S_n) i j k :
 p (p i) = i -> p (p j) = j -> 
 k \notin [:: i; j; p i; p j] -> swap_node p i j k = p k.
Proof.
move=> ppI ppJ kIH.
suff: p k \notin [:: i; j; p i; p j].
  rewrite !inE !negb_or => /and4P[kDi kDj kDpi kDpj].
  by rewrite !permM !tpermD // eq_sym.
rewrite -{1}ppI -{1}ppJ.
by apply: contra kIH; rewrite !inE => /or4P[] /eqP /perm_inj ->;
   rewrite eqxx ?orbT.
Qed.

(* Rajouter deux cycles (i, k) et (j, p k)                                    *)

Definition unswap_node n (p : 'S_n) i j k :=
    (p * tperm i (p k) * tperm j k * tperm k (p k))%g.

Lemma unswap_nodeL n (p : 'S_n) i j k :
  p i = i -> p j = j ->  p k != k -> unswap_node p i j k i = k.
Proof.
move=> piEi pjEj pkDk.
rewrite !permM piEi tpermL [tperm _ _ (p k)]tpermD ?tpermR 1?eq_sym //.
by apply: contra pkDk; rewrite -pjEj=> /eqP /perm_inj->; rewrite pjEj.
Qed.

Lemma unswap_nodeR n (p : 'S_n) i j k :
  i != j -> p j = j ->  p k != k -> unswap_node p i j k j = p k.
Proof.
move=> iDj pjEj pkDk.
rewrite !permM pjEj [tperm _ _ j]tpermD ?(tpermL, tpermR) //.
by apply: contra pkDk; rewrite -pjEj=> /eqP /perm_inj->; rewrite pjEj.
Qed.

Lemma unswap_nodeM n (p : 'S_n) i j k :
  i != j -> p i = i ->  p j = j ->  p k != k -> unswap_node p i j k k = i.
Proof.
move=> iDj piEi pjEj pkDk.
have iDk : i != k by apply: contra pkDk => /eqP<-; apply/eqP.
rewrite !permM tpermR !tpermD // eq_sym //.
by apply/eqP; rewrite -piEi => /perm_inj; have /eqP := iDk.
Qed.

Lemma unswap_nodeMp n (p : 'S_n) i j k :
  i != j -> p i = i ->  p j = j ->  p k != k ->  p (p k) = k ->
  unswap_node p i j k (p k) = j.
Proof.
move=> iDj piEi pjEj pkDk ppK.
have iDk : i != k by apply: contra pkDk => /eqP<-; apply/eqP.
have kDj : k != j by apply: contra pkDk => /eqP->; apply/eqP.
rewrite !permM ppK [tperm _ _ k]tpermD ?tpermR ?tpermD //.
by apply/eqP; rewrite -pjEj => /perm_inj; have /eqP := kDj.
Qed.

Lemma unswap_nodeD n (p : 'S_n) i j k l :
  p i = i -> p j = j -> p (p k) = k ->
  l \notin [:: i; j; k; p k] -> unswap_node p i j k l = p l.
Proof.
move=> piEi pjEj ppK kIL.
suff : p l \notin [:: i; j; k; p k].
  rewrite !inE !negb_or => /and4P[plDi plDj plDk plDpk].
  by rewrite !permM !tpermD // eq_sym.
rewrite -{1}piEi -{1}pjEj -{1}ppK.
by apply: contra kIL; rewrite !inE => /or4P[] /eqP /perm_inj ->;
   rewrite eqxx ?orbT.
Qed.

Lemma swap_nodeK n (p : 'S_n) i j :
  i != j -> p i != i ->  p (p i) = i -> p j != j -> p (p j) = j ->
  unswap_node (swap_node p i j) i j (p i) = p.
Proof.
move=> iDj piDi ppI pjDj ppJ; apply/permP => k.
move/eqP: (iDj) => iDDj.
have piDpj : p i != p j by apply/eqP=> /perm_inj.
rewrite !permM !ppI ?(tpermL, tpermR).
case: (tpermP _ _ (p i))=> [piEj|/perm_inj iEj| /eqP piDj _] //.
  have->: p j = i by rewrite -piEj.
  rewrite  piEj!(tpermL, tpermR) !tperm1 !perm1.
  by rewrite [tperm j _]tpermC -![tperm i j _]permM tperm2 !perm1.
have pjDi : p j != i by apply: contra piDj => /eqP<-; apply/eqP.
rewrite tpermL.
case: (tpermP _ _ (p k))=> [->|/perm_inj ->|/eqP pkDi /eqP pkDpi].
- rewrite [tperm _ _ (p i)]tpermD // 1?eq_sym // !(tpermL, tpermR).
  by rewrite [tperm _ _ i]tpermD // 1?eq_sym // tpermD.
- rewrite [tperm _ _ i]tpermD // 1?eq_sym //.
  rewrite [tperm _ _ i]tpermD // 1?eq_sym // tpermL.
  rewrite [tperm _ _ (p j)]tpermD // 1?eq_sym ?tpermR //.
case: (tpermP _ _ (p k))=> [->|->|/eqP pkDj /eqP pkDpj].
- rewrite !(tpermL, tpermR) [tperm _ _ (p i)]tpermD // 1?eq_sym //.
  by rewrite tpermR tpermD.
- rewrite [tperm _ _ j]tpermD // 1?eq_sym //.
  by rewrite [tperm _ _ j]tpermD // 1?eq_sym // !tpermL.
by rewrite ![tperm _ _ (p k)]tpermD // 1?eq_sym.
Qed.

Lemma unswap_nodeK n (p : 'S_n) i j k:
  i != j -> p i = i -> p j = j -> p k != k -> p (p k) = k ->
  swap_node (unswap_node p i j k) i j = p.
Proof.
move=> iDj piEi pjEj pkDk ppK; apply/permP => l.
have kDj : k != j by  apply: contra pkDk => /eqP->; apply/eqP.
have kDi : k != i by  apply: contra pkDk => /eqP->; apply/eqP.
have pkDj : p k != j by apply: contra kDj; rewrite -{1}pjEj=> /eqP /perm_inj->.
have pkDi : p k != i by apply: contra kDi; rewrite -{1}piEi=> /eqP /perm_inj->.
move /eqP : (pkDk) => pkDDk.
rewrite /unswap_node /swap_node !permM piEi pjEj !(tpermL, tpermR).
rewrite [tperm _ _ (p k)]tpermD // 1?eq_sym //.
rewrite !(tpermL, tpermR) [tperm _ _ j]tpermD // !(tpermL, tpermR).
case: (tpermP _ _ (p l))=>[->|->|/eqP plDi /eqP plDpk].
- rewrite [tperm _ _ (p k)]tpermD // 1?eq_sym // !tpermR.
  by rewrite ![tperm _ _ i]tpermD // 1?eq_sym.
- rewrite 2?[tperm _ _ i]tpermD // 1?eq_sym // tpermL.
  by rewrite [tperm _ _ k]tpermD // 1?eq_sym // tpermL.
case: (tpermP _ _ (p l))=>[->|->|/eqP plDj /eqP plDk].
- by rewrite tpermL [tperm _ _ (p k)]tpermD // 1?eq_sym // tpermR tpermD.
- by rewrite 2?[tperm _ _ j]tpermD // 1?eq_sym // tpermL tpermR.
by rewrite ![tperm _ _ (p l)]tpermD // 1?eq_sym.
Qed.

(* Ajouter les deux cycles (i, t.2) et (i + 1, p t.2))                        *)

Definition pI2S m (i : 'I_m.+2) (t : 'S_m.+2 * 'I_m.+2) : 'S_m.+2 :=
  unswap_node t.1 (i + 1)%R i t.2.

(* Enlever les deux cycles (i, p i) et (i + 1, p (i + 1))                     *)

Definition S2pI m (i : 'I_m.+2) (p : 'S_m.+2) : 'S_m.+2 * 'I_m.+2 :=
  (swap_node p (i + 1)%R i, p (i + 1)%R).

(* Version de is_node paramétré pour permettre une preuve par induction       *)

Definition is_nodeL m k :=
  [set p | 
     [forall i : 'I_m, if i < k.*2 then ((p : 'S_m) (p i) == i) && (p i != i)
                       else p i == i]].
Notation " 'N[ n , k ] " := (@is_nodeL n k).

Lemma is_nodeLE n : 'N[n.*2,n] = 'N[n.*2].
Proof.
apply/setP=> p; rewrite !inE.
by apply/forallP/forallP=> H x; have := H x; rewrite ltn_ord.
Qed.

Lemma PPN n k p i : p \in 'N[n, k] -> p (p i) = i.
Proof.
rewrite inE => /forallP/(_ i); case: (_ < _)=> [/andP[/eqP] //|/eqP piEi].
by rewrite piEi.
Qed.

Lemma PDN n k p (i : 'I_n) : p \in 'N[n, k] -> i < k.*2 -> p i != i.
Proof. by rewrite inE => /forallP/(_ i); case: (_ <_)=> [/andP[_] //|]. Qed.

Lemma PEN n k p (i : 'I_n) : p \in 'N[n, k] -> k.*2 <= i -> p i = i.
Proof. by rewrite inE => /forallP/(_ i); case: leqP => // _ /eqP. Qed.

Lemma PLN n k p (i : 'I_n) : p \in'N[n, k] -> i < k.*2 -> p i < k.*2.
Proof.
move=> pIP iLk2.
case: leqP (PPN i pIP) (@PEN _ _ _ (p i) pIP) (PDN pIP iLk2) => //.
by move=> _ -> <- //; rewrite eqxx.
Qed.

Lemma ISE n (i: 'I_n.+2) : i <= n -> (i + 1)%R = i.+1 :> nat.
Proof.
move=> iLn.
suff: (i + 1 %% n.+2) %% n.+2 = i.+1 by [].
by rewrite !modn_small ?addn1.
Qed.

Lemma ISDE n (i: 'I_n.+2) : i <= n -> (i + 1)%R != i.
Proof.
move=> iLn.
suff: i.+1 != i by rewrite -ISE.
by have := leqnn i; rewrite leqNgt; apply: contra => /eqP{2}<-.
Qed.

(* Sp2I est bijectif                                                          *)

Lemma S2pIK n k (i : 'I_n.+2) : 
  i < k.*2.+1 <= n.+1 ->  {in  'N[n.+2, k.+1],  (pI2S i)  \o (S2pI i) =1 id}.
Proof.
move=> /andP[iLk kLn] p pIN; rewrite /pI2S /S2pI /=.
have iLn : i <= n by rewrite -ltnS (leq_trans iLk).
by rewrite swap_nodeK ?(PPN _ pIN, PDN pIN, ISE, ISDE) // ltnW.
Qed.

(* pI2S est bijectif                                                          *)

Lemma pI2SK n k (i : 'I_n.+2) : 
   k.*2 = i -> i <= n -> 
  {in setX 'N[n.+2, k] (lordinal n.+2 k.*2.+1), (S2pI i) \o (pI2S i) =1 id}.
Proof.
move=> k2Ei iLn [p j]; rewrite inE /= => /andP[pIP jIL].
have piEi : p i = i by apply: PEN pIP _; rewrite -k2Ei.
have psiEsi : p (i + 1)%R  = (i + 1)%R
   by apply: PEN pIP _; rewrite ISE // -k2Ei.
rewrite /S2pI /pI2S /=.
case: (boolP (j == i)) => [/eqP->|jDi].
  rewrite /unswap_node /swap_node !permM piEi tperm1 !mulg1 !perm1 psiEsi.
  by rewrite !(tpermL,tpermR) -!mulgA !(tperm2,mulg1).
case: (boolP (j == i)) => [/eqP->|jDk2].
  rewrite /unswap_node /swap_node !permM piEi tperm1 !mulg1 !perm1 psiEsi.
  by rewrite !(tpermL,tpermR) -!mulgA !(tperm2,mulg1).
have pjDj : p j != j.
  move: jIL; rewrite inE; rewrite ltnS leq_eqVlt k2Ei.
  have/negPf-> /= : j != i :> nat.
   by apply: contra jDi => HH; apply/eqP/val_eqP.
  by rewrite -k2Ei => /(PDN pIP).
rewrite unswap_nodeL // unswap_nodeK ?(unswap_nodeL, ISDE) //.
by apply: PPN pIP.
Qed.

(* L'image de S2pI (k décroit)                                                *)

Lemma subset_S2pI n k (i : 'I_n.+2) :
  k.*2 = i -> i <= n ->
 [set S2pI i p | p in 'N[n.+2, k.+1]] 
         \subset setX 'N[n.+2, k] (lordinal n.+2 k.*2.+1).
Proof.
move=> k2Ei iLn.
apply/subsetP=> t /imsetP[/= p pIP ->].
have sIDi : (i + 1)%R != i by apply: ISDE. 
have siLk2 : (i + 1)%R < k.+1.*2 by rewrite ISE // -k2Ei.
have iLk2 : i < k.+1.*2 by rewrite -k2Ei ltnW.
have ppSi : p (p (i + 1)%R) = (i + 1)%R by apply: PPN pIP.
have ppI : p (p i) = i by apply: PPN pIP.
have psiDsi : p (i + 1)%R != (i + 1)%R by apply: PDN pIP _.
have piDi : p i != i by apply: PDN pIP _.
rewrite !inE /=; apply/andP; split; last first.
  have :=  PLN pIP siLk2.
  rewrite leq_eqVlt doubleS eqSS ltnS k2Ei -ISE //.
  suff /negPf-> : p (i + 1)%R != (i + 1)%R :> nat by [].
  by apply: contra psiDsi => HH; apply/eqP/val_eqP.
apply/forallP=> j.
case: (boolP (j \in [:: (i + 1)%R; i; p (i + 1)%R; p i])) => [|jNIL]; last first.
  rewrite (swap_nodeD _ _ jNIL) // swap_nodeD //; last first.
    rewrite -{1}ppSi -{2}ppI; apply: contra jNIL.
    by rewrite !inE => /or4P[] /eqP/perm_inj->; rewrite eqxx ?orbT.
  rewrite inE in pIP; have /forallP/(_ j) := pIP.
  rewrite leq_eqVlt doubleS eqSS leq_eqVlt !ltnS !eqSS k2Ei -ISE //.
  have /negPf->: j != (i + 1)%R :> nat.
    rewrite !inE !negb_or in jNIL; have /and4P[HH _ _ _] := jNIL.
    by apply: contra HH => HH1; apply/eqP/val_eqP.
  suff /negPf->: j != i :> nat by [].
  rewrite !inE !negb_or in jNIL; have /and4P[_ HH _ _] := jNIL.
  by apply: contra HH => HH1; apply/eqP/val_eqP.
rewrite !inE => /or4P[] /eqP->.
- by rewrite ltnNge ISE // -k2Ei leqnSn /= swap_nodeL.
- by rewrite k2Ei ltnn swap_nodeR.
- case: (boolP (p (i + 1)%R == i)) => [/eqP->|psiDi].
    by rewrite k2Ei ltnn swap_nodeR.
  rewrite swap_nodeLp // ?swap_nodeRp //.
  have :=  PLN pIP siLk2.
  rewrite leq_eqVlt doubleS eqSS k2Ei -ISE // ltnS.
  have /negPf-> : p (i + 1)%R != (i + 1)%R :> nat by [].
  rewrite leq_eqVlt ISE // eqSS ltnS.
  have /negPf-> : p (i + 1)%R != i :> nat by [].
  move=> /=->; rewrite eqxx; apply/eqP=> /perm_inj.
  by apply/eqP; rewrite eq_sym.
case: (boolP (p i == (i + 1)%R)) => [/eqP->|piDsi].
  by rewrite ltnNge k2Ei ISE // ltnW //= swap_nodeL.
have psiDi : p (i + 1)%R != i.
  by apply: contra piDsi => /eqP{1}<-; apply/eqP.
rewrite swap_nodeRp // ?swap_nodeLp //.
have :=  PLN pIP iLk2.
rewrite leq_eqVlt doubleS eqSS k2Ei -ISE // ltnS.
have /negPf-> : p i != (i + 1)%R :> nat by [].
rewrite leq_eqVlt ISE // eqSS ltnS.
have /negPf-> : p  i != i :> nat by [].
by move=> /=->; rewrite eqxx; apply/eqP=> /perm_inj; apply/eqP.
Qed.

(* L'image de p2SI (k croit)                                                  *)

Lemma subset_pI2S n k (i : 'I_n.+2) :
  k.*2 = i -> i <= n ->  
 [set pI2S i t | t in setX 'N[n.+2, k] (lordinal n.+2 k.*2.+1)]  
         \subset'N[n.+2, k.+1].
Proof.
move=> k2Ei iLn.
apply/subsetP=> t /imsetP[[p j]]; rewrite inE /= => /andP[pIP jII] -> {t}.
have sIDi : (i + 1)%R != i by apply: ISDE. 
have siLk2 : (i + 1)%R < k.+1.*2 by rewrite ISE // -k2Ei.
have iLk2 : i < k.+1.*2 by rewrite -k2Ei ltnW.
have siDj : (i + 1)%R != j.
  by move: jII; rewrite inE k2Ei ltnNge; apply: contra=> /eqP<-; rewrite ISE.
have piEi : p i = i by apply: PEN pIP _; rewrite k2Ei.
have psiEsi : p (i + 1)%R = (i + 1)%R  by apply: PEN pIP _; rewrite k2Ei ISE.
have ppJ : p  (p j) = j by apply: PPN pIP.
rewrite inE /pI2S /=; apply/forallP=> i1.
case: (boolP (i1 \in [:: (i + 1)%R; i; j; p j])) => [|i1NIL]; last first.
  rewrite [unswap_node _ _ _ _ i1]unswap_nodeD // unswap_nodeD //; last first.
    rewrite -psiEsi -{2}piEi -{1}ppJ; apply: contra i1NIL.
    by rewrite !inE => /or4P[] /eqP/perm_inj->; rewrite eqxx ?orbT.
  rewrite !inE !negb_or in i1NIL.
  have /and4P[/eqP/val_eqP i1Dsi /eqP/val_eqP /= i1Di _ _] := i1NIL.
  rewrite inE in pIP; have /forallP/(_ i1) := pIP.
  suff ->: i1 < k.*2 = (i1 < (k.+1).*2) by [].
  rewrite doubleS ltnS [X in _ = X]leq_eqVlt k2Ei // -[i.+1]ISE //.
  by rewrite (negPf i1Dsi) [X in _ = X]leq_eqVlt ISE // eqSS (negPf i1Di).
case: (boolP (j == i)) => [/eqP-> i1IL |jDi].
  have: i1 \in [:: i; (i + 1)%R].
    rewrite !inE in i1IL |- *.
    by have /or4P[] := i1IL => /eqP-> //; rewrite ?piEi eqxx ?orbT.
  by rewrite !inE => /orP[] /eqP->; 
       rewrite doubleS k2Ei // ?ISE // ?leqnn 1?ltnW //
               !(permM, piEi, psiEsi, tperm1, perm1, tpermL, tpermR)
               eqxx // eq_sym.
move: (jII); rewrite inE; rewrite ltnS leq_eqVlt k2Ei.
have/negPf-> /= : j != i :> nat.
  by apply: contra jDi => HH; apply/eqP/val_eqP.
move=> jLi.
have pjDj : p j != j by apply: PDN pIP _; rewrite k2Ei.
have pjDi : p j != i. 
  by apply: contra jDi; rewrite -{2}ppJ => /eqP->; apply/eqP.
rewrite doubleS !inE => /or4P[] /eqP->;
   rewrite ?(unswap_nodeL, unswap_nodeR, unswap_nodeM, unswap_nodeMp) //.
- by rewrite ISE // k2Ei leqnn eqxx eq_sym.
- by rewrite k2Ei // ltnW // eqxx.
- by rewrite (leq_trans jLi) ?eqxx // k2Ei ltnW.
case: leqP=> [jLpj|]; last by rewrite eqxx eq_sym pjDi.
case/eqP: pjDj; rewrite -{2}ppJ; apply/sym_equal.
by apply: PEN pIP (leq_trans _ jLpj); rewrite ltnW // ltnW.
Qed.

(* Cardinalité des permutations dont tous les cycles sont de longueur 2       *)
(* On fait la preuve par induction en enlevant deux cycles à la fois          *)

Lemma card_is_node n : #|'N[n.+1.*2]| = \prod_(i < n.+1) i.*2.+1.
Proof.
rewrite -is_nodeLE.
suff L k : k <= n.+1 -> #|'N[ (n.+1).*2, k]| = \prod_(i < k) i.*2.+1.
  by rewrite L //.
elim: k => [_ |k IH].
  rewrite big_ord0; apply/eqP/cards1P; exists 1%g.
  apply/setP=> p; rewrite !inE.
  apply/forallP/eqP=> [Hf | -> x]; last by rewrite perm1.
  by apply/permP=> i; rewrite (eqP (Hf i)) perm1.
rewrite big_ord_recr /= ltnS => kLn; rewrite -IH ?(leq_trans kLn) //.
have k2Ln2 : k.*2 <= n.*2 by rewrite leq_double.
have sk2LSn2 : k.*2.+1 <= n.+1.*2 by rewrite ltnW.
rewrite -[k.*2.+1](card_lordinal  sk2LSn2) -cardsX /=.
pose i := Ordinal sk2LSn2.
have k2Ei : k.*2 = i by [].
apply/eqP; rewrite eqn_leq; apply/andP; split.
  apply: leq_trans (subset_leq_card (subset_S2pI k2Ei _)) => //.
  rewrite card_in_imset //= => p1 p2 p1I p2I p1Ep2.
  have/S2pIK/(_ p1)<-//= : i < k.*2.+1 <= n.*2.+1 by rewrite leqnn -ltnS.
  have/S2pIK/(_ p2)<-//= : i < k.*2.+1 <= n.*2.+1 by rewrite leqnn -ltnS.
  by rewrite p1Ep2.
apply: leq_trans (subset_leq_card (subset_pI2S k2Ei _)) => //.
rewrite card_in_imset //= => p1 p2 p1I p2I p1Ep2.
by rewrite -[p1](pI2SK k2Ei) //= -[p2](pI2SK k2Ei) //= p1Ep2.
Qed.

(* Cardinal des configurations                                                *)

Lemma card_cvalid n : #|'N2[n.+1.*2]| = ((\prod_(i < n.+1) i.*2.+1) ^ 2)%nat.
Proof. by rewrite cardsX card_is_node. Qed.

Fact card_cvalid6 : #|'N2[6]| = (15 ^ 2)%nat.
Proof. 
by rewrite (card_cvalid 2) -(big_mkord xpredT (fun i =>i.*2.+1)) unlock.
Qed.

(******************************************************************************)
(*                                                                            *)
(*                     NOMBRE DE CONFIGURATIONS A 1 CYCLE                     *)
(*                                                                            *)
(******************************************************************************)

(* Promouvoir une fonction en une permutation                                 *)

Definition perm_of n (f : {ffun 'I_n.+1 -> 'I_n.+1}) : 'S_n.+1 :=
  odflt 1%g [pick p | f == (pval p)].

Lemma perm_ofE n (f:  {ffun 'I_n.+1 -> 'I_n.+1}) : injective f -> perm_of f =1 f.
Proof.
move=> /injectiveP If i.
pose p1 := Perm If.
rewrite unlock /perm_of; case: pickP => [[f1 If1] /= /eqP-> //= |].
by move/(_ p1); rewrite eqxx.
Qed.

Lemma oddI_pre n (i : 'I_n.+2) : ~~ odd n -> odd (i - 1)%R = ~~ odd i.
Proof.
case: i => [[_| i iLn] On] /=.
  by rewrite !modn_mod !modn_small //= negbK (negPf On).
rewrite (modn_small (_ : n.+2 - 1 < _)) // addSnnS modnDr modn_small ?negbK //.
by rewrite ltnW.
Qed.

Lemma oddIS n (i : 'I_n.+2) : ~~ odd n -> odd (i + 1)%R = ~~ odd i.
Proof.
case: i => [i] /=.
rewrite leq_eqVlt => /orP[|iSLn2]; last by rewrite !modn_small?addn1.
by rewrite eqSS => /eqP->; rewrite addn1 modnn /= => ->.
Qed.

(* Traduire une configuration en une permutation en utilisant la liste S2l    *)

Definition c2p n (c : config  n.+1.*2) := 
  perm_of ([ffun n : 'I_ _  => nth 0%R (c2l c) n]).

(* Récupération de la première permutation de la configuration                *)

Definition fun_permL n (p : 'S_n.+2) :=
 [ffun i : 'I_n.+2 =>
    let k := p^-1%g i in 
    if odd k then p (k - 1)%R else p (k + 1)%R].

Lemma fun_permLK n (p : 'S_n.+2) i :
  ~~ odd n -> fun_permL p (fun_permL p i) = i.
Proof.
move=> On; rewrite /fun_permL !ffunE /=.
by have [] := boolP (odd ((p^-1)%g i)); 
   rewrite -!permM mulgV perm1 !(oddIS, oddI_pre) // => -> /=;
   rewrite (subrK, addrK) -permM mulVg perm1.
Qed.

Lemma injective_permL n (p : 'S_n.+2) : ~~ odd n -> injective (fun_permL p).
Proof.
move=> En i j piEpj.
by rewrite -[i](fun_permLK p _ En) -[j](fun_permLK p _ En) piEpj.
Qed.

Lemma fun_permLF n (p : 'S_n.+2) i : ~~ odd n -> fun_permL p i != i.
Proof.
move=> On; rewrite /fun_permL !ffunE /=.
have ppI : p ((p^-1)%g i) = i by rewrite -permM mulVg perm1.
by have [Opi|Epi] := boolP (odd ((p^-1)%g i)); 
   rewrite -{2}ppI; apply/eqP => /perm_inj/eqP; apply/idP;
   rewrite eq_sym -subr_eq0 opprD addrA (addrN, addNr) 
           sub0r ?(opprK, signr_eq0 _ 1).
Qed.

(* Récupération de la deuxième permutation de la configuration                *)

Definition fun_permR n (p : 'S_n.+2) :=
  [ffun i : 'I_n.+2 =>
    let k := p^-1%g i in 
    if odd k then p (k + 1)%R else p (k - 1)%R].

Lemma fun_permRK n (p : 'S_n.+2) i : 
  ~~ odd n -> fun_permR p (fun_permR p i) = i.
Proof.
move=> On; rewrite /fun_permR /= !ffunE.
by have [] := boolP (odd ((p^-1)%g i)); 
   rewrite -!permM mulgV perm1 !(oddIS, oddI_pre) // => -> /=;
   rewrite (subrK, addrK) -permM mulVg perm1.
Qed.

Lemma injective_permR n (p : 'S_n.+2) : ~~ odd n -> injective (fun_permR p).
Proof.
move=> En i j piEpj.
by rewrite -[i](fun_permRK p _ En) -[j](fun_permRK p _ En) piEpj.
Qed.

Lemma fun_permRF n (p : 'S_n.+2) i : ~~ odd n -> fun_permR p i != i.
Proof.
move=> On; rewrite /fun_permR !ffunE /=.
have ppI : p ((p^-1)%g i) = i by rewrite -permM mulVg perm1.
by have [Opi|Epi] := boolP (odd ((p^-1)%g i)); 
   rewrite -{2}ppI; apply/eqP => /perm_inj/eqP; apply/idP;
   rewrite eq_sym -subr_eq0 opprD addrA (addrN, addNr) 
           sub0r ?(opprK, signr_eq0 _ 1).
Qed.

(* Traduire une permutation telle que p 0 = 0 en une configuration            *)

Definition p2c n (p: 'S_n.+2) : config n.+2 :=
  (perm_of (fun_permL p), perm_of (fun_permR p)).

(* Permutation qui valent 0 en 0                                              *)

Definition perm_fix0 n : pred 'S_n.+1 := perm_on [set~ ord0].
Notation " 'F[ n ] " := (@perm_fix0 n).

Lemma perm_fix0P n p : p \in @perm_fix0 n = (p 0%R == 0%R).
Proof.
apply/subsetP/eqP=> [/(_ 0%R)| p0E0 i]; rewrite !inE; last first.
  by apply: contra => /eqP->; apply/eqP.
by case: (_ =P _)=> //; rewrite eqxx => _ /(_ is_true_true).
Qed.

Lemma c2l_codom n (p: 'S_n.+1.*2) : p 0%R = 0%R -> c2l (p2c p) = codom p.
Proof.
move=> p0E0; apply: (@eq_from_nth _ 0%R) => [|i].
  by rewrite size_follow size_codom card_ord.
have p10E0 : (p^-1)%g 0%R = 0%R by rewrite -[0%R]p0E0 -permM mulgV perm1.
rewrite size_follow => iLn.
pose j := Ordinal iLn.
rewrite (nth_map 0%R) ?size_enum_ord //= (@nth_ord_enum _ ord0 j) /=.
suff : forall k (i j : 'I_ n.+1.*2), 
   ~ odd ((p^-1)%g j) -> i < k.*2 -> 
         nth 0%R (follow k (p2c p) j) i = p (i + p^-1%g j)%R.
  by move=> /(_  n.+1 (Ordinal iLn) 0%R) => ->; rewrite // p10E0 ?addr0.
elim=> //=  {i iLn j}k IH [[|[|i]] Pi] j /negP Oj iLK /=.
- have->: Ordinal Pi = 0%R by apply/eqP.
  by rewrite add0r -permM mulVg perm1.
- have->: Ordinal Pi = 1%R by apply/eqP.
  rewrite  perm_ofE; last by apply: injective_permL; rewrite odd_double.
  by rewrite /fun_permL !ffunE (negPf Oj) addrC.
rewrite  perm_ofE; last by apply: injective_permR; rewrite odd_double.
rewrite  perm_ofE; last by apply: injective_permL; rewrite odd_double.
rewrite /= in iLK.
have PPi : i < (n.+1).*2.
  by apply: leq_trans Pi; rewrite ltnS ltnW //.
rewrite (IH (Ordinal PPi)) //=; last first.
  rewrite /fun_permL !ffunE (negPf Oj) /fun_permR -!permM mulgV perm1 oddIS ?odd_double //.
  by rewrite Oj -!permM mulgV perm1 !oddIS ?odd_double // !negbK // (negPf Oj).
rewrite /fun_permL !ffunE (negPf Oj) /fun_permR -!permM mulgV perm1 oddIS ?odd_double //.
rewrite Oj -!permM mulgV perm1.
suff->: Ordinal Pi = (Ordinal PPi + 1 + 1)%R.
  by congr (p _); rewrite -!addrA; congr (_ + _)%R; rewrite addrC !addrA.
by apply/val_eqP; rewrite [X in _ == X]ISE // ISE //= -2!ltnS ltnW.
Qed.

Lemma card_perm_fix0 n : #|'F[n]| = n`!.
Proof. by rewrite /perm_fix0 card_perm cardsC1 card_ord. Qed.

Lemma imp2c n: [set p2c p |  p  in 'F[n.*2.+1]] \subset 'N2[(n.+1).*2] :&: 'O[n].
Proof. 
apply/subsetP=> t /imsetP[p]; rewrite inE perm_fix0P => /eqP p0E0 ->.
have /perm_ofE pLE : injective (fun_permL p) => [j k fpE|].
  by rewrite -[j](fun_permLK p) ?fpE ?fun_permLK ?odd_double.
have /perm_ofE pRE : injective (fun_permR p) => [j k fpE|].
  by rewrite -[j](fun_permRK p) ?fpE ?fun_permRK ?odd_double.
rewrite /p2c inE /= -andbA; apply/and3P; split.
- rewrite inE; apply/forallP=> i.
  by rewrite !(pLE, perm_ofE, fun_permLK, fun_permLF, eqxx, odd_double).
- rewrite inE; apply/forallP=> i.
  by rewrite !(pRE, perm_ofE, fun_permRK, fun_permRF, eqxx, odd_double).
by rewrite inE c2l_codom; have /injectiveP := @perm_inj _ p.
Qed.

Lemma imc2p n: [set c2p c |  c  in 'N2[(n.+1).*2] :&: 'O[n]] \subset 'F[n.*2.+1].
Proof.
apply/subsetP=> /= p /imsetP[c]; rewrite inE => /andP[tIN tIO] ->.
rewrite perm_fix0P /c2p perm_ofE /c2l ?ffunE //.
apply/injectiveP; rewrite /injectiveb /dinjectiveb.
set F := [ffun _ => _].
suff ->: [seq F i | i <- enum 'I_n.+1.*2] = follow n.+1 c 0%R.
  by rewrite inE /c2l in tIO.
apply: (@eq_from_nth _ 0%R); first by rewrite size_map size_follow size_enum_ord.
move=> i Hi; rewrite size_map size_enum_ord in Hi.
by rewrite (nth_map 0%R) ?ffunE ?nth_enum_ord // size_enum_ord.
Qed.

Lemma p2SK n : {in  'F[n.*2.+1], (@c2p _) \o (@p2c n.*2) =1 id}.
Proof.
move=> p; rewrite perm_fix0P => /eqP p0E0 /=.
apply/permP=> i.
rewrite /p2c /c2p perm_ofE ?ffunE.
  by rewrite c2l_codom // (nth_map 0%R) ?size_enum_ord // nth_ord_enum.
move=> i1 j1 /= /eqP.
have i1Ls: i1 < size (c2l (p2c p)) by rewrite size_follow.
have j1Ls: j1 < size (c2l (p2c p)) by rewrite size_follow.
have US2l : uniq (c2l (p2c p)).
  by rewrite c2l_codom //; apply/injectiveP/perm_inj.
by rewrite !ffunE (nth_uniq 0%R i1Ls j1Ls US2l) => HH; apply/val_eqP.
Qed.

Lemma I_preE n (i: 'I_n.+2) : 0 < i -> (i - 1)%R = i.-1 :> nat.
Proof.
case: i => [[|i]] //= iLn _.
rewrite subSS subn0 [n.+1 %% _]modn_small // addSnnS modnDr.
by rewrite modn_small // ltnW.
Qed.

Lemma c2lLE n (c: config n.+1.*2) (i : 'I_ n.+1.*2) (p := c.1) :
  ((forall i, p (p i) = i) ->
     p (c2l c)`_i = (c2l c)`_(if odd i then (i - 1) else (i + 1)))%R.
Proof.
move=> ppI.
suff /(_ n.+1 i 0%R (ltn_ord _)) : forall k (i j : 'I_n.+1.*2),  i < k.*2 -> 
        (p (follow k c j)`_i = (follow k c j)`_
            (if odd i then (i - 1) else (i + 1)))%R by [].
elim=> // {i}k IH [[|[|i]] Pi] j iLk.
- by  have->: Ordinal Pi = 0%R by apply/eqP.
- have->: Ordinal Pi = 1%R by apply/eqP.
  by rewrite subrr /= ppI.
have Pii : i < (n.+1).*2  by rewrite ltnS ltnW // ltnW.
have i1Lk : i < k.*2 by rewrite -2!ltnS.
have := IH (Ordinal Pii) (c.2 (c.1 j)) i1Lk.
have->: Ordinal Pi = i.+2 :> nat by []; have->: Ordinal Pii = i :> nat by [].
rewrite [odd _.+1]/= negbK [follow _.+1 _ _]/=.
case: (boolP (odd i))=> [Op|Ep].
  by rewrite !I_preE=> [->//=|//=|/=]; case: (i : nat) Op.
rewrite !ISE=> [->//|/=|/=]; last by rewrite -ltnS ltnW.
have: odd i.+3 by rewrite /= negbK.
by move: (Pi); rewrite leq_eqVlt => /orP[/eqP->|]; rewrite ?odd_double.
Qed.


Lemma c2lRE n (c: config n.+1.*2) (i : 'I_ n.+1.*2) (p := c.2) :
  ((forall i, p (p i) = i) -> (forall i, p i != i) -> uniq (c2l c) ->
     p (c2l c)`_i = (c2l c)`_(if odd i then (i + 1) else (i - 1)))%R.
Proof.
move=> ppI piDi Uc2l.
have m1E : ((-1)%R : 'I_n.+1.*2) = n.*2.+1 :> nat.
  by rewrite /= subn1 modn_small.
have Hf : forall (i : 'I_n.+1.*2), i != 0%R -> i != (-1)%R -> 
        (p (c2l c)`_i = (c2l c)`_(if odd i then (i + 1) else (i - 1)))%R.
  suff Pf: forall k (i j : 'I_n.+1.*2), 0 < i < n.*2.+1 -> i.+1 < k.*2 -> 
        (p (follow k c j)`_i = (follow k c j)`_
            (if odd i then (i + 1) else (i - 1)))%R.
    move=> i1 i1D0 i1Dm1.
    have P2 : i1.+1 < n.+1.*2.
      rewrite {2}doubleS ltnS.
      have := ltn_ord i1; rewrite leq_eqVlt eqSS ltnS.
      have/negPf->//: i1 != n.*2.+1 :> nat.
      by rewrite -m1E; apply: contra i1Dm1=> HH; apply/eqP/val_eqP.
    have P1 : 0 < i1 < n.*2.+1.
      have: i1 != 0 :> nat by apply: contra i1D0 => HH; apply/eqP/val_eqP.
      by case: (i1 : nat) P2.
    by have := Pf n.+1 i1 0%R P1 P2.
  elim=> // {i}k IH [[|[|i]] Pi] j iLn iLk //.
    have->: Ordinal Pi = 1%R by apply/eqP.
    by rewrite ISE //=; case: (k) iLk.
  have Pii : i < (n.+1).*2  by rewrite ltnS ltnW // ltnW.
  have->: Ordinal Pi = i.+2 :> nat by [].
  case: (leqP i 0)=> [iZ|iPos].
    by move: iLk; rewrite fun_if I_preE //=; case: (i : nat) iZ; case: (k) => /=.
  have P1 : 0 < i < n.*2.+1 by rewrite iPos -ltnS (leq_trans _ Pi).
  have P2 : i.+1 < k.*2 by rewrite -2!ltnS.
  have := IH (Ordinal Pii) (c.2 (c.1 j)) P1 P2.
  have->: Ordinal Pii = i :> nat by [].
  rewrite [odd _.+1]/= negbK [follow _.+1 _ _]/=.
  case: (boolP (odd i))=> [Op|Ep]; last first.
    by rewrite !I_preE=> [->//=|//=|/=]; case: (i : nat) iPos.
  rewrite !ISE=> [->//|/=|/=]; last by rewrite -ltnS ltnW.
  have: ~~ odd i.+3 by rewrite /= !negbK.
  by move: (Pi); rewrite leq_eqVlt => /orP[/eqP->|]; rewrite ?odd_double.
suff Hp : p ((c2l c)`_0)%R = ((c2l c)`_n.*2.+1)%R.
  case: (boolP (i == 0%R))=> [/eqP->|iE0]; first by rewrite sub0r m1E.
  case: (boolP (i == -1)%R)=> [/eqP->|iDm1].
    by rewrite m1E -Hp ppI [odd _]/= odd_double addNr.
  by have := Hf _ iE0 iDm1.
pose F : {ffun 'I_n.+1.*2 -> 'I_(n.+1).*2} := 
    [ffun i : 'I_n.+1.*2 => ((c2l c)`_i)%R].
have injF : injectiveb F.
  rewrite /injectiveb /dinjectiveb.
  suff->: [seq (F n) | n <- enum 'I_n.+1.*2] = c2l c by [].
  apply: (@eq_from_nth _ 0%R)=> [|i1]; rewrite size_map size_enum_ord //.
    by rewrite size_follow.
  by move=> Hi1; rewrite (nth_map 0%R) ?size_enum_ord // /F ffunE nth_enum_ord.
have PFE (k : 'I_n.+1.*2) : perm_of F k = ((c2l c)`_k)%R .
  by rewrite perm_ofE ?ffunE //; apply/injectiveP.
pose u : 'I_n.+1.*2 := (perm_of F)^-1%g (p ((c2l c)`_0)%R).
case: (boolP (u == (-1)%R))=> [/eqP uEm1| uDm1].
  have: perm_of F u = perm_of F (-1)%R by rewrite uEm1.
  by rewrite -permM mulVg perm1 PFE m1E.
case: (boolP (u == 0%R))=> [/eqP uE0 | uD0].
  have: perm_of F u = perm_of F 0%R by rewrite uE0.
  rewrite -permM mulVg perm1 PFE //= => /eqP.
  by rewrite (negPf (piDi 0%R)).
have := Hf u uD0 uDm1.
rewrite -PFE -[perm_of F _]permM mulVg perm1 ppI.
case: (boolP (odd u))=> [Ou|Eu].
  rewrite -(PFE 0%R) -(PFE (u + 1)%R) => /perm_inj U1E0.
  by have /eqP[] := uDm1; rewrite -[(-1)%R]add0r U1E0 addrK.
rewrite -(PFE 0%R) -(PFE (u - 1)%R) => /perm_inj Um1E0.
have /negP[] := Eu.
by rewrite -[u]subr0 Um1E0 opprD addrA addrN sub0r opprK.
Qed.

Lemma S2pK n : {in 'N2[n.+1.*2] :&: 'O[n], (@p2c n.*2) \o (@c2p _) =1 id}.
Proof.
move=> [p1 p2]; rewrite 2!inE -andbA => /and3P[/= p1IN p2IN tON] /=.
rewrite /p2c /c2p.
set m := 'I_ _.
set F  := [ffun i :'I_n.+1.*2 => ((c2l (p1, p2))`_i)%R].
have injF : injectiveb F.
  rewrite /injectiveb /dinjectiveb; rewrite inE in tON.
  suff->: [seq (F n) | n <- enum 'I_n.+1.*2] = c2l (p1, p2) by [].
  apply: (@eq_from_nth _ 0%R)=> [|i]; rewrite size_map size_enum_ord //.
    by rewrite size_follow.
  by move=> Hi; rewrite (nth_map 0%R) ?size_enum_ord // /F ffunE nth_enum_ord.
have PFE k : perm_of F k = ((c2l (p1, p2))`_k)%R .
  by rewrite perm_ofE ?ffunE //; apply/injectiveP.
congr (_, _); apply/permP=> i.
  rewrite perm_ofE; last by apply: injective_permL; rewrite odd_double.
  rewrite /fun_permL ffunE.
  move: (@c2lLE _ (p1, p2) (((perm_of F)^-1)%g i)).
  by rewrite !PFE; case: odd=> <- //=; try (by move=> i1; apply: is_nodeK p1IN);
     congr (p1 _); rewrite -PFE -permM mulVg perm1.
rewrite perm_ofE; last by apply: injective_permR; rewrite odd_double.
rewrite /fun_permR ffunE.
rewrite inE in tON.
move: (@c2lRE _ (p1, p2) (((perm_of F)^-1)%g i)).
rewrite !PFE; case: odd=> <- //=; try (by move=> i1; apply: is_nodeK p2IN).
- by congr (p2 _); rewrite -PFE -permM mulVg perm1.
- by move=> i1; apply: is_node_diff p2IN.
- by congr (p2 _); rewrite -PFE -permM mulVg perm1.
move=> i1; apply: is_node_diff p2IN.
Qed.

Lemma card_N2O n : #|'N2[n.+1.*2] :&: 'O[n]| = n.*2.+1 `!.
Proof.
rewrite -card_perm_fix0.
apply/eqP; rewrite eqn_leq; apply/andP; split.
  apply: leq_trans (subset_leq_card (imc2p _)).
  rewrite card_in_imset //= => p1 p2 p1I p2I p1Ep2.
  by rewrite -[p1]S2pK //= p1Ep2 [X in X = _](@S2pK _  p2).
apply: leq_trans (subset_leq_card (imp2c _)).
rewrite card_in_imset //= => p1 p2 p1I p2I p1Ep2.
by rewrite -[p1]p2SK //= p1Ep2 [X in X = _](@p2SK _  p2).
Qed.

(******************************************************************************)
(*                                                                            *)
(*                           PROBABILITÉ                                      *)
(*                                                                            *)
(******************************************************************************)

Open Scope ring_scope.

(* Le rapport entre tous les configurations de noeuds avec un cycle et toutes *)
(* les configurations                                                         *)

Definition Proba n : rat := #|'N2[n.+1.*2] :&: 'O[n]|%:R / #|'N2[n.+1.*2]|%:R.

Lemma ProbaE n : Proba n = n.*2.+1 `!%:R / ((\prod_(i < n.+1) i.*2.+1) ^2)%:R.
Proof. by rewrite /Proba card_N2O card_cvalid. Qed.

Lemma result : Proba 2 = 8%:R / 15%:R.
Proof.
apply: etrans (_ : 8%:R * 15%:R / (15%:R * 15%:R) = _); last first.
  by rewrite invfM mulrA mulfK.
rewrite ProbaE /=.
by rewrite -[(2.*2.+1)`!%:R]/120 !big_ord_recr big_ord0.
Qed.

End Corde.
