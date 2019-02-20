Require Import Cring.
From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory.

Section Cube.

(* Comme Coq ne connait rien en géométrie on doit commencer par définir       *)
(* les notions de base de géométrie                                           *)

(* Le corps des coordonées                                                    *)

Variable R : numFieldType.

(* Pour pouvoir décider les équations sur R                                   *)

Lemma Rsth : Setoid_Theory R (@eq R).
Proof.  by split => [x |x y ->| x y z -> ->]. Qed.

Global Instance Roperators:
  @Ring_ops R 0%R 1%R +%R *%R  (fun x y => x - y)%R -%R (@eq R).

Global Instance Rring: (@Ring _ _ _ _ _ _ _ _ Roperators).
Proof.
by split; [
   exact: Rsth | move=> x y -> t u -> | move=> x y -> t u ->
 | move=> x y -> t u -> | move=> x y -> | exact: add0r 
 | exact: addrC | exact: addrA | exact: mul1r | exact: mulr1
 | exact: mulrA | exact: mulrDl | move=> x y z; exact: mulrDr | idtac
 | exact: addrN 
].
Defined.

Global Instance Rcring: (Cring (Rr:=Rring)).
Proof. exact: mulrC. Defined.

(* Un petit test                                                              *)

Fact test (x y : R) : (x - y) * (x + y) = x * x - y * y.
Proof. cring. Qed.

(******************************************************************************)
(*                          POINT                                             *)
(******************************************************************************)

Inductive point := Point of R & R & R.

(* On a besoin de l'égalité sur les points : p1 == p2                         *)

Definition eq_point p1 p2 :=
 let: Point x1 y1 z1 := p1 in
 let: Point x2 y2 z2 := p2 in [&& x1 == x2, y1 == y2 & z1 == z2].

Lemma eq_pointP : Equality.axiom eq_point.
Proof.
case=> x1 y1 z1 [x2 y2 z2].
apply: (iffP idP)=> [/and3P[/eqP<- /eqP<- /eqP<-]|[<- <- <- //]] //=.
by rewrite !eqxx.
Qed.

Canonical point_eqMixin := EqMixin eq_pointP.
Canonical point_eqType := Eval hnf in EqType point point_eqMixin.


(******************************************************************************)
(*                          LIGNE                                             *)
(******************************************************************************)

(* Définition d'une ligne : deux points distincts *)

Inductive line := Line (p1  p2 : point) of (p1 != p2).

(* x1 / y1, x2 / y2 et z1 / z2 sont proportionnels                           *)

Definition proportional (x1 y1 x2 y2 x3 y3 : R) := 
  [&& x1 * y2 == y1 * x2, x1 * y3 == y1 * x3 & x2 * y3 == y2 * x3].

Lemma proportionalP (x1 y1 x2 y2 x3 y3 : R) :
  reflect (exists k, (x1, x2, x3) = (k * y1, k * y2, k * y3) \/
                     (y1, y2, y3) = (k * x1, k * x2, k * x3))
          (proportional x1 y1 x2 y2 x3 y3).
Proof.
apply: (iffP idP)=> [/and3P[P1 P2 P3]|[k [] [-> -> ->]]]; last 2 first.
- by rewrite /proportional ![_ * (k * _)]mulrCA !mulrA !eqxx.
- by rewrite /proportional ![_ * (k * _)]mulrCA !mulrA !eqxx.
case: (boolP (x1 == 0)) P1 P2 => [/eqP->|x1NZ P1 P2]; last first.
  exists (y1 / x1); rewrite divfK //; right.
  by congr (_,_,_); apply/(mulfI x1NZ)/eqP; rewrite mulrCA mulrA divfK.
rewrite !mul0r ![0 == _]eq_sym !mulf_eq0.
case: (boolP (y1 == 0))=> [/eqP-> _ _|y1NZ /eqP-> /eqP->]; last first.
  by exists 0; rewrite !mul0r; left.
case: (boolP (x2 == 0)) P3 => [/eqP->|x2NZ P3]; last first.
  exists (y2 / x2); rewrite mulr0 divfK //; right.
  by congr (_,_,_); apply/(mulfI x2NZ)/eqP; rewrite mulrCA mulrA divfK.
rewrite !mul0r ![0 == _]eq_sym !mulf_eq0 => /orP[] /eqP->.
  case: (boolP (x3 == 0)) => [/eqP->|x3NZ].
  by exists 0; rewrite !mul0r; left.
  by exists (y3 / x3); rewrite mulr0 divfK //; right.
by exists 0; rewrite !mul0r; left.
Qed.

Lemma proportionalNZP (x1 y1 x2 y2 x3 y3 : R) (NZ : (x1, x2, x3) != 0) :
  reflect (exists k , (y1, y2, y3) = (k * x1, k * x2, k * x3))
          (proportional x1 y1 x2 y2 x3 y3).
Proof.
apply: (iffP idP)=> [/proportionalP [k [] Hk]|[k Hk]].
- have kNZ : k != 0 by apply: contra NZ; rewrite Hk => /eqP->; rewrite !mul0r.
  by exists k^-1; case: Hk => -> -> ->; rewrite !mulrA !mulVf // !mul1r.
- by exists k.
by apply/proportionalP; exists k; right.
Qed.

Lemma proportional_id x y z :  proportional x x y y z z.
Proof. by rewrite /proportional !eqxx. Qed.

Lemma proportionalC x1 y1 x2 y2 x3 y3 :  
  proportional x1 y1 x2 y2 x3 y3 = proportional y1 x1 y2 x2 y3 x3.
Proof.
by apply/and3P/and3P=> [] [/eqP-> /eqP-> /eqP->]; rewrite !eqxx.
Qed.

Lemma proportional_trans x1 y1 z1 x2 y2 z2 x3 y3 z3 (PNZ : (y1, y2, y3) != 0) :
  proportional x1 y1 x2 y2 x3 y3 -> proportional y1 z1 y2 z2 y3 z3 ->
      proportional x1 z1 x2 z2 x3 z3.
Proof.
case/proportionalP=> k1 [] [E1 E2 E3] /proportionalP[k2 [] [E4 E5 E6]];
    apply/proportionalP.
- by exists (k1 * k2); rewrite E1 E2 E3 E4 E5 E6 !mulrA; left.
- case: (boolP (k1 == 0))=> [/eqP k1Z|k1NZ].
    by exists 0; rewrite E1 E2 E3 k1Z !mul0r; left.
  by exists (k2 / k1); right; rewrite E1 E2 E3 E4 E5 E6 !mulrA !divfK.
- have k1NZ: k1 != 0.
    by apply: contra PNZ=> /eqP E7; rewrite E1 E2 E3 E7 !mul0r.
  by exists (k2 / k1); left; congr (_,_,_); apply: (mulfI k1NZ);
     rewrite mulrCA mulrA divfK -?E1 -?E2 -?E3 -?E4 -?E5 -?E6.
by exists (k2 * k1); rewrite E4 E5 E6 E1 E2 E3 !mulrA; right.
Qed.
 
(* Un point est sur la line : p \in l *)

Definition on_line (l : line) (p : point) := 
let: Line (Point x1 y1 z1) (Point x2 y2 z2) _ := l in
let : Point x3 y3 z3 := p in
  proportional (x1 - x2) (x1 - x3) (y1 - y2) (y1 - y3) (z1 - z2) (z1 - z3).

Canonical on_line_predType := mkPredType on_line.

(* Deux lignes parallèles   : l1 /[l] l2                                      *)

Definition lpar l1 l2 :=
let: Line (Point x1 y1 z1) (Point x2 y2 z2) _ := l1 in
let: Line (Point x3 y3 z3) (Point x4 y4 z4) _ := l2 in
  proportional (x1 - x2) (x3 - x4) (y1 - y2) (y3 - y4) (z1 - z2) (z3 - z4).

Notation " l1 /[l]/ l2 " := (lpar l1 l2) (at level 10).

Lemma lpar_id l : l /[l]/ l.
Proof.
by case: l => [[x1 y1 z1] [x2 y2 z2] /= _]; exact: proportional_id.
Qed.

Lemma lparC l1 l2 : l1 /[l]/ l2 = l2 /[l]/ l1.
Proof.
case: l1 => [[x1 y1 z1] [x2 y2 z2] /=].
case: l2 => [[x3 y3 z3] [x4 y4 z4] /= _ _].
exact: proportionalC.
Qed.

Lemma lpar_trans l1 l2 l3 : l1 /[l]/ l2 -> l2 /[l]/ l3 -> l1 /[l]/ l3.
Proof.
case: l1 => [[x1 y1 z1] [x2 y2 z2] /=].
case: l2 => [[x3 y3 z3] [x4 y4 z4] /=].
case: l3 => [[x5 y5 z5] [x6 y6 z6] /=] _ DP _ /= P1 P2.
apply: proportional_trans P2 => //.
apply: contra DP=> /eqP[] /eqP E1 /eqP E2 /eqP E3.
by apply/eqP; congr Point; apply/eqP; rewrite -subr_eq0.
Qed.

(******************************************************************************)
(*                          PLAN                                              *)
(******************************************************************************)

Inductive plane := Plane (a b c d : R) of (a, b, c) != (0, 0, 0).

(* Pour l'appartenance d'un point à un plan: p \on P                          *)

Definition on_plane pl p :=
  let: Point x y z := p in
  let: Plane a b c d _ := pl in a * x + b * y + c * z == d.

Notation "p \on pl" := (on_plane pl p) (at level 10).

(* Deux plans parallèles : P1 /[p]/ P2                                        *)

Definition ppar p1 p2 :=
let: Plane a1 b1 c1 d1 _ := p1 in
let: Plane a2 b2 c2 d2 _ := p2 in proportional a1 a2 b1 b2 c1 c2.

Notation " p1 /[p]/ p2 " := (ppar p1 p2) (at level 10).

Lemma ppar_id p : p /[p]/ p.
Proof. by case: p => [a b c d /= _]; exact: proportional_id. Qed.

Lemma pparC p1 p2 : p1 /[p]/ p2 = p2 /[p]/ p1.
Proof.
case: p1 => [a1 b1 c1 d1 /=].
case: p2 => [a2 b2 c2 d2 /= _ _].
by exact: proportionalC.
Qed.

Lemma ppar_trans p1 p2 p3 : p1 /[p]/ p2 -> p2 /[p]/ p3 -> p1 /[p]/ p3.
Proof.
case: p1 => a1 b1 c1 d1 /= Dp1.
case: p2 => [a2 b2 c2 d2 /= Dp2].
case: p3 => [a3 b3 c3 d3 /= Dp3].
exact: proportional_trans.
Qed.

(* Appartenance d'une ligne à un plan : l \in P                               *)

Definition l_on_plane (pl : plane) l :=
  let: Line p1 p2 _ := l in (on_plane pl p1) && (on_plane pl p2).

Canonical l_on_plane_predType := mkPredType l_on_plane.

Lemma l_on_planeE (p1 p2 : point) (L : p1 != p2) (P : plane) :
  p1 \on P -> p2 \on P -> Line L \in P.
Proof.
case: p1 L => x1 y1 z1.
case: p2 => x2 y2 z2.
case: P => a b c d i L.
by rewrite /= /in_mem /= /l_on_plane => ->.
Qed.

(* L'intersection d'un plan avec deux plans parallèles donne deux lignes      *)
(* parallèles                                                                 *)

Lemma par_2_plane (p1 p2 p3 : plane) (l1 l2 : line) :
  l1 \in p1 -> l1 \in p3 -> l2 \in p2 -> l2 \in p3 ->
  ~~ p1 /[p]/ p3 -> p1 /[p]/ p2 -> l1 /[l]/ l2.
Proof.
case p1 => [a1 b1 c1 d1 Hp1].
case p2 => [a2 b2 c2 d2 Hp2].
case p3 => [a3 b3 c3 d3 Hp3].
case l1 => [[x1 y1 z1] [x2 y2 z2] HP1].
case l2 => [[x3 y3 z3] [x4 y4 z4] HP2] /=.
case/andP=> /eqP P1 /eqP P2.
case/andP=> /eqP P3 /eqP P4.
case/andP=> /eqP P5 /eqP P6.
case/andP=> /eqP P7 /eqP P8.
move=> HH /(proportionalNZP _ _ _ Hp1) [k Hk].
have kNZ : k != 0.
  by apply: contra Hp2; rewrite Hk => /eqP->; rewrite !mul0r.
pose d4 := k^-1 * d2.
have {P5}P5 : a1 * x3 + b1 * y3 + c1 * z3 = d4.
  apply: (mulfI kNZ); rewrite mulrA mulfV //; rewrite /d4 -P5.
  by case: Hk => -> -> ->; cring.
have {P6}P6 : a1 * x4 + b1 * y4 + c1 * z4 = d4.
  apply: (mulfI kNZ); rewrite mulrA mulfV //; rewrite /d4 -P6.
  by case: Hk => -> -> ->; cring.
pose u := a1 * b3 - a3 * b1.
pose v := a1 * c3 - a3 * c1.
pose w := b1 * c3 - b3 * c1.
have F1 : v * (x1 - x2)- -w * (y1 - y2) = 0.
  have<-: c3 * (d1 - d1) - c1 * (d3 - d3)= 0 by cring.
  by rewrite -{1}P1 -P2 -{1}P3 -P4; cring.
have F2 : u * (x1 - x2) - w * (z1 - z2) = 0.
  have<-: b3 * (d1 - d1) - b1 * (d3 - d3)= 0 by cring.
  by rewrite -{1}P1 -P2 -{1}P3 -P4; cring.
have F3 : - u * (y1 - y2)- v * (z1 - z2) = 0.
  have<-: a3 * (d1 - d1) - a1 * (d3 - d3)= 0 by cring.
  rewrite -{1}P1 -P2 -{1}P3 -P4; cring.
have F4 : v * (x3 - x4) - - w * (y3 - y4) = 0.
  have<-: c3 * (d4 - d4) - c1 * (d3 - d3)= 0 by cring.
  rewrite -{1}P5 -P6 -{1}P7 -P8; cring.
have F5 : u * (x3 - x4)- w * (z3 - z4) = 0.
  have<-: b3 * (d4 - d4) - b1 * (d3 - d3)= 0 by cring.
  by rewrite -{1}P5 -P6 -{1}P7 -P8; cring.
have F6 : -u * (y3 - y4) - v * (z3 - z4) = 0.
  have<-: a3 * (d4 - d4) - a1 * (d3 - d3)= 0 by cring.
  rewrite -{1}P5 -P6 -{1}P7 -P8; cring.
have: [||u != 0, v != 0 | w != 0] by rewrite !subr_eq0 -!negb_and.
case: (boolP (u == 0))=> [/eqP uZ | uNZ];  
    rewrite ?uZ ?(oppr0, mul0r, sub0r, subr0) in F2 F3 F5 F6.
  case: (boolP (v == 0))=> [/eqP vZ /= wNZ | vNZ _];  
    rewrite ?vZ ?(oppr0, mul0r, sub0r, subr0) in F1 F3 F4 F6.
    move/eqP: F1; rewrite mulNr opprK mulf_eq0 (negPf wNZ) => /eqP->.
    move/eqP: F2; rewrite oppr_eq0 mulf_eq0 (negPf wNZ) => /eqP->.
    move/eqP: F4; rewrite mulNr opprK mulf_eq0 (negPf wNZ) => /eqP->.
    move/eqP: F5; rewrite oppr_eq0 mulf_eq0 (negPf wNZ) => /eqP->.
    case: (boolP (x1 - x2 == 0)) => [/eqP->|x1x2NZ].
      by apply/proportionalP; exists 0; left; rewrite !mul0r.
    apply/proportionalP; exists ((x1 - x2)^-1 * (x3 - x4)); right.
    by rewrite mulrAC mulVf // mul1r !mulr0.
  move/eqP: F3; rewrite oppr_eq0 mulf_eq0 (negPf vNZ) => /eqP->.
  move/eqP: F6; rewrite oppr_eq0 mulf_eq0 (negPf vNZ) => /eqP->.
  case: (boolP (w == 0))=> [/eqP wZ | wNZ];  
    rewrite ?wZ ?(oppr0, mul0r, sub0r, subr0) in F1 F2 F4 F5.
    move/eqP: F1; rewrite mulf_eq0 (negPf vNZ) => /eqP->.
    move/eqP: F4; rewrite mulf_eq0 (negPf vNZ) => /eqP->.
    case: (boolP (y1 - y2 == 0)) => [/eqP->|y1y2NZ].
      by apply/proportionalP; exists 0; left; rewrite !mul0r.
    apply/proportionalP; exists ((y1 - y2)^-1 * (y3 - y4)); right.
    by rewrite !mulr0 mulrAC mulVf // mul1r.
  have vwNZ : v * w != 0 by rewrite mulf_eq0 negb_or vNZ.
  rewrite /proportional !mulr0 !eqxx !andbT.
  apply/eqP/(mulfI vwNZ)/eqP.
  rewrite [v * _]mulrC !mulrA.
  rewrite -[w * _ * _]mulrA; move/eqP: F1; rewrite subr_eq0 => /eqP->.
  rewrite eq_sym -[w * v * _]mulrA; move/eqP: F4; rewrite subr_eq0 => /eqP->.
  by apply/eqP; cring.
case: (boolP (v == 0))=> [/eqP vZ /= _ | vNZ _];
    rewrite ?vZ ?(oppr0, mul0r, sub0r, subr0) in F1 F3 F4 F6.
  move/eqP: F3; rewrite mulNr oppr_eq0 mulf_eq0 (negPf uNZ) => /eqP->.
  move/eqP: F6; rewrite mulNr oppr_eq0 mulf_eq0 (negPf uNZ) => /eqP->.
  case: (boolP (w == 0))=> [/eqP wZ | wNZ];
      rewrite ?uZ ?vZ ?wZ ?(oppr0, mul0r, sub0r, subr0) in F1 F2 F4 F5.
    move/eqP: F2; rewrite mulf_eq0 (negPf uNZ) => /eqP->.
    move/eqP: F5; rewrite mulf_eq0 (negPf uNZ) => /eqP->.
    case: (boolP (z1 - z2 == 0)) => [/eqP->|z1z2NZ].
      by apply/proportionalP; exists 0; left; rewrite !mul0r.
    apply/proportionalP; exists ((z1 - z2)^-1 * (z3 - z4)); right.
    by rewrite !mulr0 mulrAC mulVf // mul1r.
  have uwNZ : u * w != 0 by rewrite mulf_eq0 negb_or uNZ.
  rewrite /proportional !mul0r !mulr0 !eqxx !andbT.
  apply/eqP/(mulfI uwNZ)/eqP.
  rewrite !mulrA [u * _ * _]mulrAC; move/eqP: F2; rewrite subr_eq0 => /eqP->.
  rewrite eq_sym [u * _ * _]mulrAC; move/eqP: F5; rewrite subr_eq0 => /eqP->.
  by apply/eqP; cring.
have uvNZ : u * v != 0 by rewrite mulf_eq0 negb_or uNZ.
apply/and3P; split; apply/eqP/(mulfI uvNZ)/eqP; rewrite !mulrA.
- rewrite -[u * v * _]mulrA; move/eqP: F1; rewrite subr_eq0 => /eqP->.
  rewrite eq_sym -[u * v * _]mulrA; move/eqP: F4; rewrite subr_eq0 => /eqP->.
  by apply/eqP; cring.
- rewrite [u * _]mulrC -[v * u * _]mulrA.
  move/eqP: F2; rewrite subr_eq0 => /eqP->.
- rewrite eq_sym -[v * u * _]mulrA; move/eqP: F5; rewrite subr_eq0 => /eqP->.
  by apply/eqP; cring.
rewrite [u * v]mulrC -![v * u * _]mulrA -[u]opprK mulNr.
move/eqP: F3; rewrite subr_eq0 => /eqP->.
rewrite mulNr; move/eqP: F6; rewrite subr_eq0 => /eqP->.
by apply/eqP; cring.
Qed.

(******************************************************************************)
(*                          CUBE                                              *)
(******************************************************************************)

(* les faces sont numérotées de 0 à 5                                         *)

Definition face := 'I_6.

(* Appartenance à une face du cube (les faces sont numérotées de 0 à 5)       *)

Definition on_face (f : face) p :=
  let: Point x y z := p in
  if f == 0%N :> nat then [&& x == 0, 0 <= y <= 1 & 0 <= z <= 1] else
  if f == 1%N :> nat then [&& x == 1, 0 <= y <= 1 & 0 <= z <= 1] else
  if f == 2%N :> nat then [&& y == 0, 0 <= x <= 1 & 0 <= z <= 1] else
  if f == 3%N :> nat then [&& y == 1, 0 <= x <= 1 & 0 <= z <= 1] else
  if f == 4%N :> nat then [&& z == 0, 0 <= x <= 1 & 0 <= y <= 1] else
  [&& z == 1, 0 <= x <= 1 & 0 <= y <= 1].

Canonical on_face_predType := mkPredType on_face.

(* Plans associés aux faces du cube (les faces sont numérotées de 0 à 5)      *)
 
Fact Px : (1,0,0) != (0,0,0) :> R * R * R.
Proof. by apply/negP=> /eqP[] /eqP; rewrite oner_eq0. Qed.
Fact Py : (0,1,0) != (0,0,0) :> R * R * R.
Proof. by apply/negP=> /eqP[] /eqP; rewrite oner_eq0. Qed.
Fact Pz : (0,0,1) != (0,0,0) :> R * R * R.
Proof. by apply/negP=> /eqP[] /eqP; rewrite oner_eq0. Qed.

Definition face_plane (f : face) :=
  if f == 0%N :> nat then Plane 0 Px else
  if f == 1%N :> nat then Plane 1 Px else
  if f == 2%N :> nat then Plane 0 Py else
  if f == 3%N :> nat then Plane 1 Py else
  if f == 4%N :> nat then Plane 0 Pz else
  Plane 1 Pz.

Notation "`P[ i ]" := (face_plane i).

(* Appartenir à une face s'est bien appartenir au plan correspondant          *)

Lemma app_face_place p f : p \in f -> p \on `P[f].
Proof.
case: p => x y z.
by case f => [] [|[|[|[|[|[|i]]]]]] Pi /= /and3P[/eqP-> _ _]; 
   rewrite !(mul0r, mul1r, add0r, addr0).
Qed.

(* Propriété clé : si on prend au moins 4 faces du cube, il y a en a au moins *)
(* deux qui sont parallèles                                                   *)

Lemma count_exist : forall (T : Type) (t : T) (a : pred T) (s : seq T),
       (1 < count a s -> exists i,  exists j,
          [/\ i < size s, j < size s, a (nth t s i), a (nth t s j) & i != j])%N.
Proof.
move=> T t a s; elim: s => //= x s IH.
case: (boolP (a x))=> [ax Hi | Nax]; last first.
  by case/IH=> i1 [j1 [P1 P2 P3 P4 P5]]; exists i1.+1; exists j1.+1.
have ha : has a s.
  by rewrite has_count -ltnS -[X in (_ < X)%N]add1n.
exists 0%N; exists (find a s).+1.
by rewrite !ltnS /= ax nth_find -?has_find.
Qed.

Lemma par_face_place n (t : n.+4.-tuple face) :
  exists i, exists j, `P[tnth t i] /[p]/ `P[tnth t j] && (i != j).
Proof.
pose p0 i := `P[i] /[p]/ `P[0].
pose p1 i := `P[i] /[p]/ `P[2%:R].
pose p2 i := `P[i] /[p]/ `P[4%:R].
have PP : (count p0 t + count p1 t + count p2 t = n.+4)%N.
  rewrite -{4}(size_tuple t) -count_predT -count_predUI.
  have /eq_count->: predI p0 p1 =1 pred0.
    move=> i /=; rewrite /p0 /p1; apply/idP/negP.
    by case: i; (do 6 try case => //) => i /=; 
       rewrite /proportional !mul0r !mul1r !eqxx ?[_ == 1]eq_sym
               ?oner_eq0 ?andbF ?orbT.
  rewrite count_pred0 addn0 -count_predUI.
  have /eq_count->: predI (predU p0 p1) p2 =1 pred0.
    move=> i /=; rewrite /p0 /p1 /p2; apply/idP/negP.
    by case: i; (do 6 try case => //) => i /=; 
       rewrite /proportional !mul0r !mul1r !eqxx ?[_ == 1]eq_sym
               ?oner_eq0 ?andbF ?orbT.
  rewrite count_pred0 addn0; apply: eq_count => i /=.
  rewrite /p0 /p1 /p2.
  by case: i; do 7 try case => //=; rewrite proportional_id ?orbT.
case: (boolP (1 < count p0 t)%N) => F0.
  have [i [j [Li Lj Pi Pj Dij] ]] := count_exist 0 F0.
  rewrite size_tuple in Li Lj.
  exists (Ordinal Li); exists (Ordinal Lj).
  by rewrite !(tnth_nth 0) (ppar_trans Pi) 1?pparC.
case: (boolP (1 < count p1 t)%N) => F1.
  have [i [j [Li Lj Pi Pj Dij] ]] := count_exist 0 F1.
  rewrite size_tuple in Li Lj.
  exists (Ordinal Li); exists (Ordinal Lj).
  by rewrite !(tnth_nth 0) (ppar_trans Pi) 1?pparC.
case: (boolP (1 < count p2 t)%N) => F2.
  have [i [j [Li Lj Pi Pj Dij] ]] := count_exist 0 F2.
  rewrite size_tuple in Li Lj.
  exists (Ordinal Li); exists (Ordinal Lj).
  by rewrite !(tnth_nth 0) (ppar_trans Pi) 1?pparC.
by case: count PP F0 F1 F2 => [|[|[|]]] //;
   do 2 case: count => [|[|[|]]] //.
Qed.

(******************************************************************************)
(*               POLYGONE INSCRIT                                             *)
(******************************************************************************)

(* Notre plan de coupe                                                        *)

Variable P : plane.

(* fonction next sur les indices pour avoir la circularité                    *)

Definition next n : 'I_n -> 'I_n :=
  if n is n1.+1 then fun i => inZp i.+1 else id.

Lemma nextE n (i : 'I_n.+2) : next i = i + 1.
Proof.  by apply/val_eqP; rewrite /= addn1. Qed.

(* Définition du polygone inscrit                                             *)

Inductive ipolygon n := IPolygon (t: n.-tuple point) of
 [&&
    (* tous les points appartiennent au plan                                  *)
    [forall i, tnth t i \on P], 
    (* les points sont 2 à 2 distincts                                        *)
    [forall i, forall j, (i != j) ==> (tnth t i != tnth t j)] &         
    (* un point et son successeur appartiennent toujours à une face qui       *)
    (* n'est pas parallèle au plan de coupe                                   *)
    [forall i,  exists f : face,
       [&& tnth t i \in f, tnth t (next i) \in f & ~~ `P[f] /[p]/ P ]]
  ].

(* Fonction d'accès des points du polygone                                    *)

Definition ipoint n (ip : ipolygon n) i := 
  let: IPolygon t _ := ip in tnth t i.

(* Fonction d'accès des lignes du polygone                                     *)

Lemma ipoint_diff n (ip : ipolygon n.+2) i : ipoint ip i != ipoint ip (next i).
Proof.
case: ip=> t /= /and3P[_ /forallP/(_ i) /forallP/(_ (next i)) /implyP->] //.
by rewrite nextE eq_sym addrC -subr_eq0 addrK oner_eq0.
Qed.

Lemma ipoint_on_p n (ip : ipolygon n.+2) i : ipoint ip i \on P.
Proof. by case: (ip)=> t /= /and3P[/forallP/(_ i)]. Qed.

Definition iline n (ip : ipolygon n.+2) i := Line (ipoint_diff ip i).

Lemma ipoint_iline n (ip : ipolygon n.+2) i : ipoint ip i \in iline ip i.
Proof.
rewrite /in_mem /=.
case: ipoint => x1 y1 z1; case: ipoint=> x2 y2 z2.
by apply/proportionalP; exists 0; right; rewrite !mul0r !subrr.
Qed.

Lemma ipoint_iline_next  n (ip : ipolygon n.+2) i :
  ipoint ip (next i) \in iline ip i.
Proof.
rewrite /in_mem /=.
case: ipoint => x1 y1 z1; case: ipoint=> x2 y2 z2.
by apply/proportionalP; exists 1; right; rewrite !mul1r.
Qed.

Lemma iline_in_p n (ip : ipolygon n.+2) i : iline ip i \in P.
Proof. by apply: l_on_planeE; apply: ipoint_on_p. Qed.

(* Tout polygone inscrit de plus de 4 points à au moins deux lignes           *)
(* parallèles , on ne peut donc pas avoir de pentagone régulier!              *)

Lemma ipolygon_par n (ip : ipolygon n.+4) :
  exists i, exists j, iline ip i /[l]/ (iline ip j) && (i != j).
Proof.
case: ip => t Ht.
have /and3P[_ _ /forallP HP] := Ht.
have /existsP[f0 /and3P[t0If0 t1If0 Pf0]] := HP 0.
have /existsP[f1 /and3P[t1If1 t2If1 Pf1]] := HP 1.
have /existsP[f2 /and3P[t2If2 t3If2 Pf2]] := HP 2%:R.
have /existsP[f3 /and3P[t3If3 t4If3 Pf3]] := HP 3%:R.
set p := IPolygon _.
pose T := [tuple f0; f1; f2; f3].
pose T1 : 4.-tuple 'I_n.+4 := [tuple 0; 1; 2%:R; 3%:R].
have [i [j /andP[Hi Hj]]] := (par_face_place T).
exists (tnth T1 i); exists (tnth T1 j); apply/andP; split => //.
  have PP : ~~ `P[tnth T i] /[p]/ P by case: (i); do 4 case=> //.
  apply: par_2_plane PP (Hi).
    apply: l_on_planeE.
      by apply: app_face_place; case: (i); do 4 case=> //.
      by apply: app_face_place; case: (i); do 4 case=> //.
    by apply: iline_in_p.
  apply: l_on_planeE.
    by apply: app_face_place; case: (j); do 4 case=> //.
    by apply: app_face_place; case: (j); do 4 case=> //.
  by apply: iline_in_p.
by case: (i) Hj; (do 4 (try case=> //)) => U;
   case: (j); (do 4 (try case=> //=)) => V.
Qed.

End Cube.