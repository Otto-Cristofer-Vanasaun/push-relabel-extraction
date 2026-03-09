Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.QOrderedType.
Require Import Coq.QArith.Qminmax.
Require Import Coq.QArith.QOrderedType.
Require Import Lia. (*tactic: lia*)
Require Import Lqa. (*tactic: lra*)
Require Import Coq.Arith.PeanoNat.

Ltac destruct_guard_in H :=
generalize H; clear H;
lazymatch goal with
| |- context [match ?X with _ => _ end] =>
let e := fresh "E" in destruct X eqn: e;
let h := fresh H in intros h
| |- context [if ?X then _ else _] =>
let e := fresh "E" in destruct X eqn: e;
let h := fresh H in intros h
end.

Ltac destruct_guard :=
match goal with
| |- context [match ?X with _ => _ end] =>
let e := fresh "E" in destruct X eqn: e
| |- context [if ?X then _ else _] =>
let e := fresh "E" in destruct X eqn: e
end.

Ltac inv_clear H := inversion H; subst; clear H.

Fixpoint Distinct {t} (xs:list t) : Prop :=
match xs with
| nil => True
| x::xs => ~(In x xs) /\ Distinct xs
end.

Module Type T.
Parameter V: Type.
Parameter eqb: V -> V -> bool.
Parameter equal: forall x y, reflect (x=y) (eqb x y).
Lemma eqb_refl u: eqb u u = true.
Proof. destruct (equal u u); auto. Qed.
Lemma eqb_neq u v: u<>v -> eqb u v = false.
Proof. intros. destruct (equal u v); auto. contradiction. Qed.
End T.

Module Type MapSpec (T:T).
Import T.
(* Arvutamine *)
Parameter t: forall (e:Type), Type.
Parameter empty: forall {e:Type}, t e.
Parameter replace: forall {e:Type} , V -> e -> t e -> t e.
Parameter find: forall {e:Type} , e -> t e -> V -> e.
Parameter update: forall {e:Type}, e -> V -> (e->e) -> t e -> t e.
Parameter size: forall {e:Type}, t e -> nat.
Notation "m [ v ]" := (find m v) (at level 12).
(* Omadused *)
Parameter FindUpdateEq: forall {e d} {f:e->e} (xs:t e) u ,
find d (update d u f xs) u = f (find d xs u) .
Parameter FindUpdateNeq: forall {e d} {f:e->e} (xs:t e) u v , u<>v ->
find d (update d v f xs) u = find d xs u .

Parameter FindReplaceEq: forall {e d} {f:e} (xs:t e) u,
find d (replace u f xs) u = f .

Parameter FindReplaceNeq: forall {e d} {f:e} (xs:t e) u v, u<>v ->
find d (replace v f xs) u = find d xs u .
Parameter FindEmpty: forall {e} {d:e} k, find d empty k = d.
End MapSpec.

Module Map (T:T) <: MapSpec (T).
Import T.
Definition t (e:Type) := list (V * e).
Definition empty {e:Type} : t e := nil.

(* Eemaldab tipu v järjendist xs, kui see seal leidub *)
Fixpoint remove {e:Type} (v:V) (xs: t e) : t e :=
match xs with
| nil => nil
| ((u,y)::xs) =>
if eqb v u then
remove v xs
else
(u,y)::(remove v xs)
end.

(* Asendab tipu v järjendis xs, kui see seal leidub *)
Fixpoint replace {e:Type} (v:V) (x:e) (xs:t e) :=
match xs with
| nil => (v,x)::nil
| ((u,y)::xs) =>
if eqb v u then
(u,x)::(remove v xs)
else
(u,y)::(replace v x xs)
end.

(* Uuendab tipust väljuvaid servasid, kui antud tipp leidub xs-is *)
Fixpoint update {e:Type} (d:e) (v:V) (f:e->e) (xs:t e) :=
match xs with
| nil => (v,f d)::nil
| ((u,y)::xs) =>
if eqb v u then
(u,f y)::(remove v xs)
else
(u,y)::(update d v f xs)
end.
Fixpoint find {e:Type} d (xs:t e) (v:V) :=
match xs with
| nil => d
| ((u,y)::xs) =>
if eqb v u then
y
else
find d xs v
end.
Definition size {e:Type} (m: t e): nat := length m.

Lemma FindEmpty: forall {e} {d:e} k, find d empty k = d.
Proof.
intros. cbn. reflexivity.
Qed.

Lemma FindRemoveEq {e d} {f:e->e} (xs:t e) u :
find d (remove u xs) u = d.
Proof.
intros. induction xs.
+ simpl. reflexivity.
+ simpl. destruct a.
- destruct (equal u v).
* auto.
* simpl. rewrite -> eqb_neq; auto.
Qed.

Lemma FindRemoveNeq {e d} (xs:t e) u v : u<>v ->
find d (remove v xs) u = find d xs u .
Proof.
intros. induction xs; auto.
simpl. destruct a. destruct (equal v v0).
+ destruct (equal u v0).
- subst. contradiction.
- auto.
+ simpl. rewrite -> IHxs. reflexivity.
Qed.

Lemma FindUpdateEq {e d} {f:e->e} (xs:t e) u :
find d (update d u f xs) u = f (find d xs u) .
Proof.
intros. induction xs.
+ simpl. destruct (equal u u); auto.
- contradiction.
+ simpl. destruct a. destruct (equal u v).
- simpl. subst v. destruct (equal u u); auto.
* rewrite -> FindRemoveNeq; auto.
-- contradiction.
- simpl. destruct (equal u v).
* subst. contradiction.
* rewrite -> IHxs. reflexivity.
Qed.

Lemma FindUpdateNeq {e d} {f:e->e} (xs:t e) u v : u<>v ->
find d (update d v f xs) u = find d xs u .
Proof.
intros. induction xs.
+ simpl. destruct (equal u v); auto.
- contradiction.
+ simpl. destruct a. destruct (equal v v0).
- simpl. subst. rewrite eqb_neq; auto.
rewrite -> FindRemoveNeq; auto.
- simpl. destruct (equal u v0); auto.
Qed.
Lemma FindReplaceEq {e d} {f:e} (xs:t e) u :
find d (replace u f xs) u = f .
Proof.
intros. induction xs.
+ simpl. destruct (equal u u); auto.
- contradiction.
+ simpl. destruct a. destruct (equal u v).
- simpl. destruct (equal u v); auto.
* contradiction.
- simpl. destruct (equal u v).
* contradiction.
* rewrite -> IHxs. reflexivity.
Qed.

Lemma FindReplaceNeq {e d} {f:e} (xs:t e) u v : u<>v ->
find d (replace v f xs) u = find d xs u .
Proof.
intros. induction xs.
+ simpl. destruct (equal u v); auto.
- contradiction.
+ simpl. destruct a. destruct (equal v v0).
- simpl. subst. rewrite -> eqb_neq; auto.
* rewrite -> FindRemoveNeq; auto.
- simpl. destruct (equal u v0); auto.
Qed.
End Map.

Module Type SetSpec (T:T).
Import T.
(* Arvutamine *)
Parameter t: Type.
Parameter empty: t.
Parameter add: V -> t -> t.
Parameter remove: V -> t -> t.
Parameter mem: V -> t -> bool.
Parameter choice: forall (s:t), option (V * t).
Parameter filter: forall (p:V->bool), t -> t.
Parameter to_list: t -> list V.
Parameter find_first: (V -> bool) -> t -> option V.
Parameter size: t -> nat.
Notation "v ∈ s" := (mem v s) (at level 12).
(* Tõestus *)

Parameter to_list_distinct: forall s, Distinct (to_list s).
Parameter to_list_in: forall v s, v ∈ s = true <-> In v (to_list s).

Parameter in_filter: forall v (p:V->bool) s, (v ∈ (filter p s)) = true -> (v ∈ s) = true /\ p v = true.

Parameter filter_in: forall v (p:V->bool) s, (v ∈ s) = true -> p v = true -> (v ∈ (filter p s)) = true.

Parameter find_first_specSome: forall p vs v,
find_first p vs = Some v -> p v = true /\ v ∈ vs = true.
Parameter find_first_specNone: forall p vs,
find_first p vs = None -> forall v, v ∈ vs = true -> p v = false .
Parameter choiceSome: forall s a s',
choice s = Some (a,s') -> a ∈ s=true /\ s'=remove a s.
Parameter MemRemoveNeq: forall (xs:t) u v, u<>v -> u ∈ (remove v xs) = u ∈ xs.
Parameter MemAddNeq: forall (xs:t) u v, u<>v -> u ∈ (add v xs) = u ∈ xs.
Parameter MemRemoveEq: forall (xs:t) u, u ∈ (remove u xs) = false.
Parameter MemAddEq: forall (xs:t) v, v ∈ (add v xs) = true.
Parameter choiceNone: forall s, choice s = None <-> s=empty.
Parameter MemEmpty: forall v, v ∈ empty = false.
End SetSpec.

Module MkSet (T:T) <: SetSpec (T).
Import T.
Definition t := list V.
Definition empty: t := nil.
Fixpoint remove v s :=
match s with
| nil => nil
| v' :: s => if T.eqb v v' then remove v s else v' :: remove v s
end.
Definition add v s := v :: remove v s.

Fixpoint to_list (s:t): list V :=
match s with
| nil => nil
| x::xs => x :: remove x (to_list xs)
end.

Fixpoint mem v s :=
match s with
| nil => false
| v' :: s => if T.eqb v v' then true else mem v s
end.

Fixpoint find_first (p:V -> bool) (xs: list V) :=
match xs with
| nil => None
| x::xs => if p x then Some x else find_first p xs
end.
Definition size (s:t) := length (to_list s).

Notation "v ∈ s" := (mem v s) (at level 12).

Lemma find_first_specSome: forall p vs v,
find_first p vs = Some v -> p v = true /\ v ∈ vs = true.
Proof.
intros p vs. induction vs; intros v H; cbn in H.
+ inv_clear H.
+ destruct (p a) eqn:E.
++ inv_clear H. split; try tauto. cbn.
rewrite eqb_refl. reflexivity.
++ apply IHvs in H. destruct H.
split; auto. cbn. destruct (eqb v a) eqn:G; auto.
Qed.

Lemma find_first_specNone: forall p vs,
find_first p vs = None -> forall v, v ∈ vs = true -> p v = false .
Proof.
intros p vs H. induction vs; intros.
+ inversion H0.
+ cbn in *. destruct (p a) eqn:E; [inversion H|].
destruct (equal v a); subst; auto.
Qed.

Lemma NotInRemoveToList: forall a s, ~ In a (remove a s).
Proof.
intros a. induction s; cbn; auto.
destruct (equal a a0); auto. cbn. intros [H|H]; auto.
Qed.

Lemma RemoveIn: forall b a xs, In b (remove a xs) -> In b xs.
Proof.
intros b a xs. induction xs; cbn; intros H; auto.
destruct (equal a a0); try tauto.
cbn in H. destruct H; subst; tauto.
Qed.

Lemma DistinctRemove: forall a xs, Distinct xs -> Distinct (remove a xs) .
Proof.
intros a. induction xs; auto. cbn. intros [H1 H2].
destruct (equal a a0); cbn; subst; auto. split; auto.
intro H. eapply H1, RemoveIn, H.
Qed.
Lemma to_list_distinct: forall s, Distinct (to_list s).
Proof.
induction s; simpl; auto. split.
+ apply NotInRemoveToList.
+ apply DistinctRemove, IHs.
Qed.

Lemma InRemove: forall v a s, v <> a -> In v s -> In v (remove a s).
Proof.
intros v a xs He. induction xs; cbn; auto. intros [->|H].
+ destruct (equal a v); cbn; subst; auto. tauto.
+ destruct (equal a a0); cbn; subst; auto.
Qed.

Lemma to_list_in: forall v s, v ∈ s = true <-> In v (to_list s).
Proof.
intros v s. split; intros H.
+ induction s; cbn; auto.
++ inversion H.
++ cbn in *. destruct (equal v a); subst; try tauto.
right. apply InRemove; auto.
+ induction s; [inversion H|]. cbn in *.
destruct (equal v a);
destruct H; subst; cbn; auto.
eapply IHs, RemoveIn, H.
Qed.

Lemma MemEmpty: forall v, v ∈ empty = false.
Proof. intros. reflexivity. Qed.

Lemma MemAddEq (xs:t) v :
v ∈ (add v xs) = true.
Proof.
intros. simpl. rewrite eqb_refl; auto.
Qed.

Lemma MemRemoveEq (xs:t) u :
u ∈ (remove u xs) = false.
Proof.
intros. induction xs; auto.
simpl. destruct (equal u a); auto.
simpl. rewrite eqb_neq; auto.
Qed.

Lemma MemRemoveNeq (xs:t) u v : u<>v ->
u ∈ (remove v xs) = u ∈ xs.
Proof.
intros. induction xs; auto.
simpl. destruct (equal v a).
+ subst. destruct (equal u a); auto.
+ destruct (equal u a).
- subst. simpl. rewrite eqb_refl; auto.
- simpl. rewrite eqb_neq; auto.
Qed.

Lemma MemAddNeq (xs:t) u v : u<>v ->
u ∈ (add v xs) = u ∈ xs.
Proof.
intros. induction xs.
+ simpl. destruct (equal u v); auto.
contradiction.
+ simpl. destruct (equal u v).
- destruct (equal u a); auto.
subst. contradiction.
- destruct (equal v a).
* destruct (equal u a).
** subst. contradiction.
** subst. rewrite <- IHxs. inversion IHxs. destruct (equal u a).
*** subst. contradiction.
*** rewrite IHxs. apply H1.
* destruct (equal u a).
** subst. simpl. rewrite eqb_refl; auto.
** simpl. destruct (equal u a).
*** subst. contradiction.
*** simpl in *. rewrite eqb_neq in IHxs; auto.
Qed.

Definition choice s: option (V*t) :=
match s with
| nil => None
| v :: s => Some (v, remove v s)
end.

Lemma choiceNone s: choice s = None <-> s=empty.
Proof.
intros. induction s.
+ split; auto.
+ split.
- destruct IHs. simpl in *.
intros. inversion H1.
- intros. inversion H.
Qed.

Fixpoint filter (p:V->bool) (xs:t) :=
match xs with
| nil => nil
| v::s => if p v then v::filter p s else filter p s
end.
Lemma in_filter v (p:V->bool) s : (v ∈ (filter p s)) = true -> (v ∈ s) = true /\ p v = true.
Proof.
intros. split.
+ induction s; auto.
simpl in *. destruct (equal v a); auto.
- apply IHs. destruct (p a).
* simpl in *. rewrite eqb_neq in H; auto.
* auto.
+ induction s.
- simpl in *. inversion H.
- simpl in H. destruct (p a) eqn : e.
* simpl in *. destruct (equal v a); subst; auto.
* auto.
Qed.

Lemma filter_in v (p:V->bool) s : (v ∈ s) = true -> p v = true -> (v ∈ (filter p s)) = true.
Proof.
intros. induction s; auto.
simpl in *. destruct (p a) eqn : E.
+ simpl. destruct (equal v a); auto.
+ destruct (equal v a); auto.
subst. apply IHs. rewrite <- H0. destruct (p a).
- inversion E.
- inversion H0.
Qed.

Definition fold_left {a:Type} (f:a -> V -> a) (xs:t) (x:a) :=
fold_left f xs x.

Inductive IsSet : t -> Prop :=
| NilIsSet: IsSet nil
| ConsIsSet {a xs} : (a ∈ xs) = false -> IsSet xs -> IsSet (a::xs).
Lemma EmptyIsSet: IsSet empty.
Proof.
apply NilIsSet.
Qed.

Lemma RemoveOtherInFalse a b xs: a ∈ xs = false -> a ∈ remove b xs = false.
Proof.
intros. induction xs; auto.
simpl. destruct (equal b a0).
+ apply IHxs. subst. inversion H. destruct (equal a a0); auto.
inversion H1.
+ simpl. destruct (equal a a0).
- subst. simpl in *. rewrite eqb_refl in H. inversion H.
- apply IHxs. simpl in *. destruct (equal a a0); auto.
subst. inversion H.
Qed.
Lemma RemoveSameInFalse a xs: a ∈ remove a xs = false.
Proof.
intros. induction xs; auto.
simpl. destruct (equal a a0); auto.
simpl. destruct (equal a a0); auto.
subst. contradiction.
Qed.

Lemma RemoveIsSet a xs: IsSet xs -> IsSet (remove a xs).
Proof.
intros. induction xs; auto.
simpl. destruct (equal a a0).
+ subst. apply IHxs. inversion H. subst. apply H3.
+ inversion H. subst. apply ConsIsSet.
- rewrite <- H2. apply MemRemoveNeq.
intro C. inv_clear C. contradiction.
- auto.
Qed.

Lemma AddIsSet a xs: IsSet xs -> IsSet (add a xs).
Proof.
intros. induction xs.
+ unfold add. simpl. apply ConsIsSet; auto.
+ unfold add. simpl. destruct (equal a a0).
- subst. inversion H. subst. auto.
- inversion H. subst. apply ConsIsSet.
* simpl. rewrite eqb_neq; auto.
apply RemoveSameInFalse.
* apply ConsIsSet.
** apply RemoveOtherInFalse. apply H2.
** apply RemoveIsSet. apply H3.
Qed.

Lemma ChoiceIsSet a xs: IsSet xs -> forall xs', choice xs = Some (a, xs') -> IsSet xs'.
Proof.
intros. induction xs.
+ inversion H0.
+ inversion H. subst. inversion H0. subst. apply RemoveIsSet, H4.
Qed.

Lemma FilterOtherInFalse a f xs: a ∈ xs = false -> a ∈ filter f xs = false.
Proof.
intros. induction xs; auto.
simpl. destruct (f a0) eqn : E.
+ simpl. destruct (equal a a0).
- subst. simpl in *. rewrite eqb_refl in H. inversion H.
- apply IHxs. simpl in *. destruct (equal a a0); auto.
subst. inversion H.
+ apply IHxs. simpl in *. destruct (equal a a0); auto.
subst. inversion H.
Qed.

Lemma filterIsSet f xs: IsSet xs -> IsSet (filter f xs).
Proof.
intros. induction xs; auto.
simpl. destruct (f a).
+ apply ConsIsSet.
- apply FilterOtherInFalse. inversion H. auto.
- inversion H. subst. apply IHxs. apply H3.
+ inversion H. subst. apply IHxs. apply H3.
Qed.

Lemma choiceSome s: forall a s',
choice s = Some (a,s') -> a ∈ s=true /\ s'=remove a s.
Proof.
induction s; intros.
+ inversion H.
+ split.
- simpl. destruct (equal a0 a).
* subst. auto.
* inversion H. subst. simpl in H. inversion H.
subst. contradiction.
- simpl. destruct (equal a a0).
** subst. rewrite eqb_refl. simpl in *.
inversion H. reflexivity.
** rewrite eqb_neq; auto. simpl in *. inversion H. contradiction.
Qed.
End MkSet.

Module Tuple (T U:T) <: T.
Definition V := (T.V * U.V)%type.
Definition eqb '(a,b) '(c,d) := T.eqb a c && U.eqb b d.
Definition equal (x y:V): reflect (x=y) (eqb x y).
Proof.
destruct x, y. simpl.
destruct (T.equal v v1), (U.equal v0 v2); subst;
simpl; constructor; intuition; inversion H; auto.
Qed.
Lemma eqb_refl u: eqb u u = true.
Proof. destruct (equal u u); auto. Qed.
Lemma eqb_neq u v: u<>v -> eqb u v = false.
Proof. intros. destruct (equal u v); auto. contradiction. Qed.
End Tuple.

Module PR (T:T).

(* Sisend *)

Import T.
Definition R := Q.

Module Edge := Tuple (T) (T).

Module EMap : MapSpec (Edge) := Map (Edge).

Module VSet : SetSpec (T) := MkSet (T).
Notation "v '∈v' s" := (VSet.mem v s) (at level 12).

Module ESet : SetSpec (Edge) := MkSet (Edge).
Notation "v '∈e' s" := (ESet.mem v s) (at level 12).

(* Graaf, mis koosneb tippude ja servade hulkadest*)
Definition Graph := (VSet.t * ESet.t)%type.

(* Transpordivõrk kujul (Graaf, serva läbilaskevõime, algustipp, lõpptipp)*)
Definition FlowNet := (Graph * (V -> V -> R) * V * V)%type.

Definition nodes (fn:FlowNet) :=
let '((vs, es),c,s,t) := fn in vs.

(* väljund *)
Definition sink (fn:FlowNet) :=
let '((vs, es),c,s,t) := fn in t.

(* sisend *)
Definition source (fn:FlowNet) :=
let '((vs, es),c,s,t) := fn in s.
Definition QLe (a b: Q): bool :=
match Qlt_le_dec b a with
| left _ => false
| right _ => true
end.
Infix "<=?" := QLe : Q_scope.
Definition QLt (a b: Q): bool :=
match Qlt_le_dec a b with
| left _ => true
| right _ => false
end.
Infix "<?" := QLt : Q_scope.
Definition QInfLt (x y: option Q): bool :=
match x, y with
| Some a, Some b => a <? b
| Some _, None => true
| _, _ => false
end.

Lemma QLt_spec x y: reflect (x<y)%Q (x<?y)%Q.
Proof.
unfold QLt. destruct (Qlt_le_dec x y ) ; constructor; lra.
Qed.

Lemma QLt_false x y: (x <? y)%Q = false <-> y<=x .
Proof. unfold QLt. destruct (Qlt_le_dec x y); split; intros.
all: auto.
all: try inversion H. lra.
Qed.

Definition QSumList :=
fold_right Qplus 0 .
(* Arvutab transpordivõrgu fn, millel on eelvoog f, tipu x ülejäägi, lahutades väljaminevast voost maha sissetuleva voo. *)
Definition excess (fn:FlowNet) (f: EMap.t R) : V -> R :=
let '((vs, es),c,s,t) := fn in
fun u =>
QSumList (map (fun v => EMap.find 0 f (v,u)) (VSet.to_list vs)) -
QSumList (map (fun v => EMap.find 0 f (u,v)) (VSet.to_list vs)) .
(* Arvutab välja serva (u, v) alles oleva läbilaskevõime ja tagastab selle.
c u v tähistab serva läbilaskevõimet ja f[(u,v)] serva voogu.
Tingimus (u,v) ∈e es tagastab tõeväärtuse true, siis kui serv (u, v) kuulub servade hulka es.
Kui serv (u, v) ei kuulu servade hulka, siis tagastatakse voog, mis läheb tagurpidi ehk serva (v, u) voog.*)
Definition res_cap (fn: FlowNet) (f: EMap.t R) u v : R :=
let '((vs, es),c,s,t) := fn in
if (u,v) ∈e es then
c u v - EMap.find 0 f (u,v)
else
EMap.find 0 f (v,u)
.

Definition E (fn: FlowNet) (f: EMap.t R) :=
let '((vs, es),c,s,t) := fn in
ESet.filter (fun '(u, v) => EMap.find 0 f (u,v) <? c u v) es.
Definition res_net (fn: FlowNet) (f: EMap.t R) : FlowNet :=
let '((vs, es),c,s,t) := fn in
((vs,E fn f),res_cap fn f,s,t).

Module NMap := Map (T).
(* valib tipu u ülejäägist ning läbilaskevõimest Qmin abil miinimumi ja saadab selle voona edasi järgmisesse tippu v.
Kui (u,v) ∈e es ehk serv (u, v) kuulub hulka es tagastab true, siis suurendatakse serva (u, v) voogu delta võrra.
False korral vähendatakse serva (v, u) voogu delta võrra. *)
Definition push fn f u v : EMap.t R :=
let '((vs, es),c,s,t) := fn in
let delta := Qmin (excess fn f u) (res_cap fn f u v) in
if (u,v) ∈e es then
(EMap.update 0 (u,v) (fun x=>x+delta) f)
else
(EMap.update 0 (v,u) (fun x=>x-delta) f)
.
Definition option_min (x:option nat) (y:nat): option nat :=
match x with
| None => Some y
| Some a => Some (min a y)
end.

Fixpoint smallest_rank l xs r :=
match xs, r with
| nil, _ => r
| v::xs, None => smallest_rank l xs (Some v)
| v::xs, Some r =>
if (NMap.find 0 l r <=? NMap.find 0 l v)%nat
then smallest_rank l xs (Some r)
else smallest_rank l xs (Some v)
end.

(* Filtreerib välja tipud, mille vahel on läbilaskevõime ära kasutatud ja jätab alles tipud, mille vahel on läbilaskevõime olemas.
Peale seda otsib, kas leiab tipu r, mille kõrgus on väiksem või võrdne tipu v kõrgusega.
Kui tipu r kõrgus on väiksem või võrdne tipu v kõrgusega siis tagastatakse tipp r, vastasel juhul tagastatakse tipp v. *)
Definition relabel_find fn f (l:NMap.t nat) u vs :=
let fvs := VSet.filter (fun v => 0 <? res_cap fn f u v) vs in
smallest_rank l (VSet.to_list fvs) None.
(* Suurendab tipu u kõrgust 1 võrra, leides naabertippude hulgast kõige väiksema kõrgusega tipu.
Kui leitakse vastab tipp, siis asendatakse tipu u kõrgust leitud kõrguses 1 võrra suuremaga.
Kui sobivat tippu ei leidu ehk saadakse väärtus None, siis relabel nurjub.
See juhtum aga algoritmi töö käigus kunagi ei realiseeru.*)
Definition relabel fn f (l:NMap.t nat) u : option (NMap.t nat):=
let '((vs, es),c,s,t) := fn in
match relabel_find fn f l u vs with
| None => None
| Some n => Some (NMap.replace u (1 + NMap.find 0 l n)%nat l)
end.

(* Otsib tippude vs’ hulgast tippu v, kuhu saaks voogu saata ning
mis oleks tipu u kõrgusest 1 võrra kõrgemal ja servade (u, v) vahel oleks veel läbilaskevõimet. *)
Definition find_push_node fn f (l:NMap.t nat) u (vs':VSet.t) :=
let '((vs, es),c,s,t) := fn in
VSet.find_first (fun v =>
(NMap.find 0 l u =? 1+ NMap.find 0 l v)%nat &&
(0 <? res_cap fn f u v)) vs'.

(* Kontrollib, et antud tipp v ei oleks väljund ega sisend ja ülejääk oleks suurem kui 0.
T.eqb tagastab tõeväärtuse true, siis kui argumentideks antud tipud on võrdsed ning
0 <? Excess fn f v tagastab true väärtuse, siis kui tipu v ülejääk on suurem kui 0. *)
Definition has_excess_not_sink fn f v :=
let '((vs, es),c,s,t) := fn in
if T.eqb v t || T.eqb v s then
false
else if 0 <? excess fn f v then
true
else
false
.

Inductive Tr : Type :=
| Init: EMap.t Q -> NMap.t nat -> VSet.t -> Tr
| Push: V -> V -> EMap.t Q -> VSet.t -> Tr
| Relabel : V -> nat -> NMap.t nat -> Tr
| OutOfGas
| RelabelFailed
.

(* Leiab graafis maksimaalse voo, kasutades push ja relabel samme, ning tagastab selle, juhul kui graafis pole tippe või servasid, siis tagastab väärtuse None. *)
Fixpoint gpr_helper_trace fn f l ac g tr: (option (EMap.t Q*NMap.t nat)*list Tr) :=
let '((vs, es),c,s,t) := fn in
match g with
| O => (None, OutOfGas::tr)
| S g' =>
match VSet.choice ac with
| None => (Some (f,l),tr)
| Some (u,ac') =>
match find_push_node fn f l u vs with
| Some v =>
let f' := push fn f u v in
let ac' := if 0 <? (excess fn f' u) then ac else ac' in
if has_excess_not_sink fn f' v then
let ac'' := VSet.add v ac' in
gpr_helper_trace fn f' l ac'' g' (Push u v f' ac''::tr)
else
let ac'' := VSet.remove v ac' in
gpr_helper_trace fn f' l ac'' g' (Push u v f' ac'::tr)
| None =>
match relabel fn f l u with
| None => (None, RelabelFailed::tr)
| Some l' =>
gpr_helper_trace fn f l' ac g' (Relabel u (NMap.find 0 l' u)%nat l'::tr)
end
end
end
end.
Lemma gpr_helper_trace_fn fn f l ac g tr :
gpr_helper_trace fn f l ac g tr =
let '((vs, es),c,s,t) := fn in
match g with
| O => (None, OutOfGas::tr)
| S g' =>
match VSet.choice ac with
| None => (Some (f,l),tr)
| Some (u,ac') =>
match find_push_node fn f l u vs with
| Some v =>
let f' := push fn f u v in
let ac' := if 0 <? (excess fn f' u) then ac else ac' in
if has_excess_not_sink fn f' v then
let ac'' := VSet.add v ac' in
gpr_helper_trace fn f' l ac'' g' (Push u v f' ac''::tr)
else
let ac'' := VSet.remove v ac' in
gpr_helper_trace fn f' l ac'' g' (Push u v f' ac'::tr)
| None =>
match relabel fn f l u with
| None => (None, RelabelFailed::tr)
| Some l' =>
gpr_helper_trace fn f l' ac g' (Relabel u (NMap.find 0 l' u)%nat l'::tr)
end
end
end
end.
Proof. destruct g; auto. Qed.

(* Teeb push-relabel algoritmi initsialiseerimise ühe sammu, milleks on
sisendtipust väljuvatele servadele voo saatmine, kasutades ära serva kogu läbilaskevõime. *)
Definition initial_push fn: (EMap.t Q*VSet.t) :=
let '((_, es),c,s,t) := fn in
let es' := ESet.to_list (ESet.filter (fun '(u,v) => T.eqb s u ) es) in
fold_left (fun '(f, ac) '(u,v) =>
let f' := EMap.replace (u,v) (c u v) f in
let ac :=
if has_excess_not_sink fn f' v then
(VSet.add v ac)
else
ac
in
(f', ac)
) es' (EMap.empty, VSet.empty) .

(* Algväärtustab graafi, muutes tippude kõrgused nii, et tipp s on kõrgusega length vs ja kõik teised tipud kõrgusega 0.
Seejärel toestab algse push sammu tipust s väljuvate servade peal.
Lõpus kutsutakse välja Fixpoint gpr_helper_trace, mis leiab maksimaalse voo ja tagastab leitud väärtuse funktsioonile gpr_trace.*)
Definition gpr_trace (fn:FlowNet): (option (EMap.t Q*NMap.t nat)*list Tr) :=
let '((vs, es),c,s,t) := fn in
let vs_size := VSet.size vs in
let labels := NMap.replace s vs_size NMap.empty in
let bound := (ESet.size es * vs_size * vs_size)%nat in
let '(f, active) := initial_push fn in
gpr_helper_trace fn f labels active bound (Init f labels active :: nil).

