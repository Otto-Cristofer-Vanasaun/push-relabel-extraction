Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.QOrderedType.
Require Import Coq.QArith.Qminmax.
Require Import Coq.QArith.QOrderedType.
Require Import Lia. (*tactic: lia*)
Require Import Lqa. (*tactic: lra*)
Require Import Coq.Arith.PeanoNat.  
From Coq Require Import QArith.
From Coq Require Import QArith.Qreduction.
Require Extraction.
Require Setoid.


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

Lemma snoc_distinct {t} xs: forall (a:t), 
    Distinct xs -> ~In a xs -> Distinct (xs ++ a::nil).
Proof.
    induction xs; simpl; auto. intros a0 [H1 H2] H3. 
    split; [|apply IHxs; tauto].
    intros H. apply in_app_or in H. destruct H; try contradiction.
    destruct H; subst; tauto.
Qed.

Lemma rev_distinct {t} (xs:list t): Distinct xs -> Distinct (rev xs).
Proof.
    induction xs; intros; auto. destruct H. 
    simpl. apply snoc_distinct; auto.
    intro W. apply in_rev in W. tauto.
Qed.

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


    Lemma FindRemoveEq {e d} {f:e->e} (xs:t e) u  :  
        find d (remove u xs) u = d.
    Proof.
        intros. induction xs.
        + simpl. reflexivity.
        + simpl. destruct a.
        - destruct (equal u v).
        * auto.
        * simpl. rewrite -> eqb_neq; auto.
        Qed.

    Lemma FindRemoveNeq {e d} (xs:t e) u v  : u<>v -> 
        find d (remove v xs) u = find d xs u .
    Proof.
        intros. induction xs; auto.
        simpl. destruct a. destruct (equal v v0).
        + destruct (equal u v0).
        - subst. contradiction.
        - auto.
        + simpl. rewrite -> IHxs. reflexivity.
        Qed. 

    Lemma FindUpdateEq {e d} {f:e->e} (xs:t e) u  :
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

    Lemma FindUpdateNeq {e d} {f:e->e} (xs:t e) u v  : u<>v -> 
        find d (update d v f xs) u = find d xs u .
    Proof.
        intros. induction xs.
        + simpl. destruct (equal u v); auto.
        - contradiction.
        + simpl. destruct a. destruct (equal v v0).
        - simpl. subst. rewrite eqb_neq; auto.
          rewrite -> FindRemoveNeq; auto.
        -  simpl. destruct (equal u v0); auto.
        Qed.
    
    Lemma FindReplaceEq {e d} {f:e} (xs:t e) u  :
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

    Lemma FindReplaceNeq {e d} {f:e} (xs:t e) u v  : u<>v -> 
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

    Parameter in_filter: forall v (p:V->bool) s, (v ∈ (filter p s)) = true -> (v ∈ s) = true  /\ p v = true.

    Parameter filter_in: forall v (p:V->bool) s, (v ∈ s)  = true -> p v = true -> (v ∈ (filter p s)) = true.

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
        +   inv_clear H.
        +   destruct (p a) eqn:E.
        ++  inv_clear H. split; try tauto. cbn.
            rewrite eqb_refl. reflexivity. 
        ++  apply IHvs in H. destruct H.
            split; auto. cbn. destruct (eqb v a) eqn:G; auto.
    Qed.

    Lemma find_first_specNone: forall p vs, 
        find_first p vs = None -> forall v, v ∈ vs = true -> p v = false .
    Proof.
        intros p vs H. induction vs; intros.
        +   inversion H0.
        +   cbn in *. destruct (p a) eqn:E; [inversion H|].
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
        intro H.  eapply H1, RemoveIn, H. 
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
        +   destruct (equal a v); cbn; subst; auto. tauto.
        +   destruct (equal a a0); cbn; subst; auto.
    Qed.

    Lemma to_list_in: forall v s, v ∈ s = true <-> In v (to_list s).
    Proof.
        intros v s. split; intros H.
        +   induction s; cbn; auto.
        ++  inversion H.
        ++  cbn in *. destruct (equal v a); subst; try tauto.
            right. apply InRemove; auto.
        +   induction s; [inversion H|]. cbn in *.
            destruct (equal v a);
            destruct H; subst; cbn; auto.
            eapply IHs, RemoveIn, H. 
    Qed.


    Lemma MemEmpty: forall v, v ∈ empty = false.
    Proof. intros. reflexivity. Qed.

    Lemma MemAddEq (xs:t) v  :
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

    Lemma MemRemoveNeq (xs:t) u v  : u<>v -> 
        u ∈ (remove v xs) = u ∈ xs.
    Proof.
        intros. induction xs; auto.
        simpl. destruct (equal v a).
        + subst. destruct (equal u a); auto.
        + destruct (equal u a).
        - subst. simpl. rewrite eqb_refl; auto.
        - simpl. rewrite eqb_neq; auto.
        Qed.

    Lemma MemAddNeq (xs:t) u v  : u<>v -> 
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
        ** subst. simpl.  rewrite eqb_refl; auto.
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
    
    Lemma in_filter v (p:V->bool) s : (v ∈ (filter p s)) = true -> (v ∈ s)  = true  /\ p v = true.
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

    Lemma filter_in v (p:V->bool) s : (v ∈ s)  = true -> p v = true -> (v ∈ (filter p s)) = true.
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


Module Type Product (A:T) (B:T) <: T.
Definition V := (A.V * B.V)%type.
Parameter eqb: V -> V -> bool.
Parameter equal: forall x y, reflect (x=y) (eqb x y).
Lemma eqb_refl u: eqb u u = true.
Proof. destruct (equal u u); auto. Qed. 
Lemma eqb_neq u v: u<>v -> eqb u v = false.
Proof. intros. destruct (equal u v); auto. contradiction. Qed. 
End Product.

Module Tuple (T U:T) <: Product (T) (U).
    Definition V := (T.V * U.V)%type.
    Definition eqb '(a,b) '(c,d) := T.eqb a c && U.eqb b d.
    Definition equal (x y:V): reflect (x=y) (eqb x y).
    Proof. 
        destruct x, y. simpl. 
        destruct (T.equal v v1), (U.equal v0 v2); subst; 
            simpl; constructor; intuition; inversion H; auto.
    Defined.
    Lemma eqb_refl u: eqb u u = true.
    Proof. destruct (equal u u); auto. Qed. 
    Lemma eqb_neq u v: u<>v -> eqb u v = false.
    Proof. intros. destruct (equal u v); auto. contradiction. Qed. 
End Tuple.

Module PR 
    (T:T) 
    (Edge : Product (T) (T)) 
    (EMap : MapSpec (Edge))
    (VSet : SetSpec (T))
    (ESet : SetSpec (Edge) )
    (NMap : MapSpec (T))
    .
(* Sisend *)

    Import T.
    Definition R := Q.

    Notation "v '∈v' s" := (VSet.mem v s) (at level 12). 
    Notation "v '∈e' s" := (ESet.mem v s) (at level 12). 

    (* Graaf, mis koosneb tippude ja servade hulkadest*)
    Definition Graph := (VSet.t * ESet.t)%type.

    (* Transpordivõrk kujul (Graaf, serva läbilaskevõime, algustipp, lõpptipp)*)
    Definition FlowNet := (Graph * (V -> V -> R) * V * V)%type.

    Definition nodes (fn:FlowNet) := 
        let '((vs, es),c,s,t) := fn in vs.

    Definition edges (fn:FlowNet) := 
        let '((vs, es),c,s,t) := fn in es.

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
    Defined.

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
            Qred(
            QSumList (map (fun v => EMap.find 0 f (v,u)) (VSet.to_list vs)) -
            QSumList (map (fun v => EMap.find 0 f (u,v)) (VSet.to_list vs))) .
    
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

    Definition E (fn: FlowNet) (f: EMap.t R)  :=
        let '((vs, es),c,s,t) := fn in
        ESet.filter (fun '(u, v) => EMap.find 0 f (u,v) <? c u v) es.    
    
    Definition res_net (fn: FlowNet) (f: EMap.t R)  : FlowNet :=
        let '((vs, es),c,s,t) := fn in
        ((vs,E fn f),res_cap fn f,s,t).

    (* valib tipu u ülejäägist ning läbilaskevõimest Qmin abil miinimumi ja saadab selle voona edasi järgmisesse tippu v.
     Kui (u,v) ∈e es ehk serv (u, v) kuulub hulka es tagastab true, siis suurendatakse serva (u, v) voogu delta võrra. 
     False korral vähendatakse serva (v, u) voogu delta võrra. *)
    Definition push fn f (exMap: NMap.t R) u v : (EMap.t R * NMap.t R) :=
        let '((vs, es),c,s,t) := fn in
        let delta := Qmin (NMap.find 0 exMap u) (res_cap fn f u v) in
        let exMap' := NMap.update (Qred 0) v (fun x=>Qred (x+delta)) 
            (NMap.update (Qred 0) u (fun x=>Qred (x-delta)) exMap) in
        if (u,v) ∈e es  then
            let f' := EMap.update 0 (u,v) (fun x=>Qred (x+delta)) f in
            (f', exMap')
        else 
            let f' := EMap.update 0 (v,u) (fun x=>Qred (x-delta)) f in
            (f', exMap')
    .
    
    Definition option_min (x:option nat) (y:nat): option nat :=
        match x with
        | None => Some y
        | Some a => Some (min a y)
        end.

    Fixpoint smallest_rank l xs r :=
        match xs, r with
        | nil, _ => r
        | v::xs, None   => smallest_rank l xs (Some v)
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
    Definition has_excess_not_sink (fn:FlowNet) (exMap:NMap.t R) v : bool :=
        let '((vs, es),c,s,t) := fn in
        if T.eqb v t || T.eqb v s then
            false
        else if 0 <? NMap.find (Qred 0) exMap v then 
            true
        else
            false
    .

    Definition tracing_on := true .

    Inductive Tr : Type :=
        | Init: EMap.t Q -> NMap.t nat -> VSet.t ->  Tr
        | Push: V -> V -> EMap.t Q -> VSet.t ->  Tr
        | Relabel : V -> nat -> NMap.t nat ->  Tr
        | OutOfGas
        | RelabelFailed
        .

    (* Leiab graafis maksimaalse voo, kasutades push ja relabel samme, ning tagastab selle, juhul kui graafis pole tippe või servasid, siis tagastab väärtuse None. *)
    Fixpoint gpr_helper_trace fn f l (exMap:NMap.t R) ac g tr: (option (EMap.t Q*NMap.t nat*NMap.t R)*list Tr) :=
        let '((vs, es),c,s,t) := fn in
        match g with
        | O => (None, OutOfGas::tr)
        | S g' => 
            match VSet.choice ac with
            | None => (Some (f,l,exMap),tr)
            | Some (u,ac') =>
            match find_push_node fn f l u vs with
            | Some v =>
                let (f',exMap') := push fn f exMap u v in
                let ac' := if 0 <? (NMap.find (Qred 0) exMap' u) then ac else ac' in
                if has_excess_not_sink fn exMap' v  then 
                    let ac'' := VSet.add v ac' in
                    gpr_helper_trace fn f' l exMap' ac'' g' (Push u v f' ac''::tr)
                else 
                    let ac'' := VSet.remove v ac' in
                    gpr_helper_trace fn f' l exMap' ac'' g' (Push u v f' ac'::tr)
            | None =>
                match relabel fn f l u with
                | None => (None, RelabelFailed::tr)
                | Some l' =>
                    gpr_helper_trace fn f l' exMap ac g' (Relabel u (NMap.find 0 l' u)%nat l'::tr)
                end
            end
            end 
        end.
    
    Lemma gpr_helper_trace_fn fn f l exMap ac g tr : 
        gpr_helper_trace fn f l exMap ac g tr =
            let '((vs, es),c,s,t) := fn in
        match g with
        | O => (None, OutOfGas::tr)
        | S g' => 
            match VSet.choice ac with
            | None => (Some (f,l,exMap),tr)
            | Some (u,ac') =>
            match find_push_node fn f l u vs with
            | Some v =>
                let (f',exMap') := push fn f exMap u v in
                let ac' := if 0 <? (NMap.find (Qred 0) exMap' u) then ac else ac' in
                if has_excess_not_sink fn exMap' v  then 
                    let ac'' := VSet.add v ac' in
                    gpr_helper_trace fn f' l exMap' ac'' g' (Push u v f' ac''::tr)
                else 
                    let ac'' := VSet.remove v ac' in
                    gpr_helper_trace fn f' l exMap' ac'' g' (Push u v f' ac'::tr)
            | None =>
                match relabel fn f l u with
                | None => (None, RelabelFailed::tr)
                | Some l' =>
                    gpr_helper_trace fn f l' exMap ac g' (Relabel u (NMap.find 0 l' u)%nat l'::tr)
                end
            end
            end 
        end.
    Proof. destruct g; auto. Qed.

    Definition initial_push_step fn '(f, ac, exMap) '(u, v) :=
        let '((_, es),c,s,t) := fn in
        let f' := EMap.update 0 (u,v) (fun x=>Qred (x+c u v)) f in
        let exMap' := NMap.update (Qred 0) v (fun x=>Qred (x+c u v)) 
            (NMap.update (Qred 0) u (fun x=>Qred (x-c u v)) exMap) in
        let ac' := 
            if has_excess_not_sink fn exMap' v then 
                (VSet.add v ac) 
            else 
                ac 
        in
        (f', ac', exMap').

    (* Teeb push-relabel algoritmi initsialiseerimise ühe sammu, milleks on 
    sisendtipust väljuvatele servadele voo saatmine, kasutades ära serva kogu läbilaskevõime. *)
    Definition initial_push fn: (EMap.t Q*VSet.t*NMap.t R) :=
        let '((_, es),c,s,t) := fn in
        let es' := ESet.to_list (ESet.filter (fun '(u,v) => T.eqb s u ) es) in
        let start_st := (EMap.empty, VSet.empty, NMap.empty) in
        fold_left (initial_push_step fn) es' start_st.


    (* Algväärtustab graafi, muutes tippude kõrgused nii, et tipp s on kõrgusega length vs ja kõik teised tipud kõrgusega 0. 
    Seejärel toestab algse push sammu tipust s väljuvate servade peal. 
    Lõpus kutsutakse välja Fixpoint gpr_helper_trace, mis leiab maksimaalse voo ja tagastab leitud väärtuse funktsioonile gpr_trace.*)
    Definition gpr_trace (fn:FlowNet): (option (EMap.t Q*NMap.t nat*NMap.t R)*list Tr) :=
        let '((vs, es),c,s,t) := fn in
        let vs_size := VSet.size vs in
        let labels := NMap.replace s vs_size NMap.empty in
        let bound := (ESet.size es * vs_size * vs_size)%nat in
        let '(f, active, excess) := initial_push fn in
        gpr_helper_trace fn f labels excess active bound (Init f labels active :: nil).

    
    (* Iga serva korral ei ole voog suurem kui läbilaskevõime *)
    Definition CapacityConstraint (fn:FlowNet) (f:EMap.t Q) := 
        let '((vs, es),c,s,t) := fn in
        forall u v, ESet.mem (u,v) es = true -> 
            EMap.find 0 f (u,v) <= c u v.
    
    (* Tagastab true, kui igas tipus v, mis ei ole sisend, on ülejääk mittenegatiivne *)
    Definition NonDeficientFlowConstraint (fn:FlowNet) (f:EMap.t Q) := 
        let '((vs, es),c,s,t) := fn in
        forall v, (v ∈v vs) = true -> v<>s -> 0 <= excess fn f v.

    Definition ExcessCached (fn:FlowNet) (f:EMap.t Q) (exMap:NMap.t R) := 
        let '((vs, es),c,s,t) := fn in
        forall v, excess fn f v = NMap.find (Qred 0) exMap v.

    (* Tagastab true kui igas tipus v.a sisendis ja väljundis on ülejääk 0.  *)
    Definition FlowConservationConstraint (fn:FlowNet) (f:EMap.t Q) := 
        let '((vs, es),c,s,t) := fn in
        forall v, (v ∈v vs) = true -> v<>s -> v<>t -> excess fn f v == 0.
    
    (* Tagastab true kui on täidetud eelvoo nõuded *)
    Definition PreFlowCond (fn:FlowNet) (f:EMap.t Q ) := 
            CapacityConstraint fn f /\ NonDeficientFlowConstraint fn f. 

    (* Tagastab true kui voog ja läbilaskevõime on mittenegatiivsed *)
    Definition FlowMapPositiveConstraint (fn:FlowNet) (f:EMap.t Q) := 
        let '((vs, es),c,s,t) := fn in
        forall u v, EMap.find 0 f (u,v) >= 0 /\ c u v >= 0.
    
    (* Tagastab true, kui tipp v on tippude hulgas ja omab ülejääki *)
    Definition ActiveNode (fn:FlowNet) (f:EMap.t Q)v := 
        let '((vs, es),c,s,t) := fn in
        (v ∈v vs) = true /\ excess fn f v > 0.


    (* Tagastab true, kui iga tipu u ja v korral, kui serv (u ,v) kuulub servade hulka on tippudel u ja v korrektsed kõrgused *)
    Definition ValidLabeling  fn (f:EMap.t Q) (l:NMap.t nat) :=
        forall u v,
        let '((vs, es),c,s,t) := fn in
        ((u,v) ∈e E fn f) = true  ->  (NMap.find 0 l u <= NMap.find 0 l v + 1)%nat.

    Inductive CPath (fn:FlowNet) (f:EMap.t Q): V -> V -> Prop :=
    | Start u : CPath fn f u u
    | Step u v1 vn: ((u,v1) ∈e E fn f) = true -> CPath fn f v1 vn ->  CPath fn f u vn
    .

    (* Graafis ei leidu enam täiendavaid teid *)
    Definition NoAugPath (fn:FlowNet) (f:EMap.t Q) := 
        let '((vs, es),c,s,t) := fn in
        CPath fn f s t -> False.

    (* Tagastab true, kui iga tipu u ja v korral on täidetud tingimus cf (u, v) > 0, siis l(u) <= l(v) + 1 *)
    Definition NoSteepArc (fn:FlowNet) (f:EMap.t Q) (l:NMap.t nat):=
        forall u v,
        res_cap fn f u v > 0 -> (NMap.find 0 l u <= NMap.find 0 l v+1)%nat.

    (* Tagastab true iga tipu u ja v korral kui on täidetud tingimus cf (u, v) > 0 ja tipud u ja v kuuluvad transpordivõrku *)
    Definition ResCapNodes (fn:FlowNet) (f:EMap.t Q) :=
            forall u v,
            res_cap fn f u v > 0 -> u ∈v (nodes fn) = true /\ v ∈v (nodes fn) = true.

    (* Tagastab true, kui ei leidu tippu, kuhu saaks push sammu teha *)
    Definition NoPushCondition fn (f:EMap.t Q) (l:NMap.t nat) u := 
                forall v, v ∈v (nodes fn) = true -> (NMap.find 0 l u <> NMap.find 0 l v + 1)%nat.
    
    (* Tagastab true, kui push sammu eeldused on täidetud, ehk tipus on ülejääk ja järgmine tipp on 1 võrra madalamal *)
    Definition PushCondition fn (f:EMap.t Q) (l:NMap.t nat) u v := 
        excess fn f u > 0 /\ (NMap.find 0 l u = NMap.find 0 l v + 1)%nat.
    
    (* Kui tippudel olid korrektsed kõrgused enne push sammu, siis ka peale push sammu on tippudel korrektsed kõrgused *)
    Lemma PushValidLabel fn (f:EMap.t Q) (exMap:NMap.t R) (l:NMap.t nat) x y:
        let '((vs, es),c,s,t) := fn in
        ExcessCached fn f exMap ->
        ValidLabeling fn f l -> PushCondition fn f l x y
                -> ValidLabeling fn (fst (push fn f exMap x y)) l.
    Proof.
        intros. destruct fn as [[[[vs es] c] s] t]. unfold ValidLabeling, PushCondition, ExcessCached. 
        intros Hex H H0 u v H1. unfold push in H1.
        repeat rewrite <- Hex in H1. 
        destruct ((x, y) ∈e es) eqn : E.
        + unfold PR.E, fst in *. apply ESet.in_filter in H1. destruct H1.  
        apply H. apply ESet.filter_in.
        - auto.
        - destruct (Edge.equal (x,y) (u, v)).
        * inversion e. subst. rewrite EMap.FindUpdateEq in H2. 
        eapply (reflect_iff _ _ (QLt_spec _ _)). 
        eapply (reflect_iff _ _ (QLt_spec _ _)) in H2.
        unfold res_cap in H2. rewrite E in H2.
        destruct ( Q.min_dec (excess (vs, es, c, s, t) f u) (c u v - EMap.find  0 f (u, v))).
        ** rewrite q in H2. rewrite Qred_correct in *.  lra.
        ** rewrite q in H2. unfold R in H2. 
            rewrite Qred_correct in *. lra.
        * rewrite EMap.FindUpdateNeq in H2; auto.
        + unfold PR.E, fst in *. apply ESet.in_filter in H1. destruct H1.
        destruct (Edge.equal (y, x) (u, v)).
        - inversion e. subst. lia.
        - rewrite EMap.FindUpdateNeq in H2; auto.
        apply H. apply ESet.filter_in; auto.
        Qed.

    Definition RelabelCondition fn (f:EMap.t Q) (l:NMap.t nat) u := 
      excess fn f u > 0 /\ forall v, v ∈v (nodes fn) = true -> res_cap fn f u v > 0 -> (NMap.find 0 l u <= NMap.find 0 l v)%nat.


    Lemma minProp: forall a b, (min a b = a /\ a <= b)%nat \/ 
                                (min a b = b /\ b <= a)%nat.
    Proof. lia. Qed. 


    Lemma RFindResCapCondition fn (f:EMap.t Q) (l:NMap.t nat) u vs : forall vs' v,
        (VSet.filter (fun v0 : V => 0 <? res_cap fn f u v0) vs) = vs' ->
        (v ∈v vs') = true ->  (0 <? res_cap fn f u v) = true .
    Proof.
        intros vs' v Hf Hi. rewrite <- Hf in Hi.
        eapply VSet.in_filter in Hi. tauto.
    Qed. 

    Lemma smallest_rank_In: forall l xs r v,
        smallest_rank l xs (Some r) = Some v -> In v (r::xs).
    Proof.
        intros l xs. induction xs; cbn; intros; auto.
        +   inv_clear H. tauto.
        +   destruct (NMap.find 0 l r <=? NMap.find 0 l a)%nat.
        ++  apply IHxs in H. cbn in H. tauto.
        ++  apply IHxs in H. cbn in H. tauto.   
    Qed.

    Lemma smaller_rank_leq: forall l xs v0 v v' ,
        smallest_rank l xs (Some v0) = Some v ->
        (In v' xs \/ (NMap.find 0 l v0 <= NMap.find 0 l v')%nat) ->
        (NMap.find 0 l v <= NMap.find 0 l v')%nat.
    Proof.
        intros l xs. induction xs; intros v0 v v' Hs H; cbn in *.
        +   inv_clear Hs. destruct H; auto. inv_clear H.
        +  destruct (Nat.leb_spec0 (NMap.find 0 l v0)%nat (NMap.find 0 l a)%nat).
        ++  eapply IHxs with (v':=v')in Hs; auto.
            destruct H; try lia. 
            destruct H; subst; try lia.
            tauto.
        ++  eapply IHxs with (v':=v')in Hs; auto.
            destruct H; try lia. 
            destruct H; subst; try lia.
            tauto.
    Qed.

    Lemma RFindCondition fn (f:EMap.t Q) (l:NMap.t nat) u vs: forall v, 
      relabel_find fn f l u vs = Some v  ->
      (0 <? res_cap fn f u v) = true /\ (forall v', (v' ∈v vs) = true 
        -> (0 <? res_cap fn f u v') = true -> (NMap.find 0 l v <= NMap.find 0 l v')%nat).
    Proof.
    intros. unfold relabel_find in H. split.
    +   destruct (VSet.to_list (VSet.filter (fun v => 0<?res_cap fn f u v) vs)) eqn:E.
    ++  cbn in H. inversion H.  
    ++  cbn in H. apply smallest_rank_In in H.
        rewrite <- E in H.
        apply VSet.to_list_in in H. 
        apply VSet.in_filter in H. tauto.
    +   intros.
        destruct (VSet.to_list (VSet.filter (fun v => 0<?res_cap fn f u v) vs)) eqn:E.
    ++  cbn in H. inversion H.
    ++  cbn in H.
        eapply VSet.filter_in  with (p:=(fun v : V => 0 <? res_cap fn f u v)) in H0; auto.
        apply VSet.to_list_in in H0.
        rewrite E in H0. clear E.
        cbn in H0. destruct H0.
    +++ subst. clear -H. generalize dependent v'.
        induction l0; intros v' H.
        *   cbn in H. inv_clear H. lia.
        *   cbn in H.
            destruct ((NMap.find 0 l v' <=? NMap.find 0 l a)%nat) eqn:E.
        **  apply IHl0, H.
        **  destruct (Nat.leb_spec0 (NMap.find 0 l v')%nat (NMap.find 0 l a)%nat);
            [inversion E|].
            specialize (IHl0 _ H). lia.
    +++ eapply smaller_rank_leq; eauto.
    Qed.

    Lemma RFindMemCondition fn f (l:NMap.t nat) u vs: forall v, 
        relabel_find fn f l u vs = Some v ->
            (v ∈v vs) = true.
    Proof.        
        intros. unfold relabel_find in H. 
        set (xs:=VSet.to_list _) in H.
        destruct xs eqn:E.
        + simpl in H. inversion H.
        + simpl. cbn in H. apply smallest_rank_In in H.
          rewrite <- E in H.
          apply VSet.to_list_in in H.
          apply VSet.in_filter in H. tauto.
    Qed.

    (* Kui enne relabel sammu olid tippudel korrektsed kõrgused, siis peale relabel sammu on samuti tippudel korrektsed kõrgused *)
    Lemma RelabelValidLabel fn (f:EMap.t Q) (l:@NMap.t nat) x l':
        let '((vs, es),c,s,t) := fn in
        (forall u v, ((u, v) ∈e es = true) -> (u ∈v vs) = true /\ (v ∈v vs) = true) ->
        ValidLabeling fn f l -> RelabelCondition fn f l x 
            -> relabel fn f l x = Some l' -> ValidLabeling fn f l'.
    Proof.
        intros. destruct fn as [[[[vs es] c] s] t]. unfold ValidLabeling, RelabelCondition.
        intros R. intros. unfold relabel in H1. 
        destruct (relabel_find (vs, es, c, s, t) f l x vs) eqn:E0;
            [| inversion H1].
        inversion H1. clear H1 H4. apply H in H2 as P. unfold PR.E in H2. 
        apply ESet.in_filter in H2. destruct H2. destruct H0. 
        apply RFindMemCondition in E0 as P1. apply RFindCondition in E0.
        destruct E0. eapply (reflect_iff _ _ (QLt_spec _ _)) in H4. apply H3 in H4 as P2.
        destruct (equal x u); destruct (equal x v); subst.
        + erewrite -> NMap.FindReplaceEq. lia.
        + erewrite -> NMap.FindReplaceEq; erewrite -> NMap.FindReplaceNeq. 
        - assert ((NMap.find 0 l v0) <= NMap.find 0 l v)%nat. { apply H5. + edestruct R; eauto. + unfold res_cap.
        rewrite H1. eapply (reflect_iff _ _ (QLt_spec _ _)).
        eapply (reflect_iff _ _ (QLt_spec _ _)) in H2. lra.
        } lia.
        - symmetry. auto.
        + erewrite -> NMap.FindReplaceEq; erewrite -> NMap.FindReplaceNeq.
        - lia.
        - symmetry; auto.
        + erewrite -> NMap.FindReplaceNeq. 
        - erewrite -> NMap.FindReplaceNeq. lia. symmetry; auto.
        - symmetry; auto.
        + auto.
    Qed.

    (* Kui tippudel on korrektsed kõrgused ning leidub aktiivseid tippe ja leidub tipp kuhu saab push sammu teha, siis järledub, et 
    on täidetud push sammu eeldused. *)
    Lemma FPNCondition fn f l u vs': 
        (u ∈v nodes fn) = true -> forall v, 
        ValidLabeling fn f l -> ActiveNode fn f u ->
        find_push_node fn f l u vs' = Some v -> PushCondition fn f l u v.
    Proof.
        unfold PushCondition, ValidLabeling, ActiveNode. intros. 
        destruct fn as [[[[vs es] c] s] t]. split.
        + apply H1; apply H.
        +   unfold find_push_node in H2.
            apply VSet.find_first_specSome in H2.
            destruct H2. apply andb_true_iff in H2.
            destruct H2. 
            destruct (Nat.eqb_spec (NMap.find 0%nat l u) (1 + NMap.find 0%nat l v)); [|inversion H2]. 
            lia.
    Qed.

    Lemma map_fn A B (f:A->B) x xs : map f (x::xs) =  f x :: map f xs.
    Proof. reflexivity. Qed.

    Lemma SumSame (f:EMap.t Q) (s:V->V*V) vs u v d : 
        (forall v0,  In v0 vs -> s v0 <> (u, v)) ->
        map (fun v0 => EMap.find 0 
            (EMap.update 0 (u, v) (fun x0 => Qred (x0 + d)) f) 
            (s v0)) vs = 
        map (fun v0 => EMap.find 0 f (s v0)) vs.
    Proof.
        induction vs; intros.
        + simpl. auto.
        +   do 2 rewrite map_fn.
            erewrite IHvs.
        ++  f_equal. erewrite EMap.FindUpdateNeq; auto.
            apply H. cbn. auto.
        ++  intros. apply H. constructor 2. auto.
    Qed.
    
    Lemma PushActiveCondition (fn:FlowNet) (f:EMap.t R ) (exMap:NMap.t R) u v x: 
        ActiveNode fn f x -> x<>v -> x<>u -> ActiveNode fn (fst (push fn f exMap u v)) x .
        Proof.
            unfold ActiveNode. destruct fn as [[[[vs es] c] s] t]. intros. destruct H. split; auto.
            unfold push. destruct ((u, v) ∈e es) eqn : E.
            + unfold excess, fst in *. 
                set (d := Qmin _ _). 
                rewrite Qred_correct in *. rewrite SumSame.
            - rewrite SumSame.
            * apply H2. 
            * intros v0 _ q. inversion q. subst. apply H1. auto.
            - intros v0 _ q. inversion q. subst. apply H0. auto. 
            +  set (d := Qmin _ _). unfold excess, fst. unfold Qminus. rewrite SumSame.
            - rewrite SumSame.
            * apply H2.
            * intros v0 _ q. inversion q. subst. apply H0. auto.
            - intros v0 _ q. inversion q. subst. apply H1. auto. 
    Qed.

    
    Lemma DeltaPositive fn (f:EMap.t Q) (l:NMap.t nat) u v:
        let '((vs, es),c,s,t) := fn in
        (u ∈v vs) = true -> 
        FlowMapPositiveConstraint fn f ->
        PreFlowCond fn f -> 
        PushCondition fn f l u v ->
        Qmin (excess fn f u) (res_cap fn f u v) >= 0.
    Proof.
        unfold FlowMapPositiveConstraint, PreFlowCond, PushCondition.
        destruct fn as [[[[vs es] c] s] t]. unfold CapacityConstraint, NonDeficientFlowConstraint.
        intros. destruct H2. edestruct (Q.min_spec_le); destruct H4; rewrite H5; try lra.
        unfold res_cap. destruct ((u, v) ∈e es) eqn : E.
        + destruct H1. specialize (H1 _ _ E). unfold R in *. lra.
        + apply H0.
    Qed.

    Lemma PushFlowMapPos fn (f:EMap.t Q) (exMap:NMap.t R) (l:NMap.t nat) x y:
        let '((vs, es),c,s,t) := fn in
        (x ∈v vs) = true ->
        ExcessCached fn f exMap ->
        FlowMapPositiveConstraint fn f -> 
        PreFlowCond fn f ->
        PushCondition fn f l x y ->
        FlowMapPositiveConstraint fn (fst (push fn f exMap x y)).
    Proof.
        unfold FlowMapPositiveConstraint, PreFlowCond, PushCondition.
        unfold CapacityConstraint, NonDeficientFlowConstraint, ExcessCached.
        destruct fn as [[[[vs es] c] s] t]. 
        intros H Hex H0 H1 H2 u v. split.
        + unfold push. repeat rewrite <- Hex.
         destruct ((x, y) ∈e es) eqn : E.
        - destruct (Edge.equal (x,y) (u,v)).
        * inv_clear e. unfold fst. rewrite EMap.FindUpdateEq.
        eapply (DeltaPositive ((vs, es),c,s,t)) in H2; auto.
        specialize (H0 u v). rewrite Qred_correct. lra.
        * unfold fst. rewrite EMap.FindUpdateNeq; auto.
        apply H0.
        - destruct (Edge.equal (y,x) (u,v)).
        * inv_clear e. unfold fst. rewrite EMap.FindUpdateEq.
        unfold res_cap. rewrite E. edestruct (Q.min_spec_le); destruct H3.
        ** erewrite H4. unfold R in *. rewrite Qred_correct. lra.
        ** erewrite H4. unfold R in *. rewrite Qred_correct. lra.
        * unfold fst. rewrite EMap.FindUpdateNeq; auto.
            apply H0.
            + apply H0.
    Qed.        

    Lemma QSumListFn x xs: QSumList (x::xs) = x + QSumList xs.
    Proof. reflexivity. Qed.

    Lemma SumInR (f:EMap.t Q ) vs u v d : 
        Distinct vs ->
        In u vs ->
        QSumList (
            map (fun v0 => EMap.find 0
                  (EMap.update 0 (u, v) (fun x0 => Qred (x0 + d)) f) 
                  (v0, v)) vs) == 
        QSumList (map (fun v0 => EMap.find 0 f (v0, v)) vs) + d.
    Proof. 
        induction vs; intros.
        + simpl. inversion H0.
        + do 2 rewrite map_fn. destruct (equal u a).
        - subst. rewrite EMap.FindUpdateEq. erewrite SumSame.
        *   do 2 rewrite QSumListFn.
            unfold R in *. rewrite Qred_correct.  lra.
        * intros. intro C. inv_clear C. inv_clear H. tauto. 
        - rewrite EMap.FindUpdateNeq.
        * do 2 rewrite QSumListFn. erewrite IHvs.
        ** lra.
        ** inversion H. auto.
        **  simpl in H0.
            destruct H0; subst; try tauto.
        * intro C. inv_clear C. apply n. reflexivity.
    Qed. 

    Lemma SumInL (f:EMap.t Q ) vs:  forall u v d,
        Distinct vs ->
        In v vs ->
        QSumList (
            map (fun v0 => EMap.find 0
                  (EMap.update 0 (u, v) (fun x0 => Qred (x0 + d)) f) 
                  (u, v0)) vs) == 
        QSumList (map (fun v0 => EMap.find 0 f (u, v0)) vs) + d.
    Proof. 
        induction vs; intros.
        + simpl. inversion H0.
        + do 2 rewrite map_fn. destruct (equal v a).
        - subst. rewrite EMap.FindUpdateEq. erewrite SumSame.
        *   do 2 rewrite QSumListFn.
            unfold R in *. rewrite Qred_correct.  lra.
        * intros. intro C. inv_clear C. inv_clear H. tauto. 
        - rewrite EMap.FindUpdateNeq.
        * do 2 rewrite QSumListFn. erewrite IHvs.
        ** lra.
        ** inversion H. auto.
        **  simpl in H0.
            destruct H0; subst; try tauto.
        * intro C. inv_clear C. apply n. reflexivity.
    Qed. 

    Lemma SumNoL: forall f vs v t c s, s <> v ->
        QSumList (map (fun v0 : V => EMap.find 0 (EMap.replace (v, t) c f) (s,v0)) vs) = QSumList (map (fun v0 : V => EMap.find 0 f (s,v0)) vs).
    Proof.
        intros f vs. induction vs; intros; cbn; auto.
        assert ((s, a) <> (v, t)). { 
            intro q. inv_clear q. tauto. 
        }
        rewrite EMap.FindReplaceNeq; auto.
        eapply (IHvs v t c) in H. rewrite H. 
        reflexivity.
    Qed.

    Lemma SumNoUpdateL: forall f vs v t c s, s <> v ->
        QSumList (map (fun v0 : V => EMap.find 0 (EMap.update 0 (v, t) c f) (s,v0)) vs) = QSumList (map (fun v0 : V => EMap.find 0 f (s,v0)) vs).
    Proof.
        intros f vs. induction vs; intros; cbn; auto.
        assert ((s, a) <> (v, t)). { 
            intro q. inv_clear q. tauto. 
        }
        rewrite EMap.FindUpdateNeq; auto.
        eapply (IHvs v t c) in H. rewrite H. 
        reflexivity.
    Qed.

    Lemma SumNoUpdateR: forall f vs v t c s, t <> v ->
        QSumList (map (fun v0 : V => EMap.find 0 (EMap.update 0 (s, v) c f) (v0, t)) vs) = QSumList (map (fun v0 : V => EMap.find 0 f (v0,t)) vs).
    Proof.
        intros f vs. induction vs; intros; cbn; auto.
        assert ((a, t) <> (s, v)). { 
            intro q. inv_clear q. tauto. 
        }
        rewrite EMap.FindUpdateNeq; auto.
        eapply (IHvs v t c) in H. rewrite H. 
        reflexivity.
    Qed.


    (* Kui on rahuldatud eelvoo tingimused ning vood ja läbilaskevõimed on mittenegatiivsed 
    ja leidub tipp, kuhu saab push sammu teha, siis järeldub, et ka peale push sammu on eelvoo tingimused säilitatud *)
    Lemma PushPreFlow fn (f:EMap.t Q) (exMap:NMap.t R) (l:NMap.t nat) x y:
        let '((vs, es),c,s,t) := fn in
        (* VSet.IsSet vs -> *)
        (x ∈v vs) = true ->
        (y ∈v vs) = true ->
        ExcessCached fn f exMap ->
        PreFlowCond fn f -> 
        FlowMapPositiveConstraint fn f ->
        PushCondition fn f l x y->
        PreFlowCond fn (fst (push fn f exMap x y)).
    Proof.
        unfold PreFlowCond, FlowMapPositiveConstraint, PushCondition, PreFlowCond, ExcessCached.
        unfold CapacityConstraint, NonDeficientFlowConstraint.
        destruct fn as [[[[vs es] c] s] t].
        intros Hxvs Hyvs Hex [Hcc Hndf] Hfmp Hpc.
        split.
        + intros. unfold push.
        repeat rewrite <- Hex. destruct ((x, y) ∈e es) eqn : E.
        - destruct (Edge.equal (x,y) (u,v)). 
        * inv_clear e. unfold fst. rewrite EMap.FindUpdateEq. unfold res_cap.
        rewrite E. edestruct (Q.min_spec_le); destruct H0.
        ** erewrite H1. unfold R in *. rewrite Qred_correct. lra.
        ** erewrite H1. unfold R in *. rewrite Qred_correct. lra.
        * unfold fst. rewrite EMap.FindUpdateNeq; auto.
        - unfold res_cap. rewrite E. destruct (Edge.equal (y,x) (u,v)).
        * inv_clear e. unfold fst. rewrite EMap.FindUpdateEq. edestruct (Q.min_spec_le); destruct H0.
        ** erewrite H1. specialize (Hcc _ _ H). 
            rewrite Qred_correct. lra.
        ** rewrite H1. specialize (Hfmp u v). unfold R in *. 
            rewrite Qred_correct. lra.
        * unfold fst. rewrite EMap.FindUpdateNeq; auto.
        +   intros. 
            pose proof (L1:=VSet.to_list_distinct vs).
            apply VSet.to_list_in in H as L2.
            apply VSet.to_list_in in Hxvs as L3.
            apply VSet.to_list_in in Hyvs as L4.
            eapply (DeltaPositive ((vs, es),c,s,t)) in Hpc as HDp; auto;
            unfold PreFlowCond, CapacityConstraint, NonDeficientFlowConstraint; auto.
        unfold push, res_cap in *. 
        repeat rewrite <- Hex.
         destruct ((x, y) ∈e es) eqn : E.
        -   unfold excess at 1. destruct (equal v y). 
        * subst. destruct (equal x y).
        ** subst. unfold fst.
            rewrite SumInR; auto.
            rewrite SumInL; auto. destruct Hpc. unfold excess in H1.
            unfold R in *. rewrite Qred_correct in *. lra.
        ** unfold fst. rewrite SumInR; auto. 
        rewrite SumSame.
        **** specialize (Hndf y H H0). unfold excess in Hndf.
         unfold R in *. rewrite Qred_correct in *. lra.
         **** intros. intro C. inv_clear C. apply n. reflexivity.
         * unfold excess in Hpc. destruct (equal x v). 
         ** subst. unfold fst. rewrite SumSame. 
         *** erewrite SumInL; auto.
          edestruct (Q.min_spec_le); destruct H1.
         **** erewrite H2 in *. unfold excess. unfold R in *. 
              repeat rewrite Qred_correct in *. lra.
         **** erewrite H2 in *. unfold excess in H1. unfold R in *. 
            rewrite Qred_correct in *. lra.
         *** intros. intro C. inv_clear C. apply n. reflexivity.
         ** unfold fst. rewrite SumSame, SumSame.
         *** apply Hndf in H; auto.
         *** intros. intro C. inv_clear C. apply n0. reflexivity.
         *** intros. intro C. inv_clear C. apply n. reflexivity.  
         - unfold excess. unfold Qminus. destruct (equal v x).
         * subst. destruct (equal x y).
         ** subst. unfold fst. erewrite SumInL; auto.
         erewrite SumInR; auto.
         unfold excess in Hpc. unfold R in *. 
         rewrite Qred_correct in *. lra.
         ** unfold fst. erewrite SumInR; auto.
         erewrite SumSame.
         *** unfold excess in Hpc, HDp. rewrite Qred_correct in *.
         edestruct (Q.min_spec_le); destruct H1.
         **** erewrite H2 in *. unfold R in *. rewrite Qred_correct in *. lra.
         **** erewrite H2 in *. unfold R in *. rewrite Qred_correct in *. lra.
         *** intros. intro C. inv_clear C. apply n. reflexivity.
         * destruct (equal v y).
         ** subst. unfold fst. erewrite SumInL; auto.
         rewrite SumSame.
         *** apply Hndf in H; auto.
         unfold excess in H.
         rewrite Qred_correct in *.
         unfold excess, Qminus in HDp. unfold R in *. lra.
        *** intros. intro C. inv_clear C. apply n. reflexivity.
        ** unfold fst. erewrite SumSame, SumSame.
        *** apply Hndf in H; auto.
        *** intros. intro C. inv_clear C. apply n0. reflexivity.
        *** intros. intro C. inv_clear C. apply n. reflexivity.
    Qed.

    Lemma FPNinVs fn f l u v vs': 
        find_push_node fn f l u vs' = Some v -> (v ∈v vs') = true.
    Proof.
        destruct fn as [[[[vs es] c] s] t]. intros H. 
        unfold find_push_node in H. apply VSet.find_first_specSome in H as [_ H].
        auto.
    Qed.

    Lemma HENSCondition fn v :forall (exMap:NMap.t R),
        has_excess_not_sink fn exMap v = true -> 0 < NMap.find 0 exMap v /\ v <> sink fn /\ v <> source fn.
    Proof.
        unfold has_excess_not_sink. destruct fn as [[[[vs es] c] s] t].
        intros. destruct (equal v t), (equal v s)  in H. subst.
        + inversion H.
        + inversion H.
        + inversion H.
        + cbn in H. 
            set (q := 0 <? _) in H.
            destruct q eqn:E0.
        - eapply (reflect_iff _ _ (QLt_spec _ _)) in E0. split; auto.
        - inversion H. 
    Qed.

    Lemma PushActiveInv (fn:FlowNet) (f:EMap.t R) (exMap:NMap.t R) (l:NMap.t nat) u v x:
        u ∈v nodes fn = true ->
        v ∈v nodes fn = true ->
        x<>v ->
        ExcessCached fn f exMap ->
        PreFlowCond fn f ->
        FlowMapPositiveConstraint fn f ->
        PushCondition fn f l u v ->
        ActiveNode fn (fst (push fn f exMap u v)) x ->
        ActiveNode fn f x.
    Proof.
        unfold ActiveNode, push, PreFlowCond, 
        FlowConservationConstraint, PushCondition, ExcessCached.
        destruct fn as [[[[vs es] c] s] t].
        pose proof (H:= True).
        intros H0 H1 H2 Hex H3 H4 H5 H6.
        repeat rewrite <- Hex in H6.
        cbn in H0, H1.
        pose proof (L1:=VSet.to_list_distinct vs).
        apply VSet.to_list_in in H0 as L2.
        apply VSet.to_list_in in H1 as L3.
        destruct ((u, v) ∈e es) eqn:E0.
        + destruct H6. split; auto. 
        unfold excess in *.
        destruct (equal x u) in H7.
        -   subst. unfold fst in H7. 
            erewrite SumSame, SumInL in H7; auto.
        * unfold R in *. lra.
        * intros. intro C. inv_clear C. apply H2. reflexivity.
        - unfold fst in H7. erewrite SumSame, SumSame in H7.
        * unfold R in *. lra.
        * intros. intro C. inv_clear C. apply n. reflexivity.
        * intros. intro C. inv_clear C. apply H2. reflexivity.
        + destruct H6. split; auto. 
        unfold excess in *. unfold Qminus in *. set (d:= Qmin _ _) in *.
        destruct (equal x u) in H7.
        - subst. unfold fst in H7.  erewrite SumInR, SumSame in H7; auto.
        * unfold R in *. lra.
        * intros. intro C. inv_clear C. apply H2. reflexivity.
        - unfold fst in H7. erewrite SumSame, SumSame in H7; auto.
        * intros. intro C. inv_clear C. apply H2. reflexivity.
        * intros. intro C. inv_clear C. apply n. reflexivity.
    Qed.
    
    Lemma FPNConditionNone fn f l u vs': 
        find_push_node fn f l u vs' = None -> 
        forall v, v ∈v vs' = true -> (0 <? res_cap fn f u v = false) 
        \/ (NMap.find 0 l u <> NMap.find 0 l v + 1)%nat.
    Proof.
        destruct fn as [[[[vs es] c] s] t].
        intros H v Hvs. 
        unfold find_push_node in H.
        eapply VSet.find_first_specNone in H; eauto.
        apply andb_false_iff in H. destruct H; try tauto.
        destruct (Nat.eqb_spec (NMap.find 0%nat l u) (1 + NMap.find 0%nat l v)); lia.
    Qed. 

    Lemma HENSConditionFalse fn v :forall (exMap:NMap.t R),
        has_excess_not_sink fn exMap v = false -> 0 >= NMap.find 0 exMap v  \/ v = sink fn \/ v = source fn.
    Proof.
        unfold has_excess_not_sink.
        intros. destruct fn as [[[[vs es] c] s] t].
        destruct (equal v t), (equal v s); subst; auto.
        cbn in H. set (q := _ <? _) in H.
        destruct q eqn:E0; [inversion H|].
        unfold q in E0. apply QLt_false in E0. 
        cbn. left. apply E0.
    Qed.

    Lemma PushNoSteepArc fn f (exMap:NMap.t R) l x y:
        (x ∈v nodes fn) = true -> 
        ExcessCached fn f exMap ->
        FlowMapPositiveConstraint fn f ->
        PreFlowCond fn f -> 
        PushCondition fn f l x y ->
        NoSteepArc fn f l -> NoSteepArc fn (fst (push fn f exMap x y)) l.
    Proof.
        unfold FlowMapPositiveConstraint, PreFlowCond, PushCondition,
        NoSteepArc. unfold CapacityConstraint, NonDeficientFlowConstraint.
        unfold ExcessCached.
        destruct fn as [[[[vs es] c] s] t].
        intros H Hex H0 H1 H2 H3 u v H4 . unfold push,fst in H4.
        repeat rewrite <- Hex in H4.
        set (d:= Qmin _ _) in H4. 
        destruct ((x, y) ∈e es) eqn : E.
        + unfold res_cap in H4. destruct ((u, v) ∈e es) eqn : E2.
        - destruct (Edge.equal (u, v) (x, y)).
        * inv_clear e. lia.
        * apply H3. unfold res_cap. rewrite E2. rewrite EMap.FindUpdateNeq in H4; auto.
        - destruct (Edge.equal (v, u) (x, y)).
        * inv_clear e. lia.
        * rewrite EMap.FindUpdateNeq in H4; auto. 
        apply H3. unfold res_cap. rewrite E2. auto.
        + unfold res_cap in H4. destruct ((u, v) ∈e es) eqn : E2.
        - destruct (Edge.equal (u, v) (y, x)).
        * inv_clear e. lia.
        * rewrite EMap.FindUpdateNeq in H4; auto.
        apply H3. unfold res_cap. rewrite E2. auto.
        - destruct (Edge.equal (v, u) (y, x)).
        * inv_clear e. lia.
        * rewrite EMap.FindUpdateNeq in H4; auto.
        apply H3. unfold res_cap. rewrite E2. auto.
    Qed.

    Lemma PushResCapNodes fn f (exMap:NMap.t R) x y:        
        x ∈v (nodes fn) = true -> y ∈v (nodes fn) = true ->
        ExcessCached fn f exMap ->
        ResCapNodes fn f -> ResCapNodes fn (fst (push fn f exMap x y)).
    Proof.
        unfold ResCapNodes, ExcessCached.
        intros H H0 Hex H1 u v H2. 
        unfold push, fst in H2. destruct fn as [[[[vs es] c] s] t].
        repeat rewrite <- Hex in H2.
        set (d:= Qmin _ _) in H2. destruct ((x, y) ∈e es) eqn : E.
        + unfold res_cap in H2. destruct ((u, v) ∈e es) eqn : E2.
        - destruct (Edge.equal (u, v) (x, y)).
        * inv_clear e. tauto.
        * rewrite EMap.FindUpdateNeq in H2; auto.
        apply H1. unfold res_cap. rewrite E2. auto.
        -  destruct (Edge.equal (v, u) (x, y)).
        * inv_clear e. tauto.
        * rewrite EMap.FindUpdateNeq in H2; auto.
        apply H1. unfold res_cap. rewrite E2. auto.
        + unfold res_cap in H2. destruct ((u, v) ∈e es) eqn : E2.
        - destruct (Edge.equal (u, v) (y, x)).
        * inv_clear e. tauto.
        * rewrite EMap.FindUpdateNeq in H2; auto.
        apply H1. unfold res_cap. rewrite E2. auto.
        - destruct (Edge.equal (v, u) (y, x)).
        * inv_clear e. tauto.
        * rewrite EMap.FindUpdateNeq in H2; auto.
        apply H1. unfold res_cap. rewrite E2. auto.
    Qed.
    
    Lemma MapNil A B f : @map A B f nil = nil.
    Proof. reflexivity. Qed.

    Lemma QSumListNil : QSumList nil = 0.
    Proof. reflexivity. Qed.

    Definition excess_loop f u xs := 
        QSumList (map (fun v => EMap.find 0 f (v,u)) xs) -
            QSumList (map (fun v => EMap.find 0 f (u,v)) xs) .

    Lemma PushExcessCycle f xs x d z:
        excess_loop (EMap.update 0 (x,x) (fun x=>Qred (x+d)) f) z xs == excess_loop f z xs .
    Proof.
        (* intros z. *)
        destruct (equal x z); subst.
        +   unfold excess_loop.
            induction xs.
        ++  cbn. lra.
        ++  repeat rewrite map_fn.
            repeat rewrite QSumListFn. 
            destruct (equal a z); subst.
        +++ repeat rewrite EMap.FindUpdateEq. lra.  
        +++ rewrite EMap.FindUpdateNeq; [|intro C; inv_clear C; contradiction].
            rewrite EMap.FindUpdateNeq; [|intro C; inv_clear C; contradiction].
            lra.
        +   unfold excess_loop.
            induction xs.
        ++  cbn. lra.
        ++  repeat rewrite map_fn.
            repeat rewrite QSumListFn. 
            rewrite EMap.FindUpdateNeq; [|intro C; inv_clear C; contradiction].
            rewrite EMap.FindUpdateNeq; [|intro C; inv_clear C; contradiction].
            lra.
    Qed.

    Lemma PushExcessIn f xs x y d:
        x<>y ->
        Distinct xs ->
        (In x xs /\ excess_loop (EMap.update 0 (x,y) (fun x=>Qred (x+d)) f) y xs == excess_loop f y xs + d) \/
        (~In x xs /\ excess_loop (EMap.update 0 (x,y) (fun x=>Qred (x+d)) f) y xs == excess_loop f y xs ) .
    Proof.
        intros Hxy Hd.
        unfold excess_loop.
        induction xs.
        +   right. split; auto. cbn. lra.
        +   cbn in Hd. destruct Hd as [Hd1 Hd2].
            specialize (IHxs Hd2). 
            destruct IHxs as [[Hx IH]|[Hnx IH]].
        ++  destruct (equal a x); subst; try contradiction.
            left. split; [cbn; auto|].
            do 4 rewrite map_fn, QSumListFn.
            destruct (equal a y); subst.
        +++ rewrite EMap.FindUpdateNeq;
            [|intros C; inv_clear C; contradiction].
            set (r1 := QSumList _) in IH |- *.
            set (r2 := QSumList _) in IH |- *.
            set (r3 := QSumList _) in IH |- *.
            set (r4 := QSumList _) in IH |- *.
            set (r5 := EMap.find _ _ _) in IH |- *.            
            lra.
        +++ rewrite EMap.FindUpdateNeq;
            [|intros C; inv_clear C; contradiction].
            rewrite EMap.FindUpdateNeq;
            [|intros C; inv_clear C; contradiction].
            set (r1 := QSumList _) in IH |- *.
            set (r2 := QSumList _) in IH |- *.
            set (r3 := QSumList _) in IH |- *.
            set (r4 := QSumList _) in IH |- *.
            set (r5 := EMap.find _ _ _) in IH |- *.            
            lra.
        ++  destruct (equal x a); subst.
        +++ left. split; [cbn;auto|].
            do 4 (rewrite map_fn; rewrite QSumListFn).
            repeat rewrite EMap.FindUpdateEq.
            repeat rewrite EMap.FindUpdateNeq; 
            [|intros C; inv_clear C; contradiction].
            set (r1 := QSumList _) in IH |- *.
            set (r2 := QSumList _) in IH |- *.
            set (r3 := QSumList _) in IH |- *.
            set (r4 := QSumList _) in IH |- *.
            set (r5 := EMap.find _ _ _) in IH |- *.            
            set (r6 := EMap.find _ _ _) in IH |- *.
            rewrite Qred_correct.            
            lra.
        +++ destruct (equal y a); subst.
            *   right. split; [intros C; inv_clear C; contradiction|].
                do 4 (rewrite map_fn; rewrite QSumListFn).
                repeat rewrite EMap.FindUpdateEq.
                rewrite EMap.FindUpdateNeq; 
                [|intros C; inv_clear C; contradiction].
                set (r1 := QSumList _) in IH |- *.
                set (r2 := QSumList _) in IH |- *.
                set (r3 := QSumList _) in IH |- *.
                set (r4 := QSumList _) in IH |- *.
                set (r5 := EMap.find _ _ _) in IH |- *.            
                lra.
            *   right. split; [intros C; inv_clear C; contradiction|].
                do 4 (rewrite map_fn; rewrite QSumListFn).
                repeat rewrite EMap.FindUpdateEq.
                repeat (rewrite EMap.FindUpdateNeq; 
                [|intros C; inv_clear C; contradiction]).
                set (r1 := QSumList _) in IH |- *.
                set (r2 := QSumList _) in IH |- *.
                set (r3 := QSumList _) in IH |- *.
                set (r4 := QSumList _) in IH |- *.
                set (r5 := EMap.find _ _ _) in IH |- *.            
                lra.
    Qed.

    Lemma PushExcessOut f xs x y d:
        x<>y ->
        Distinct xs ->
        (In y xs /\ excess_loop (EMap.update 0 (x,y) (fun x=>Qred (x+d)) f) x xs == excess_loop f x xs - d) \/
        (~In y xs /\ excess_loop (EMap.update 0 (x,y) (fun x=>Qred (x+d)) f) x xs == excess_loop f x xs ) .
    Proof.
        intros Hxy Hd.
        unfold excess_loop.
        induction xs.
        +   right. split; auto. cbn. lra.
        +   cbn in Hd. destruct Hd as [Hd1 Hd2].
            specialize (IHxs Hd2). 
            destruct IHxs as [[Hx IH]|[Hnx IH]].
        ++  destruct (equal a y); subst; try contradiction.
            left. split; [cbn; auto|].
            do 4 rewrite map_fn, QSumListFn.
            destruct (equal a x); subst.
        +++ rewrite EMap.FindUpdateNeq;
            [|intros C; inv_clear C; contradiction].
            set (r1 := QSumList _) in IH |- *.
            set (r2 := QSumList _) in IH |- *.
            set (r3 := QSumList _) in IH |- *.
            set (r4 := QSumList _) in IH |- *.
            set (r5 := EMap.find _ _ _) in IH |- *.                           
            lra.
        +++ rewrite EMap.FindUpdateNeq;
            [|intros C; inv_clear C; contradiction].
            rewrite EMap.FindUpdateNeq;
            [|intros C; inv_clear C; contradiction].
            set (r1 := QSumList _) in IH |- *.
            set (r2 := QSumList _) in IH |- *.
            set (r3 := QSumList _) in IH |- *.
            set (r4 := QSumList _) in IH |- *.
            set (r5 := EMap.find _ _ _) in IH |- *.            
            lra.
        ++  destruct (equal y a); subst.
        +++ left. split; [cbn;auto|].
            do 4 (rewrite map_fn; rewrite QSumListFn).
            repeat rewrite EMap.FindUpdateEq.
            repeat rewrite EMap.FindUpdateNeq; 
            [|intros C; inv_clear C; contradiction].
            set (r1 := QSumList _) in IH |- *.
            set (r2 := QSumList _) in IH |- *.
            set (r3 := QSumList _) in IH |- *.
            set (r4 := QSumList _) in IH |- *.
            set (r5 := EMap.find _ _ _) in IH |- *.            
            set (r6 := EMap.find _ _ _) in IH |- *.
            rewrite Qred_correct.            
            lra.
        +++ destruct (equal x a); subst.
            *   right. split; [intros C; inv_clear C; contradiction|].
                do 4 (rewrite map_fn; rewrite QSumListFn).
                repeat rewrite EMap.FindUpdateEq.
                rewrite EMap.FindUpdateNeq; 
                [|intros C; inv_clear C; contradiction].
                set (r1 := QSumList _) in IH |- *.
                set (r2 := QSumList _) in IH |- *.
                set (r3 := QSumList _) in IH |- *.
                set (r4 := QSumList _) in IH |- *.
                set (r5 := EMap.find _ _ _) in IH |- *.            
                lra.
            *   right. split; [intros C; inv_clear C; contradiction|].
                do 4 (rewrite map_fn; rewrite QSumListFn).
                repeat rewrite EMap.FindUpdateEq.
                repeat (rewrite EMap.FindUpdateNeq; 
                [|intros C; inv_clear C; contradiction]).
                set (r1 := QSumList _) in IH |- *.
                set (r2 := QSumList _) in IH |- *.
                set (r3 := QSumList _) in IH |- *.
                set (r4 := QSumList _) in IH |- *.
                set (r5 := EMap.find _ _ _) in IH |- *.            
                lra.
    Qed.

    Lemma PushExcessOther f xs x y z d:
        x<>y -> z<>x -> z<>y ->
        Distinct xs ->
        excess_loop (EMap.update 0 (x,y) (fun x=>Qred (x+d)) f) z xs == excess_loop f z xs .
    Proof.
        intros Hxy Hxz Hyz Hd.
        unfold excess_loop.
        induction xs.
        +   cbn. lra.
        +   cbn in Hd. destruct Hd as [Hd1 Hd2].
            specialize (IHxs Hd2).
            do 4 rewrite map_fn, QSumListFn.
            destruct (equal a x); subst.
        +++ rewrite EMap.FindUpdateNeq;
            [|intros C; inv_clear C; contradiction].
            rewrite EMap.FindUpdateNeq;
            [|intros C; inv_clear C; contradiction].
            lra.
        +++ rewrite EMap.FindUpdateNeq;
            [|intros C; inv_clear C; contradiction].
            rewrite EMap.FindUpdateNeq;
            [|intros C; inv_clear C; contradiction].
            lra.
    Qed.

    Definition ExcessCacheNormal exMap:= forall v,
        NMap.find (Qred 0) exMap v = Qred (NMap.find (Qred 0) exMap v).


    Lemma ExcessCachedNe fn f exMap x y d:
        x<>y ->
        x ∈v nodes fn = true ->
        y ∈v nodes fn = true ->
        ExcessCacheNormal exMap ->
        ExcessCached fn f exMap ->
        ExcessCached fn 
            (EMap.update 0 (x, y) (fun x0 : Q => Qred (x0 + d)) f)
            (NMap.update (Qred 0) y (fun x0 : Q => Qred (x0 + d)) 
                (NMap.update (Qred 0) x (fun x0 : Q => Qred (x0 - d)) exMap)).
    Proof.
        destruct fn as [[[[vs es] c] s] t].
        intros Hxy Hx Hy Hexn Hex v.
        unfold excess.
        destruct (equal y v), (equal x v); subst; try contradiction.
        ++  rewrite NMap.FindUpdateEq.
            rewrite NMap.FindUpdateNeq; auto.
            apply Qred_complete.
            assert (In x (VSet.to_list vs)). {
                apply VSet.to_list_in. auto.
            }
            pose proof (PushExcessIn f (VSet.to_list vs) x v d Hxy (VSet.to_list_distinct _)).
            destruct H0; destruct H0; [|contradiction].
            unfold excess_loop in H1.
            rewrite H1. rewrite <- Hex. unfold excess.
            rewrite Qred_correct.
            reflexivity.
        ++  rewrite NMap.FindUpdateNeq; auto.
            rewrite NMap.FindUpdateEq.
            apply Qred_complete.
            assert (In y (VSet.to_list vs)). {
                apply VSet.to_list_in. auto.
            }
            pose proof (PushExcessOut f (VSet.to_list vs) v y d Hxy (VSet.to_list_distinct _)).
            destruct H0; destruct H0; [|contradiction].
            unfold excess_loop in H1.
            rewrite H1. rewrite <- Hex. unfold excess.
            rewrite Qred_correct.
            reflexivity.
        ++  rewrite NMap.FindUpdateNeq; auto.
            rewrite NMap.FindUpdateNeq; auto.
            rewrite Hexn. apply Qred_complete.
            rewrite SumNoUpdateL; auto. 
            rewrite SumNoUpdateR; auto. 
            rewrite <- Hex. unfold excess.
            rewrite Qred_correct.
            reflexivity.
    Qed.
 
    Lemma ExcessCachedNe' fn f exMap x y d:
        x<>y ->
        x ∈v nodes fn = true ->
        y ∈v nodes fn = true ->
        ExcessCacheNormal exMap ->
        ExcessCached fn f exMap ->
        ExcessCached fn 
            (EMap.update 0 (y, x) (fun x0 : Q => Qred (x0 - d)) f)
            (NMap.update (Qred 0) y (fun x0 : Q => Qred (x0 + d)) 
                (NMap.update (Qred 0) x (fun x0 : Q => Qred (x0 - d)) exMap)).
    Proof.
        destruct fn as [[[[vs es] c] s] t].
        intros Hxy Hx Hy Hexn Hex v.
        unfold excess.
        destruct (equal y v), (equal x v); subst; try contradiction.
        ++  rewrite NMap.FindUpdateEq.
            rewrite NMap.FindUpdateNeq; auto.
            apply Qred_complete.
            assert (In x (VSet.to_list vs)). { 
                apply VSet.to_list_in. auto.
            }
            assert (Hyx: v<>x). { auto. }
            pose proof (PushExcessOut f (VSet.to_list vs) v x (-d) Hyx (VSet.to_list_distinct _)).
            destruct H0; destruct H0; [|contradiction].
            unfold excess_loop in H1.
            rewrite H1. rewrite <- Hex. unfold excess.
            rewrite Qred_correct. lra.
        ++  rewrite NMap.FindUpdateNeq; auto.
            rewrite NMap.FindUpdateEq.
            apply Qred_complete.
            assert (In y (VSet.to_list vs)). { 
                apply VSet.to_list_in. auto.
            }
            pose proof (PushExcessIn f (VSet.to_list vs) y v (-d) n (VSet.to_list_distinct _)).
            destruct H0; destruct H0; [|contradiction].
            unfold excess_loop in H1.
            rewrite H1. rewrite <- Hex. unfold excess.
            rewrite Qred_correct.
            reflexivity.
        ++  rewrite NMap.FindUpdateNeq; auto.
            rewrite NMap.FindUpdateNeq; auto.
            rewrite Hexn. apply Qred_complete.
            rewrite SumNoUpdateL; auto. 
            rewrite SumNoUpdateR; auto. 
            rewrite <- Hex. unfold excess.
            rewrite Qred_correct.
            reflexivity.
    Qed.

    Lemma PushExcessCached fn f exMap x y f' exMap':
        x<>y ->
        x ∈v nodes fn = true ->
        y ∈v nodes fn = true ->
        ExcessCacheNormal exMap ->
        ExcessCached fn f exMap ->
        push fn f exMap x y = (f', exMap') ->
        ExcessCached fn f' exMap'.
    Proof.
        destruct fn as [[[[vs es] c] s] t].
        intros Hxy Hx Hy Hexn Hex H.
        unfold push in H.
        destruct ((x, y) ∈e es) eqn:E.
        +   apply pair_equal_spec in H. destruct H. subst.
            set (d:=Qmin _ _). generalize d. clear d. 
            intros d.
            apply ExcessCachedNe; auto. 
        +   apply pair_equal_spec in H. destruct H. subst.
            set (d:=Qmin _ _). generalize d. clear d. 
            intros d.
            unfold Qminus.
            apply ExcessCachedNe'; auto.
    Qed.

    Lemma ExcessCachedLoop fn f exMap x d:
        x ∈v nodes fn = true ->
        ExcessCacheNormal exMap ->
        ExcessCached fn f exMap ->
        ExcessCached fn 
            (EMap.update 0 (x, x) (fun x0 : Q => Qred (x0 + d)) f)
            (NMap.update (Qred 0) x (fun x0 : Q => Qred (x0 + d)) 
                (NMap.update (Qred 0) x (fun x0 : Q => Qred (x0 - d)) exMap)).
    Proof.
        destruct fn as [[[[vs es] c] s] t].
        intros Hx Hexn Hex v.
        unfold excess.
        pose proof (PushExcessCycle f (VSet.to_list vs) x d v).
        unfold excess_loop in H.
        destruct (equal v x); subst.
        ++  repeat rewrite NMap.FindUpdateEq.
            apply Qred_complete. rewrite H. 
            rewrite <- Hex. unfold excess.
            repeat rewrite Qred_correct.
            lra.
        ++  repeat (rewrite NMap.FindUpdateNeq; auto).
            rewrite Hexn.
            apply Qred_complete. rewrite H. 
            rewrite <- Hex. unfold excess.
            repeat (rewrite Qred_correct; auto).
            lra.
    Qed.

    Lemma ExcessCachedLoop' fn f exMap x d:
        x ∈v nodes fn = true ->
        ExcessCacheNormal exMap ->
        ExcessCached fn f exMap ->
        ExcessCached fn 
            (EMap.update 0 (x, x) (fun x0 : Q => Qred (x0 - d)) f)
            (NMap.update (Qred 0) x (fun x0 : Q => Qred (x0 + d)) 
                (NMap.update (Qred 0) x (fun x0 : Q => Qred (x0 - d)) exMap)).
    Proof.
        destruct fn as [[[[vs es] c] s] t].
        intros Hx Hexn Hex v.
        unfold excess.
        pose proof (PushExcessCycle f (VSet.to_list vs) x (-d) v).
        unfold excess_loop in H.
        destruct (equal v x); subst.
        ++  repeat rewrite NMap.FindUpdateEq.
            apply Qred_complete. rewrite H. 
            rewrite <- Hex. unfold excess.
            repeat rewrite Qred_correct.
            lra.
        ++  repeat (rewrite NMap.FindUpdateNeq; auto).
            rewrite Hexn.
            apply Qred_complete. rewrite H. 
            rewrite <- Hex. unfold excess.
            repeat (rewrite Qred_correct; auto).
            lra.
    Qed.

    Lemma PushExcessCachedLoop fn f exMap x f' exMap':
        x ∈v nodes fn = true ->
        ExcessCacheNormal exMap ->
        ExcessCached fn f exMap ->
        push fn f exMap x x = (f', exMap') ->
        ExcessCached fn f' exMap'.
    Proof.
        destruct fn as [[[[vs es] c] s] t].
        intros Hx Hexn Hex H.
        unfold push in H.
        destruct ((x, x) ∈e es) eqn:E.
        +   apply pair_equal_spec in H. destruct H. subst.
            set (d:=Qmin _ _). generalize d. clear d. 
            intros d.
            apply ExcessCachedLoop; auto.
        +   apply pair_equal_spec in H. destruct H. subst.
            set (d:=Qmin _ _). generalize d. clear d.
            intros d.
            apply ExcessCachedLoop'; auto.
    Qed.


    Lemma RelabelNoSteepArc fn f l x:
        (x ∈v nodes fn) = true -> 
        ResCapNodes fn f ->
        find_push_node fn f l x (nodes fn) = None ->
        NoSteepArc fn f l -> 
        forall l', relabel fn f l x = Some l' -> NoSteepArc fn f l'.
    Proof.
        unfold ResCapNodes, NoSteepArc, relabel.
        destruct fn as [[[[vs es] c] s] t].
        intros. set (r := relabel_find _ _ _ _ _) in H3.
        destruct r eqn:E0; [| inversion H3].
        inv_clear H3. apply RFindCondition in E0.
        destruct (equal x u), (equal x v).
        + subst. rewrite NMap.FindReplaceEq. lia.
        + subst. rewrite NMap.FindReplaceEq. rewrite NMap.FindReplaceNeq; auto.
        destruct E0. apply H0 in H4 as P. destruct P as [P1 P2].
        eapply (reflect_iff _ _ (QLt_spec _ _)) in H4.
        apply H5 in H4; auto. lia.
        + subst. rewrite NMap.FindReplaceEq. rewrite NMap.FindReplaceNeq; auto.
        destruct E0 as [E1 E2]. eapply (reflect_iff _ _ (QLt_spec _ _)) in E1. 
        apply H0 in E1 as P. destruct P as [P1 P2]. 
        apply H2 in H4. apply H2 in E1. lia.
        + rewrite NMap.FindReplaceNeq; auto. rewrite NMap.FindReplaceNeq; auto.
    Qed.



    Lemma RelabelValidCondition fn f l u : 
        ActiveNode fn f u ->
        NoSteepArc fn f l ->
        find_push_node fn f l u (nodes fn) = None -> 
        forall v,
        relabel_find fn f l u (nodes fn) = Some v -> 
        RelabelCondition fn f l u.
    Proof.
        unfold ActiveNode, NoSteepArc, RelabelCondition.
        destruct fn as [[[[vs es] c] s] t]. intros.
        split; try tauto. intros.
        eapply RFindCondition in H2 as P2. destruct P2. apply H0 in H4 as P1.
        eapply RFindMemCondition in H2.
        eapply FPNConditionNone with (v := v0) in H1; auto. 
        destruct H1.
        + rewrite QLt_false in H1. lra.
        + lia.
    Qed.

    
    Lemma PairFst {A B} {f:A*B} {x y}: f = (x,y) -> x = fst f.
    Proof. intros. rewrite H. reflexivity. Qed.

    Ltac Qred_correct := repeat (let n := fresh in set (n:=Qred _); rewrite (Qred_correct); unfold n; clear n).

    (* Siis kui gpr_helper_trace tagastab voo f' ja kõrgused l', siis järeldub, et ainukesed aktiivsed tipud on sisend või väljund,
     täidetud on voo säilivus nõue ja sisendi ning väljundi kõrgused on samad, mis alguses ehk invariante ei rikuta.  *)
    Lemma FlowConservationGpr fn g:forall (f:EMap.t Q) (exMap:NMap.t R) (l:NMap.t nat) ac tr,
        let '((vs, es),c,s,t) := fn in
        (* Iga tipp u ja v korral, kui nende vahel on serv, siis need tipud kuuluvad tippude hulka*)
        (forall u v, ((u, v) ∈e es = true) -> (u ∈v vs) = true /\ (v ∈v vs) = true) ->
        ExcessCacheNormal exMap ->
        ExcessCached fn f exMap ->
        (* Tippude hulk vs on hulk*)
        (* VSet.IsSet vs -> *)
        (* Aktiivstete tippude hulk ac on hulk*)
        (* VSet.IsSet ac -> *)
        (* Leidub tippusid, mille vahel on läbilaskevõime *)
        ResCapNodes fn f ->
        (* Täidetud on invariant h(u) <= h(v) + 1 *)
        NoSteepArc fn f l ->
        (* Iga tipp n korral, kui n kuulub aktiivsete tippude hulka, siis n kuulub ka tippude hulka*)
        (forall n, n ∈v ac = true -> n ∈v vs = true) ->
        (* Graafis on säilitatud korrektsed kõrgused *)
        ValidLabeling fn f l ->
        (* Iga tipp n korral, kui n kuulub aktiivsete tippude hulka, siis see on ekvivalentne sellega, et tipus n on ülejääk ja 
        tipp n pole sisend ega väljund*)
        (forall n, n ∈v ac = true <-> (ActiveNode fn f n /\ n<>t /\ n<>s)) ->
        (* Täidetud on eelvoo tingimused *)
        PreFlowCond fn f ->
        (* Vood ja läbilaskevõimed on mittenegatiivsed *)
        FlowMapPositiveConstraint fn f ->
        (* gpr_helper_trace tagastab voo f' ja kõrgsued l', siis sellest järeldub, et*)
        forall f' l' exMap' tr', 
        gpr_helper_trace fn f l exMap ac g tr = (Some (f', l', exMap'),tr') ->
        ExcessCacheNormal exMap' /\
        ExcessCached fn f' exMap' /\
        (* Iga tipu n korral, mis on aktiivne on n väljund või sisend*)
        (forall n, ActiveNode fn f' n -> n=t \/ n=s) /\
        (* Täidetud on voo säilivuse nõue*)
        FlowConservationConstraint fn f' /\
        (* Sisendi ja väljundi kõrgus on funktsiooni gpr_helper_trace lõpus sama, mis oli alguses *)
        (NMap.find 0 l s)%nat = (NMap.find 0 l' s)%nat /\ (NMap.find 0 l t)%nat = (NMap.find 0 l' t)%nat.
    Proof.        
        destruct fn as [[[[vs es] c] s] t]. induction g;
        intros f exMap l ac tr Heisn Hen Hex Hrcn Hnsa Hnvs Hvl Han Hprc Hfmpc f' l' exMap' tr' H.
        +   simpl in H. inversion H.
        +   rewrite gpr_helper_trace_fn in H. destruct_guard_in H.
        ++  destruct p. destruct_guard_in H.
        +++ cbn zeta in H. destruct_guard_in H.
        *   apply VSet.choiceSome in E0. destruct E0.
            destruct_guard_in H.
        **  eapply IHg in H; eauto.
        *** unfold push in E2 . destruct_guard_in E2. 
        -   intros q. 
            apply pair_equal_spec in E3. destruct E3. subst. clear - Hen.
            destruct (equal q v0).
        --  subst. rewrite NMap.FindUpdateEq. 
            apply Qred_complete. set (q:=Qred _).  rewrite (Qred_correct). reflexivity.
        --  repeat (rewrite NMap.FindUpdateNeq with (v:=v0); auto).
            destruct (equal q v).
        --- subst. repeat rewrite NMap.FindUpdateEq. 
            apply Qred_complete. set (q:=Qred _).  rewrite Qred_correct. reflexivity.
        --- repeat (rewrite NMap.FindUpdateNeq; auto).
        -   intros q. 
            apply pair_equal_spec in E3. destruct E3. subst. clear - Hen.
            destruct (equal q v0).
        --  subst. rewrite NMap.FindUpdateEq.
            apply Qred_complete. set (q:=Qred _ ). rewrite Qred_correct. reflexivity.
        --  repeat (rewrite NMap.FindUpdateNeq with (v:=v0); auto).
            destruct (equal q v).
        --- subst. repeat rewrite NMap.FindUpdateEq. 
            apply Qred_complete. set (q:=Qred _).  rewrite Qred_correct. reflexivity.
        --- repeat (rewrite NMap.FindUpdateNeq; auto).
        *** destruct (equal v v0).
        -   subst. apply PushExcessCachedLoop in E2; auto.
        -   apply PushExcessCached in E2; auto. cbn.
            apply FPNinVs in E1; auto.
        *** rewrite (PairFst E2).
            clear H IHg. apply PushResCapNodes; auto.
            eapply FPNinVs, E1.
        *** rewrite (PairFst E2).
            clear H IHg. apply PushNoSteepArc; auto.
            eapply FPNCondition; eauto.
            apply Han in H0. tauto.
        *** clear H IHg. intros. destruct_guard_in H. simpl VSet.mem in H.
        **** destruct (equal n v0).
        ***** subst. eapply FPNinVs; eauto.
        (* ***** rewrite VSet.MemRemoveNeq in H; auto.
        **** destruct (equal n v0).
        ***** subst. eapply FPNinVs; eauto. *)
        ***** rewrite VSet.MemAddNeq in H; auto.
        **** destruct (equal n v0).
        ***** subst. eapply FPNinVs; eauto.
        ***** rewrite VSet.MemAddNeq in H; auto. subst. destruct (equal n v).
        ****** subst. rewrite VSet.MemRemoveEq in H. inversion H.
        ****** rewrite VSet.MemRemoveNeq in H; auto.
        *** rewrite (PairFst E2).
            clear H IHg. eapply (PushValidLabel (vs, es, c ,s, t)); auto.
            eapply FPNCondition; eauto. apply Han in H0. tauto.
        *** rewrite (PairFst E2). 
            intros. split; intros.
        **** destruct (equal n v0).
        ***** subst. clear H IHg. apply HENSCondition in E0. 
            split; try tauto. split.
        ****** eapply FPNinVs, E1.
        ****** destruct (equal v v0).
        -   subst. rewrite E2. simpl fst.
            apply PushExcessCachedLoop in E2; auto. 
            rewrite (E2 v0). tauto.
        -   rewrite E2. simpl fst.
            apply PushExcessCached in E2; auto.
        --  rewrite (E2 v0). tauto. 
        --  apply FPNinVs in E1; auto.
        ***** clear H IHg. rewrite VSet.MemAddNeq in H2; eauto.
        destruct_guard_in H2.
        ****** eapply Han in H2. destruct H2. split; eauto.
        destruct (equal n v). 
        ******* subst. 
            eapply (reflect_iff _ _ (QLt_spec _ _)) in E3. split; eauto.
            destruct (equal v v0).
        -   subst. rewrite E2. simpl fst.
            apply PushExcessCachedLoop in E2; auto. 
            rewrite (E2 v0). tauto.
        -   rewrite E2. simpl fst.
            apply PushExcessCached in E2; auto.
        --  rewrite (E2 v). tauto. 
        --  apply FPNinVs in E1; auto.
        ******* eapply PushActiveCondition; eauto.
        ****** subst. destruct (equal n v).
        ******* subst. rewrite VSet.MemRemoveEq in H2. inversion H2.
        ******* rewrite VSet.MemRemoveNeq in H2; eauto. 
        eapply Han in H2. destruct H2. split; eauto. 
         eapply PushActiveCondition; eauto.
        **** clear H IHg. destruct (equal n v0).
        ***** subst. apply VSet.MemAddEq. 
        ***** rewrite VSet.MemAddNeq; auto.
        destruct_guard.
        ****** eapply Han. destruct H2. split; auto. destruct (equal n v).
        ******* subst. eapply Han in H0. tauto.
        ******* eapply PushActiveInv in H; auto. 
        ******** eapply FPNinVs in E1. auto.
        ******** eapply FPNCondition in E1; eauto.
        apply Han in H0; tauto.
        ****** subst. rewrite VSet.MemRemoveNeq.
        ******* eapply FPNinVs in E1 as P. eapply FPNCondition in E1; eauto;
        [| eapply Han in H0; tauto]. destruct H2. eapply PushActiveInv in H; eauto.
        eapply Han. split; auto.
        ******* intro C. subst. destruct H2. destruct H. 
            destruct (equal v v0).
        -   subst. rewrite E2 in H2. simpl fst in H2.
            apply PushExcessCachedLoop in E2; auto. 
        -   rewrite E2 in H2. simpl fst in H2.
            apply PushExcessCached in E2; auto.
        --  specialize (E2 v). apply QLt_false in E3. rewrite E2 in H2. lra.
        --  apply FPNinVs in E1; auto.
        *** clear H IHg.
            rewrite (PairFst E2).
            eapply (PushPreFlow (vs, es, c, s, t)); auto. 
        **** eapply FPNinVs in E1. auto.
        **** eapply FPNCondition; eauto. eapply Han in H0; tauto.
        *** clear H IHg. 
            rewrite (PairFst E2).
            eapply (PushFlowMapPos (vs, es, c, s, t)); eauto.
            eapply FPNCondition; eauto. eapply Han in H0. tauto.
        **  eapply FPNinVs in E1 as P. apply Han in H0 as W. destruct W. 
            eapply FPNCondition in E1 as P2; auto.
            eapply HENSConditionFalse in E0 as Q.
            eapply IHg in H; eauto.
        *** unfold push in E2 . destruct_guard_in E2. 
        -   intros q. 
            apply pair_equal_spec in E3. destruct E3. subst. clear - Hen.
            destruct (equal q v0).
        --  subst. rewrite NMap.FindUpdateEq.
            apply Qred_complete. set (q:=Qred _ ). rewrite Qred_correct. reflexivity.
        --  repeat (rewrite NMap.FindUpdateNeq with (v:=v0); auto).
            destruct (equal q v).
        --- subst. repeat rewrite NMap.FindUpdateEq. 
            apply Qred_complete. set (q:=Qred _). rewrite Qred_correct. reflexivity.
        --- repeat (rewrite NMap.FindUpdateNeq; auto).
        -   intros q. 
            apply pair_equal_spec in E3. destruct E3. subst. clear - Hen.
            destruct (equal q v0).
        --  subst. rewrite NMap.FindUpdateEq.
            apply Qred_complete. set (q:=Qred _ ). rewrite Qred_correct. reflexivity.
        --  repeat (rewrite NMap.FindUpdateNeq with (v:=v0); auto).
            destruct (equal q v).
        --- subst. repeat rewrite NMap.FindUpdateEq. 
            apply Qred_complete. set (q:=Qred _). rewrite Qred_correct. reflexivity.
        --- repeat (rewrite NMap.FindUpdateNeq; auto).
        *** destruct (equal v v0).
        -   subst. apply PushExcessCachedLoop in E2; auto.
        -   apply PushExcessCached in E2; auto.
        *** rewrite (PairFst E2).
            eapply PushResCapNodes; auto.
        *** rewrite (PairFst E2).
            eapply PushNoSteepArc; auto.
        *** intros. destruct (equal n v0).
        **** subst. auto.
        **** rewrite VSet.MemRemoveNeq in H4; auto. eapply Hnvs.
         destruct_guard_in H4; auto. subst.
         rewrite VSet.MemRemoveNeq in H4; auto.
         intro C. subst. rewrite VSet.MemRemoveEq in H4. inversion H4.
        *** rewrite (PairFst E2).
            eapply (PushValidLabel (vs, es, c, s, t)); eauto.
        *** intros. destruct (equal n v0).
        **** subst. rewrite VSet.MemRemoveEq. split; intros; [inversion H1 |].
        destruct Q.
        ***** destruct H1. destruct H1. 
            destruct (equal v v0).
        -   subst. apply PushExcessCachedLoop in E2; auto.
            specialize (E2 v0). rewrite E2 in H6. simpl Qred in *.  lra. 
        -   apply PushExcessCached in E2; auto.
            specialize (E2 v0). rewrite E2 in H6. simpl Qred in *.  lra.
        ***** simpl in H4. tauto.
        **** rewrite VSet.MemRemoveNeq; auto. destruct_guard; split; intros.
        ***** eapply Han in H4. destruct H4. split; auto. destruct (equal n v).
        ****** subst. split; auto.  eapply (reflect_iff _ _ (QLt_spec _ _)) in E3.
            destruct (equal v v0).
        -   subst. apply PushExcessCachedLoop in E2; auto.
            specialize (E2 v0). rewrite E2. lra. 
        -   apply PushExcessCached in E2; auto.
            specialize (E2 v). rewrite E2. lra.
        ****** rewrite (PairFst E2).
            eapply PushActiveCondition; eauto.
        ***** eapply Han. destruct H4. split; auto.
            rewrite (PairFst E2) in H4.
            eapply PushActiveInv in P2; eauto.
        ***** subst. destruct (equal n v).
        ****** subst. rewrite VSet.MemRemoveEq in H4. inversion H4.
        ****** rewrite VSet.MemRemoveNeq in H4; auto. 
            eapply Han in H4. destruct H4. split; auto.
            rewrite (PairFst E2).
            eapply PushActiveCondition; eauto.
        ***** subst. destruct (equal n v).
        ****** subst. eapply QLt_false in E3. destruct H4, H1. 
            destruct (equal v v0).
        -   subst. apply PushExcessCachedLoop in E2; auto.
        -   apply PushExcessCached in E2; auto.
            specialize (E2 v). rewrite E2 in H5. lra.
        ****** rewrite VSet.MemRemoveNeq; auto. eapply Han. 
            destruct H4. split; auto.
            rewrite (PairFst E2) in H1.
            eapply PushActiveInv in P2; eauto.
        *** rewrite (PairFst E2).
            eapply (PushPreFlow (vs, es, c, s, t)); eauto.
        *** rewrite (PairFst E2).
            eapply (PushFlowMapPos (vs, es, c, s, t)); eauto.
        +++ destruct_guard_in H.
        ** eapply VSet.choiceSome in E0; auto. destruct E0, H1.
            eapply IHg in H; eauto.
        *** split; try tauto. split; try tauto.
            destruct H, H1, H2, H3, H4.  rewrite <- H4, <- H5. subst.
            unfold relabel in E2. destruct_guard_in E2; [|inversion E2]. inv_clear E2.
            destruct (equal s v).
        **** subst. exfalso. apply Han in H0. destruct H0, H6. auto.
        **** rewrite NMap.FindReplaceNeq; auto. split; auto.
            destruct (equal t v). 
        ***** subst. exfalso. apply Han in H0. destruct H0. destruct H6; auto.
        ***** rewrite NMap.FindReplaceNeq; auto.
        *** eapply RelabelNoSteepArc; eauto.
        *** eapply (RelabelValidLabel (vs, es, c, s, t)); eauto. 
        unfold relabel in E2. destruct_guard_in E2; [| inversion E2].
        eapply RelabelValidCondition; eauto.
        **** apply Han. auto.
        ** inversion H. 
        ++  apply VSet.choiceNone in E0. subst. inv_clear H. 
            repeat split; try tauto.
        * intros. destruct (equal n t); auto. 
        destruct (equal n s); subst; try tauto.
        assert (n ∈v VSet.empty = true).
        ** eapply Han. tauto.
        ** rewrite VSet.MemEmpty in H0. inversion H0.
        * 
         unfold FlowConservationConstraint. intros. unfold PreFlowCond in Hprc.
        destruct Hprc. unfold NonDeficientFlowConstraint in H3.
        apply H3 in H as P; auto. clear IHg. 
        destruct (Qeq_bool (excess (vs, es, c, s, t) f' v) 0) eqn : E.
        ** eapply Qeq_bool_iff in E. auto.
        ** eapply Qeq_bool_neq in E. assert (v ∈v VSet.empty = true).
        *** eapply Han. split; auto. split; auto. lra.
        *** rewrite VSet.MemEmpty in H4. inversion H4.
    Qed.
        
    Lemma SumSameReplace (f:EMap.t Q) (s:V->V*V) vs u v d : 
        (forall v0, In v0 vs -> s v0 <> (u, v)) ->
        map (fun v0 => EMap.find 0 
            (EMap.replace (u, v) d f) 
            (s v0)) vs = 
        map (fun v0 => EMap.find 0 f (s v0)) vs.
    Proof.
        induction vs; intros.
        + simpl. auto.
        + simpl. rewrite IHvs; auto.
        f_equal. clear IHvs.
        - erewrite EMap.FindReplaceNeq; auto.
        apply H. cbn. auto.
        - intros. apply H. cbn. auto.
    Qed.

    Lemma NDFinitial vs es c s t d  y n f: 
        0 <= d ->
        n<>s ->
        excess (vs, es, c, s, t) f n <= 
            excess (vs, es, c, s, t) (EMap.update 0 (s, y) (fun x : Q => Qred (x + d)) f) n .
    Proof.
        intros Hd Hnns. unfold excess.
        set (xs := VSet.to_list vs). repeat rewrite Qred_correct.
        induction xs; intros.
        +   simpl. lra. 
        +   repeat rewrite map_fn. repeat rewrite QSumListFn.
            destruct (equal n y).
        -   subst. destruct (equal a s).
        *   subst. erewrite EMap.FindUpdateEq. 
            erewrite EMap.FindUpdateNeq;
                [|intros C; inv_clear C; contradiction].
            unfold R in *. rewrite Qred_correct. lra.
        *   repeat (erewrite EMap.FindUpdateNeq;
                [|intro C; inv_clear C; auto]).
            unfold R in *. lra.
        - repeat (erewrite EMap.FindUpdateNeq;
                [|intro C; inv_clear C; auto]).
            unfold R in *. lra.
    Qed.

    Lemma SourceDeficient vs es c s t y f: 
        (forall a, EMap.find 0 f (a,s) <= EMap.find 0 f (s,a)) ->
        EMap.find 0 f (s,y) <= c s y ->
        excess (vs, es, c, s, t) (EMap.replace (s, y) (c s y) f) s <= 0.
    Proof.
        intros Has Hcap. unfold excess.
        set (xs := VSet.to_list vs). repeat rewrite Qred_correct.
        induction xs; intros.
        +   simpl. lra.
        +   repeat rewrite map_fn. repeat rewrite QSumListFn.
            destruct (Edge.equal (s,y) (a,s)).
        - inv_clear e. erewrite EMap.FindReplaceEq. lra.
        - destruct (equal y a).
        * subst. erewrite EMap.FindReplaceEq. erewrite EMap.FindReplaceNeq.
        ** specialize (Has a). lra.
        ** auto.
        * erewrite EMap.FindReplaceNeq, EMap.FindReplaceNeq.
        ** specialize (Has a). lra.
        ** intro C. inv_clear C. auto.
        ** auto.
    Qed.

    Lemma ExcessSame vs es c s t y f n: 
        (forall a, EMap.find 0 f (a,s) <= EMap.find 0 f (s,a)) ->
        EMap.find 0 f (s,y) <= c s y ->
        n<>s ->
        n<>y ->
        excess (vs, es, c, s, t) f n  = excess (vs, es, c, s, t) (EMap.replace (s, y) (c s y) f) n.
    Proof.
        intros Has Hcap Hnns Hnny. unfold excess.
        set (xs := VSet.to_list vs). 
        apply Qred_complete.
        induction xs; intros.
       + simpl. reflexivity.
       + simpl.  erewrite EMap.FindReplaceNeq, EMap.FindReplaceNeq.
       -  lra.
       - intro C. inv_clear C. auto.
       - intro C. inv_clear C. auto.
    Qed.

    Lemma SumNoR: forall f vs v t c n, n <> t ->
        QSumList (map (fun v0 : V => EMap.find 0 (EMap.replace (v, t) c f) (v0, n)) vs) = QSumList (map (fun v0 : V => EMap.find 0 f (v0, n)) vs).
    Proof.
        intros f vs. induction vs; intros; cbn; auto.
        assert ((a, n) <> (v, t)). { 
            intro q. inv_clear q. tauto. 
        }
        rewrite EMap.FindReplaceNeq; auto.
        eapply (IHvs v t c) in H. rewrite H. 
        reflexivity.
    Qed.
        

    Lemma InitialUpdateBigger: forall f s v0 n d xs, d >= 0 ->
        QSumList (map (fun v1 : V => EMap.find 0 (EMap.update 0 (s, v0) (fun x => Qred (x + d)) f) (v1, n)) xs) >= QSumList (map (fun v1 : V => EMap.find 0 f (v1, n)) xs).
    Proof.
        intros f s v0 n d xs H.
        induction xs; intros; [cbn; try lra|].
        destruct (Edge.equal (a,n) (s,v0)).
        +   inv_clear e.
            repeat rewrite map_fn.
            repeat rewrite QSumListFn.
            rewrite EMap.FindUpdateEq.
            rewrite Qred_correct. lra.
        +   repeat rewrite map_fn.
            repeat rewrite QSumListFn.
            rewrite EMap.FindUpdateNeq; auto. lra.
    Qed.

    Lemma Qlt_le_trans: forall x y z : Q, x < y -> y <= z -> x < z.
    Proof. intros. lra. Qed.

    (* Peale initsialiseerimist on aktiivsete tippude hulgas tipud, mis ei ole sisend ega väljund ja on täidetud eelvoo nõuded
     ja vood ning läbilaskevõimed on mittenegatiivsed*)
    Lemma InitialGpr fn :
        let '((vs, es),c,s,t) := fn in
        (* Iga tipp u ja v korral, kui nende vahel on serv, siis need tipud kuuluvad tippude hulka*)
        (forall u v, ((u, v) ∈e es = true) -> (u ∈v vs) = true /\ (v ∈v vs) = true) ->
        (forall u v, c u v >= 0) ->
        forall f' ac' exMap' ,
        (* Kui algoritmi initsialiseerimise samm, kus tehakse push samm sisendist väljuvate servade peal
        tagastab voo f' ja aktiivsed tipud ac', siis sellest järeldub all olev konjuktsioon*)
        initial_push fn = (f',ac',exMap') ->
        ExcessCacheNormal exMap' /\
        ExcessCached fn f' exMap' /\
        ResCapNodes fn f' /\
        (forall n, n ∈v ac' = true -> n ∈v vs = true) /\
        (forall n, n ∈v ac' = true <-> (ActiveNode fn f' n /\ n<>t /\ n<>s)) /\
        PreFlowCond fn f' /\
        FlowMapPositiveConstraint fn f'.
    Proof.
        destruct fn as [[[[vs es] c] s] t].
        intros Hvs Hc. 
        intros f' ac' exMap'.
        unfold initial_push.
        set (es' := ESet.filter _ _).
        rewrite <- fold_left_rev_right.
        unfold initial_push_step.
        set (xs := rev _).
        assert (K:forall x, In x xs -> ESet.mem x es = true). {
            intros. apply in_rev in H.
            apply ESet.to_list_in in H.
            apply ESet.in_filter in H. tauto.
        }
        assert (G: forall x, In x xs -> fst x = s). {
            intros. apply in_rev in H.
            apply ESet.to_list_in in H.
            apply ESet.in_filter in H.
            destruct x. destruct (equal s v); subst;cbn; auto.
            destruct H. inversion H0.
        }
        assert (Ds: Distinct xs). {
            apply rev_distinct. 
            apply ESet.to_list_distinct.
        }
        set (F := (fun y => _)).
        intros H.
        apply (@proj2  (forall u v, ~In (u,v) xs -> EMap.find 0 f' (u,v) == 0 )).
        generalize dependent H.
        generalize dependent exMap'.
        generalize dependent ac'.
        generalize dependent f'.
        induction xs; intros f' ac' exMap' H.
        +   cbn in H. inv_clear H.
             repeat split; auto.
        ++  intros. rewrite EMap.FindEmpty. lra.
        ++  intros v. rewrite NMap.FindEmpty. apply Qred_complete. 
            rewrite Qred_correct. lra.
        ++  intros v. unfold excess.
            rewrite NMap.FindEmpty. apply Qred_complete.
            generalize (VSet.to_list vs).
            intros l. induction l; cbn; [lra|].
            repeat rewrite EMap.FindEmpty. lra.
        ++  cbn in H. destruct_guard_in H.
        +++ apply Hvs in E0. tauto.
        +++ rewrite EMap.FindEmpty in H. lra.
        ++  cbn in H. destruct_guard_in H.
        +++ apply Hvs in E0. tauto.
        +++ rewrite EMap.FindEmpty in H. lra.
        (* ++  intros. rewrite EMap.FindEmpty. apply Hc. *)
        ++  intros. rewrite VSet.MemEmpty in H. inversion H.
        ++  rewrite VSet.MemEmpty in H. inversion H.
        ++  rewrite VSet.MemEmpty in H. inversion H.
        ++  rewrite VSet.MemEmpty in H. inversion H.
        ++  rewrite VSet.MemEmpty in H. inversion H.
        ++  intros [[H0 H1] [H2 H3]]. 
            unfold excess in H1.
            set (ys:=VSet.to_list vs) in H1. exfalso. clear -H1.
            induction ys.
        +++ cbn in H1. lra.
        +++ repeat rewrite map_fn, QSumListFn in H1.
            repeat rewrite EMap.FindEmpty in H1.
            rewrite Qred_correct in H1, IHys. lra.
        ++  cbn. intros. rewrite EMap.FindEmpty. apply Hc.
        ++  unfold NonDeficientFlowConstraint, excess. intros. 
            set (ys:=VSet.to_list vs). clear -ys .
            induction ys.
        +++ cbn. lra.
        +++ repeat rewrite map_fn, QSumListFn.
            repeat rewrite EMap.FindEmpty.
            rewrite Qred_correct in IHys |- *. lra.
        ++  rewrite EMap.FindEmpty. lra.
        +   simpl fold_right in H. destruct a.
            destruct (fold_right F (EMap.empty, VSet.empty, NMap.empty) xs) eqn:E. destruct p.
            assert (K' : forall x : V * V, In x xs -> x ∈e es = true). {
                clear -K. intros. apply K. cbn. tauto.
            }
            assert (G' : forall x, In x xs -> fst x = s). {
                clear -G. intros. apply G. cbn. tauto.
            }
            destruct Ds as [Ds1 Ds2].
            specialize (IHxs K' G' Ds2 _ _ _ eq_refl).
            unfold F in H. unfold has_excess_not_sink in H.
            apply pair_equal_spec in H. destruct H. subst.
            destruct IHxs as [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]].
            assert (J: v ∈v vs = true /\ v0 ∈v vs = true). {
                apply Hvs, K. constructor; auto.
            }
            assert (G2: v = s). {
                eapply (G (v,v0)). constructor; auto.
            }
            destruct J as [J0 J1].
            apply pair_equal_spec in H as [D1 D2]; subst.
            repeat split; auto.
        ++  intros.
            destruct (Edge.equal (u,v) (s,v0)).
        +++ inv_clear e.
            destruct H. cbn. tauto. 
        +++ rewrite EMap.FindUpdateNeq; auto.
            apply H1. intro C. apply H. right. apply C.
        ++  intros v.
            destruct (equal v0 v).
        +++ subst. rewrite NMap.FindUpdateEq.
            apply Qred_complete. symmetry. apply Qred_correct.
        +++ rewrite NMap.FindUpdateNeq; auto.
            destruct (equal s v).
            *   subst. rewrite NMap.FindUpdateEq; auto.
                apply Qred_complete. symmetry.
                apply Qred_correct.
            *   rewrite NMap.FindUpdateNeq; auto.
        ++  destruct (equal s v0).
        +++ subst. eapply ExcessCachedLoop; auto.
        +++ apply ExcessCachedNe; auto.
        ++  unfold res_cap in H.
            specialize (H4 u v).
            unfold res_cap in H4.
            destruct ((u, v) ∈e es) eqn:E1.
        +++ apply Hvs in E1. tauto.
        +++ destruct (Edge.equal (s,v0) (v,u)).
            *   inv_clear e. cbn. tauto.
            *   rewrite EMap.FindUpdateNeq in H; auto.
                apply H4 in H. cbn. tauto.
        ++  unfold res_cap in H. 
            specialize (H4 u v).
            unfold res_cap in H4.
            destruct ((u, v) ∈e es) eqn:E1.
        +++ apply Hvs in E1. tauto.
        +++ destruct (Edge.equal (s,v0) (v,u)).
            *   inv_clear e. cbn. tauto.
            *   rewrite EMap.FindUpdateNeq in H; auto.
                apply H4 in H. cbn. tauto.
        (* ++  intros. 
            destruct (Edge.equal (s,v0) (u,v)).
        +++ inv_clear e. rewrite EMap.FindUpdateEq. lra.


        +++ rewrite EMap.FindReplaceNeq; auto.
        ++  intros. 
            destruct (equal v0 t); cbn in H; subst; auto.
            destruct (equal v0 s); cbn in H; subst; auto.
            destruct_guard_in H; auto.
            destruct (equal n v0); cbn in H; subst; try  tauto.
            erewrite VSet.MemAddNeq in H; auto. *)
        ++  intros. 
            destruct (equal v0 t); cbn in H; subst; auto.
            destruct (equal v0 s); cbn in H; subst; auto.
            destruct_guard_in H; auto.
            destruct (equal n v0); cbn in H; subst; try  tauto.
            erewrite VSet.MemAddNeq in H; auto.
        ++  cbn.
            destruct (equal v0 t); subst.
        +++ apply H5, H.
        +++ destruct (equal v0 s); subst.
            *   apply H5, H.
            *   set (q := NMap.find _ _ _) in H.
                cbn in H.
                destruct (0 <? q) eqn:E1.
            **  destruct (equal n v0); subst; auto.
                rewrite VSet.MemAddNeq in H; auto.
            **  apply H5, H.
        ++ destruct (equal v0 t); subst.
        +++ apply H6 in H.
            unfold ActiveNode in H.
            destruct H, H, H0.
            eapply Qlt_le_trans; eauto.
            eapply NDFinitial; auto.
        +++ destruct (equal v0 s); subst.
            *   apply H6 in H. unfold ActiveNode in H. 
                destruct H, H, H0.
                eapply Qlt_le_trans; eauto.
                eapply NDFinitial; auto.
            *   rewrite NMap.FindUpdateEq in H.
                rewrite NMap.FindUpdateNeq in H; auto.
                set (q := Qred _) in H.
                simpl in H.
                destruct (0 <? q) eqn:E1;
                [destruct (equal n v0)|].
            **  subst.
                destruct (QLt_spec 0 q); 
                    [|inversion E1].
                unfold q in q0.
                rewrite Qred_correct in q0.
                rewrite <- H3 in q0.
                assert (s <> v0) by auto.
                assert (In s (VSet.to_list vs)). {
                    apply VSet.to_list_in. auto.
                }
                pose proof (PushExcessIn t1 (VSet.to_list vs) s v0 (c s v0) H0 (VSet.to_list_distinct _)).
                destruct H9; destruct H9; [|contradiction].
                unfold excess_loop in H10.
                unfold excess in *.
                rewrite Qred_correct in *.
                lra.
            **  rewrite VSet.MemAddNeq in H; auto.
                apply H6 in H.
                destruct H, H, H0.
                eapply Qlt_le_trans; eauto.
                eapply NDFinitial; auto.
            **  apply H6 in H.
                destruct H, H, H0.
                eapply Qlt_le_trans; eauto.
                eapply NDFinitial; auto.
        ++  destruct (equal v0 t); subst.
        +++ apply H6 in H. tauto.
        +++ destruct (equal v0 s); subst.
            *   apply H6 in H. tauto.
            *   rewrite NMap.FindUpdateEq in H.
                rewrite NMap.FindUpdateNeq in H; auto.
                set (q := Qred _) in H.
                simpl in H.
                destruct (0 <? q) eqn:E1;
                [destruct (equal n v0)|].
            **  subst. tauto.
            **  rewrite VSet.MemAddNeq in H; auto.
                apply H6 in H.
                destruct H, H, H0. tauto.
            **  apply H6 in H.
                destruct H, H, H0. tauto.
        ++  intros.
            destruct (equal v0 t); subst.
        +++ apply H6. destruct H. split; try tauto.
        +++ destruct (equal v0 s); subst.
            *   apply H6. destruct H. split; try tauto.
            *   rewrite NMap.FindUpdateEq in H.
                rewrite NMap.FindUpdateNeq in H; auto.
                set (q := Qred _) in H.
                simpl in H.
                destruct (0 <? q) eqn:E1;
                [destruct (equal n v0)|].
            **  subst. tauto.
            **  simpl in H. rewrite VSet.MemAddNeq in H; auto.
                apply H6 in H.
                destruct H, H, H0. tauto.
            **  apply H6 in H.
                destruct H, H, H0. tauto.
        ++  intros [K1 [K2 K3]].
            destruct (equal v0 t); subst.
        +++ unfold ActiveNode in K1.
            apply H6. split; try tauto.
            unfold ActiveNode.
            split; try tauto. destruct K1.
            clear -H0 K2 K3 J1 Hc. unfold excess in *.
            rewrite Qred_correct in *.
            destruct (equal s t); cbn; subst.
            *   pose proof (PushExcessCycle t1 (VSet.to_list vs) t (c t t) n).
                unfold excess_loop in *. lra.
            *   assert (In t (VSet.to_list vs)). { 
                    apply VSet.to_list_in. auto.
                }
                pose proof (PushExcessOther t1 (VSet.to_list vs) s t n (c s t) n0 K3 K2 (VSet.to_list_distinct _)). 
                unfold excess_loop in H1.
                lra.
        +++ destruct (equal v0 s); subst.
            *   unfold ActiveNode in K1.
                apply H6. split; try tauto.
                unfold ActiveNode.
                split; try tauto. destruct K1.
                clear -H0 K2 K3 J1 Hc. unfold excess in *.
                rewrite Qred_correct in *.
                pose proof (PushExcessCycle t1 (VSet.to_list vs) s (c s s) n).
                unfold excess_loop in *. lra.
            *   rewrite NMap.FindUpdateEq.
                rewrite NMap.FindUpdateNeq; auto.
                destruct (0 <? Qred (NMap.find (Qred 0) t0 v0 + c s v0)) eqn:E3.
            **  destruct (equal n v0); subst.
            *** cbn. rewrite VSet.MemAddEq. auto.
            *** cbn. rewrite VSet.MemAddNeq; auto. apply H6. split; try tauto.
                unfold ActiveNode in K1 |- *. destruct K1. split; auto.
                unfold excess in *. rewrite Qred_correct in *.
                assert (G1: s<>v0) by auto.
                assert (G2: n<>s) by auto.
                assert (G3: n<>v0) by auto.
                pose proof (PushExcessOther t1 (VSet.to_list vs) s v0 n (c s v0) G1 G2 G3 (VSet.to_list_distinct _)).                 
                unfold excess_loop in *. lra.
            **  destruct (equal n v0); cbn; subst.
            *** apply H6. split; try tauto.
                unfold ActiveNode in K1 |- *. destruct K1. split; auto.
                rewrite <- H3 in E3.
                destruct (QLt_spec 0 (Qred (excess (vs, es, c, s, t) t1 v0 + c s v0))); [inversion E3|].
                exfalso.
                unfold excess in *. rewrite Qred_correct in *.
                assert (G1: s<>v0) by auto.
                assert (In s (VSet.to_list vs)). { 
                    apply VSet.to_list_in. auto.
                }
                pose proof (PushExcessIn t1 (VSet.to_list vs) s v0 (c s v0) G1 (VSet.to_list_distinct _)).
                destruct H9; destruct H9; [|contradiction].
                unfold excess_loop in *. 
                rewrite Qred_correct in *.
                lra. 
            *** apply H6. split; try tauto.
                unfold ActiveNode in K1 |- *. destruct K1. split; auto.
                rewrite <- H3 in E3.
                destruct (QLt_spec 0 (Qred (excess (vs, es, c, s, t) t1 v0 + c s v0))); [inversion E3|].
                unfold excess in *. rewrite Qred_correct in *.
                assert (G1: s<>v0) by auto.
                assert (G2: n<>s) by auto.
                assert (G3: n<>v0) by auto.
                pose proof (PushExcessOther t1 (VSet.to_list vs) s v0 n (c s v0) G1 G2 G3 (VSet.to_list_distinct _)).                 
                unfold excess_loop in *. 
                rewrite Qred_correct in *.
                lra. 
        ++  unfold CapacityConstraint. intros.
            destruct H7. unfold PreFlowCond in H0.
            destruct H0.
            specialize (H0 u v H).
            destruct (Edge.equal (u,v) (s,v0) ).
        +++ inv_clear e.
            rewrite EMap.FindUpdateEq.
            specialize (H1 _ _ Ds1). 
            rewrite Qred_correct.
            lra.
        +++ rewrite EMap.FindUpdateNeq; auto.
        ++  unfold NonDeficientFlowConstraint. intros.
            destruct H7.  destruct H7. unfold NonDeficientFlowConstraint in H9.
            specialize (H9 v H H0).
            unfold excess in *.
            destruct (equal v0 v); subst.
        +++ rewrite SumNoUpdateL; auto. 
            rewrite Qred_correct. unfold R in *.
            specialize (Hc s v).
            rewrite Qred_correct in *.
            eapply InitialUpdateBigger with (n:=v) (xs:=VSet.to_list vs) (s:=s) (v0:=v) (f:=t1) in Hc.
            clear -Hc H9. lra.
        +++ rewrite SumNoUpdateL; auto.
            rewrite SumNoUpdateR; auto.
        ++  unfold CapacityConstraint. intros.
            destruct (Edge.equal (s,v0) (u, v)).
            *   inv_clear e.
                rewrite EMap.FindUpdateEq.
                rewrite Qred_correct.
                destruct H7, H. 
                specialize (H0 u v).
                lra.
            *   rewrite EMap.FindUpdateNeq; auto.
                destruct H7, H. 
                specialize (H0 u v).
                lra.
    Qed.



    Lemma InitialPushResCap0Helper vs es c s t xs: 
    Distinct xs -> forall f' ac' exMap', 
    fold_right (fun x y => initial_push_step (vs,es,c,s,t) y x)  (EMap.empty, VSet.empty, NMap.empty) xs = (f',ac',exMap') ->
    (forall v, In (s,v) xs -> EMap.find 0 f' (s, v) == c s v) /\
    (forall u v, ~In (u,v) xs -> EMap.find 0 f' (u, v) == 0).
    Proof.
        induction xs; intros; split; intros.
        +   inv_clear H1.
        +   cbn in H0. inv_clear H0. rewrite EMap.FindEmpty. lra.
        +   simpl in H0. 
            destruct (fold_right _ _ xs) eqn:E1. destruct a, p.
            destruct H as [D1 D2].
            eapply IHxs in D2 as [C1 C2]; [|reflexivity].
            unfold initial_push_step in H0.
            repeat rewrite pair_equal_spec in H0. destruct H0, H; subst.
            destruct (Edge.equal (v0,v1) (s,v)).
        ++  inv_clear e.
            rewrite EMap.FindUpdateEq, C2; auto. 
            rewrite Qred_correct. lra.
        ++  rewrite EMap.FindUpdateNeq; auto.
            destruct H1.
        +++ inv_clear H. destruct n; auto.
        +++ apply C1; auto.
        +   simpl in H0. 
            destruct (fold_right _ _ xs) eqn:E1. destruct a, p.
            destruct H as [D1 D2].
            eapply IHxs in D2 as [C1 C2]; [|reflexivity].
            unfold initial_push_step in H0.
            repeat rewrite pair_equal_spec in H0. destruct H0, H; subst.
            rewrite EMap.FindUpdateNeq.
        ++  apply C2. cbn in H1. tauto.
        ++  intros C. inv_clear C.  cbn in H1. tauto.
    Qed.

    Lemma InitialPushResCap0 vs es c s t v : 
        v<>s -> forall  f' ac' exMap',
        initial_push (vs,es,c,s,t) = (f',ac',exMap') ->
        res_cap (vs,es,c,s,t) f' s v == 0.
    Proof.
        unfold initial_push.
        set (es' := ESet.filter _ _).
        rewrite <- fold_left_rev_right.
        set (xs := rev _). intros.
        apply InitialPushResCap0Helper in H0.
        +   destruct H0. unfold res_cap.
            destruct ((s, v) ∈e es) eqn:E.
        ++  rewrite H0; [lra|]. unfold xs. rewrite <- in_rev.
            unfold es'. apply ESet.to_list_in.
            rewrite ESet.filter_in; auto. apply eqb_refl.
        ++  rewrite H1; [lra|]. intro C.
            unfold xs in C.
            rewrite <- in_rev in C.
            unfold es' in C. apply ESet.to_list_in in C.
            eapply ESet.in_filter in C.
            destruct C.
            destruct (equal s v); subst; try tauto.
            inv_clear H3.
        +   unfold xs. apply rev_distinct. unfold es'.
            apply ESet.to_list_distinct.
    Qed.


    (* Kui tipud u ja v kuuluvad tippude hulka ning servade (u, v) läbilaskevõime on mittenegatiivne ja sisend pole väljund ning
     gpr_trace tagastab voo f' ja kõrgused l', siis järeldub, et aktiivsed tipud on ainult sisend või väljund,
     on täidetud voo nõuded ja on säilitatud invariandid, et sisendi kõrgus on võrdne tippude arvuga ja väljundi kõrgus on 0 *)
    Lemma FlowConservationGprMain fn (l:NMap.t nat):
        let '((vs, es),c,s,t) := fn in
        (forall u v, ((u, v) ∈e es = true) -> (u ∈v vs) = true /\ (v ∈v vs) = true) ->
        True ->
        (forall u v, c u v >= 0) ->
        s<>t ->
        forall f' l' eM' tr', 
        gpr_trace fn = (Some (f',l',eM'),tr') ->
        (forall n, ActiveNode fn f' n -> n=t \/ n=s) /\ 
        FlowConservationConstraint fn f' /\
        (VSet.size vs = NMap.find 0 l' s)%nat /\ (O=NMap.find 0 l' t)%nat.
    Proof.
        destruct fn as [[[[vs es] c] s] t]. 
        intros H H0 H1 Hst f' l' eM' tr' H2. unfold gpr_trace in H2.
        destruct_guard_in H2. destruct p. 
        eapply (InitialGpr (vs, es, c, s, t)) in E0 as P; eauto.
        +   destruct P, H4, H5, H6, H7, H8. 
            eapply (FlowConservationGpr (vs, es, c, s, t)) in H2; eauto.
        -   destruct H2, H10, H11, H12, H13. split; auto. split; auto.
            rewrite NMap.FindReplaceEq in H13.
            rewrite NMap.FindReplaceNeq, NMap.FindEmpty in H14; auto.
        -   unfold NoSteepArc. intros. destruct (equal u s).
        *   subst. rewrite NMap.FindReplaceEq.
            destruct (equal v s);
                [subst;rewrite NMap.FindReplaceEq;lia|].        
            unfold PreFlowCond in H8. 
            eapply InitialPushResCap0 with (v := v) in E0; auto.
            lra.
        *   rewrite NMap.FindReplaceNeq, NMap.FindEmpty; auto. lia.
        -   unfold ValidLabeling. intros. 
            destruct (equal u s), (equal v s).
        *   subst. lia.
        *   subst. unfold PR.E in H10. eapply ESet.in_filter in H10. 
            destruct H10.
            eapply InitialPushResCap0 with (v := v) in E0; auto.
            unfold res_cap in E0. rewrite H10 in E0. 
            eapply (reflect_iff _ _ (QLt_spec _ _)) in H11. lra.
         *  subst. rewrite NMap.FindReplaceNeq, NMap.FindEmpty; auto. lia.
         *  rewrite NMap.FindReplaceNeq, NMap.FindEmpty; auto. lia.
    Qed.
End PR.

Module Nat <: T.
    Definition V := nat.
    Definition eqb := Nat.eqb.
    Lemma equal: forall x y, reflect (x=y) (eqb x y).
    Proof.
        induction x; destruct y; cbn; try constructor; auto.
        destruct (IHx y); subst; constructor; auto.
    Defined.
    Lemma eqb_refl u: eqb u u = true.
    Proof. destruct (equal u u); auto. Qed. 
    Lemma eqb_neq u v: u<>v -> eqb u v = false.
    Proof. intros. destruct (equal u v); auto. contradiction. Qed. 
End Nat.

Module Edge := Tuple (Nat) (Nat).
Module EMap := Map (Edge).
Module VSet := MkSet (Nat).
Module ESet := MkSet (Edge).
Module VMap := Map (Nat).

Module PRNat := PR (Nat) (Edge) (EMap) (VSet) (ESet) (VMap).

Import ListNotations.
Open Scope nat.

(* Näited, et algoritm tagastab korrektse maksimaalse voo*)
Definition FN1 : PRNat.FlowNet := 
    let c := fun (x y: nat) => 10%Q in
    (([0;1],[(0,1)]),c,0,1).


Definition FN2 : PRNat.FlowNet := 
    let c := fun (x y: nat) => 
        match x, y with
        | 0, 1 => 15%Q
        | 0, 3 => 4%Q
        | 1, 2 => 12%Q
        | 2, 3 => 3%Q
        | 2, 5 => 7%Q
        | 3, 4 => 10%Q
        | 4, 1 => 5%Q
        | 4, 5 => 10%Q
        | _, _ => 0%Q
        end
    in
    (([0;1;2;3;4;5],[(0,1);(0,3);(1,2);(2,3);(2,5);(3,4);(4,1);(4,5)]),c,0,5).

Definition FN3 : PRNat.FlowNet := 
    let c := fun (x y: nat) => 
        match x, y with
        | 0, 1 => 4%Q
        | 0, 2 => 2%Q
        | 1, 3 => 4%Q
        | 2, 4 => 2%Q
        | 3, 5 => 4%Q
        | 4, 5 => 2%Q
        | _, _ => 0%Q
        end
    in
    (([0;1;2;3;4;5],[(0,1);(0,2);(1,3);(1,4);(2,4);(3,5);(4,5)]),c,0,5).

(* Compute (PRNat.gpr_trace FN1).

Compute (PRNat.gpr_trace FN2).

Compute (@PRNat.excess FN1 [(0,1,10%Q)] 1).

Compute (@PRNat.excess FN2 [(0, 1, 15%Q); (0, 3, 4%Q); (3, 4, 10%Q); (
    4, 1, 5%Q); (1, 2, 12%Q); (2, 5, 7%Q); (
    4, 5, 10%Q); (2, 3, 3%Q)] 5).

Compute (@PRNat.excess FN3 [(0, 1, 4%Q); (0, 2, 2%Q); 
(2, 4, 2%Q); (4, 5, 2%Q); (1, 3, 4%Q); (3, 5, 4%Q)] 5). *)

Definition FN_excess : (list nat * list (nat * nat) * (nat -> nat -> Q) * nat * nat)%type :=
  let c := fun (x y : nat) =>
    match x, y with
    | 0, 5 => 19%Q
    | 1, 2 => 19%Q
    | 1, 4 => 13%Q
    | 2, 3 => 2%Q
    | 3, 4 => 8%Q
    | 3, 6 => 2%Q
    | 4, 2 => 18%Q
    | 5, 1 => 5%Q
    | 5, 2 => 10%Q
    | _, _ => 0%Q
    end
  in
  (([0;1;2;3;4;5;6],[(0,5);(1,2);(1,4);(2,3);(3,4);(3,6);(4,2);(5,1);(5,2)]), c, 0, 6).

(* Compute (@PRNat.excess FN_excess [(0, 5, 19%Q);
(1, 2, 19%Q);
(1, 4, 13%Q);
(2, 3, 2%Q);
(3, 4, 8%Q);
(3, 6, 2%Q);
(4, 2, 18%Q);
(5, 1, 5%Q);
(5, 2, 10%Q)] 6). *)

(* Ekstraheerimine *)

Extraction Language OCaml.
Require Import ZArith.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlZInt.
Require Import ExtrOcamlNatInt.
Extract Inductive Q => "(int * int)" [ "" ].
Set Extraction File Comment "Extracted from the push-relabel algorithm proof in Rocq.".


(* Extract Constant VMap.t "'e" => "'e VerticeMap'.t".
Extract Constant VMap.empty => "fun _d -> VerticeMap'.empty".
Extract Constant VMap.find => 
    "fun d m k -> 
    try VerticeMap'.find k m with Not_found -> d".
Extract Constant VMap.replace => "fun _d k v m -> VerticeMap'.add k v m".
Extract Constant VMap.update => 
    "fun _d k f m -> 
        let old = VerticeMap'.find k m 
        in VerticeMap'.add k (f old) m".
Extract Constant EMap.t "'e" => "'e EdgeMap'.t".
Extract Constant EMap.empty => "fun _d -> EdgeMap'.empty".
Extract Constant EMap.find => 
    "fun d m k -> 
    try EdgeMap'.find k m with Not_found -> d".
Extract Constant EMap.replace => "fun _d k v m -> EdgeMap'.add k v m".
Extract Constant EMap.update => 
    "fun d k f m -> 
    let old = try EdgeMap'.find k m with Not_found -> d 
    in EdgeMap'.add k (f old) m". *)

Extract Constant VMap.t "'e" => "'e VerticeMap'.t".
Extract Constant VMap.empty => "fun _d -> VerticeMap'.create 1".
Extract Constant VMap.find => 
    "fun d k m -> 
    try VerticeMap'.find k m with Not_found -> d".
Extract Constant VMap.replace => "fun _d k v m -> VerticeMap'.replace m k v; m".
Extract Constant VMap.update => 
    "fun d k f m -> 
        let old = try VerticeMap'.find m k with Not_found -> d
        in VerticeMap'.replace m k (f old); m".
Extract Constant EMap.t "'e" => "'e EdgeMap'.t".
Extract Constant EMap.empty => "fun _d -> EdgeMap'.create 1".
Extract Constant EMap.find => 
    "fun d k m -> 
    try EdgeMap'.find k m with Not_found -> d".
Extract Constant EMap.replace => "fun _d k v m -> EdgeMap'.replace m k v; m".
Extract Constant EMap.update => 
    "fun d k f m -> 
        let old = try EdgeMap'.find m k with Not_found -> d
        in EdgeMap'.replace m k (f old); m".

(* Extract Constant VSet.t => "VerticeSet'.t".
Extract Constant VSet.empty => "VerticeSet'.empty".
Extract Constant VSet.remove => "fun v xs -> VerticeSet'.remove v xs".
Extract Constant VSet.add => "fun v xs -> VerticeSet'.add v xs".
Extract Constant VSet.mem => "fun v xs -> VerticeSet'.mem v xs".
Extract Constant VSet.choice => "fun xs -> VerticeSet'.choose xs".
Extract Constant VSet.filter => "fun f xs -> VerticeSet'.filter f xs".
Extract Constant VSet.fold_left => "fun f xs acc -> VerticeSet'.fold f xs acc". *)

Recursive Extraction PRNat.gpr_trace.

(* Extract Constant ESet.t => "(int * int) Queue.t".
Extract Constant ESet.empty => "Queue.create ()".
Extract Constant ESet.remove => "fun v xs -> EdgeSet'.remove v xs".
Extract Constant ESet.add => "Queue.push".
Extract Constant ESet.mem => 
    "fun x xs -> 
    let found = ref false in 
    Queue.iter (fun y -> if y = x then found := true) xs;
    !found".
Extract Constant ESet.choice => "Queue.pop".
Extract Constant ESet.filter =>
"fun f xs -> 
    let xs' = Queue.create () in
    Queue.iter (fun x -> if f x then Queue.push x xs') xs;
    xs'". *)
(* Extract Constant ESet.fold_left => "Queue.fold". *)
(* Extract Constant PR_nat.Nat.t => "int".
Extract Constant PR_nat.Nat.compare => "Nat.compare".
Extract Constant Edge.t => "(int * int)".
Extract Constant Edge.compare => "compare". *)

(* Set Extraction AccessOpaque. *)
Extraction ESet.



(* Näited erinevatest arvutüüpidest *)

Definition example_Q : Q := (7#12).
Definition example_Q2 : Q := 6.
Definition example_Z : Z := 45.
Definition example_pos : positive := 5.
Definition example_nat : nat := 10.
Definition example_R : PRNat.R := 6%Q.
Extraction example_nat.

(* Transpordivõrgu FN2 ekstraheerimine *)

(* 5 katse põhjal keskmine ajakuju FN2 võrgul:
Algne: 0.0994ms
Muudatused 1: 0.0752ms
Muudatused 2: 0.067ms

1: täis- ja ratsionaalarvud muudetud + tõeväärtused, listid jne (OCamlBasic jne)
2: VMap ja EMap asemel OCamli mapid/paisktabelid.
*)

Recursive Extraction PRNat.gpr_trace.

(* dune exec push-relabel *)