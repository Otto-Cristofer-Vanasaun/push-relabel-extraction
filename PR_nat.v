Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.QOrderedType.
Require Import Coq.QArith.Qminmax.
Require Import Coq.QArith.QOrderedType.
Require Import Lia. (*tactic: lia*)
Require Import Lqa. (*tactic: lra*)
Require Extraction.

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

Module Nat <: T.
    Definition V := nat.
    Definition eqb := Nat.eqb.
    Lemma equal: forall x y, reflect (x=y) (eqb x y).
    Proof.
        induction x; destruct y; cbn; try constructor; auto.
        destruct (IHx y); subst; constructor; auto.
    Qed.
    Lemma eqb_refl u: eqb u u = true.
    Proof. destruct (equal u u); auto. Qed. 
    Lemma eqb_neq u v: u<>v -> eqb u v = false.
    Proof. intros. destruct (equal u v); auto. contradiction. Qed. 
End Nat.

Module Type MapSpec (T:T).
    Import T.
    (* Arvutamine *)
    Parameter t: forall (e:Type) {d:e}, Type.
    Parameter empty: forall {e:Type} (d:e), @t e d.
    Parameter replace: forall {e:Type} {d:e}, V -> e -> @t e d -> @t e d.
    Parameter find: forall {e:Type} (d:e), @t e d -> V -> e.
    Parameter update: forall {e:Type} {d:e}, V -> (e->e) -> @t e d -> @t e d. 
    Notation "m [ v ]" := (find m v) (at level 12). 
    (* Omadused *)
    Parameter FindUpdateEq: forall {e d} {f:e->e} (xs:@t e d) u,
        find d (update u f xs) u = f (find d xs u) .
    Parameter FindUpdateNeq: forall {e d} {f:e->e} (xs:@t e d) u v , u<>v -> 
        find d (update v f xs) u = find d xs u .

    Parameter FindReplaceEq: forall {e d} {f:e} (xs:@t e d) u,
        find d (replace u f xs) u = f .

    Parameter FindReplaceNeq: forall {e d} {f:e} (xs:@t e d) u v, u<>v -> 
        find d (replace v f xs) u = find d xs u .
    
    Parameter FindEmpty: forall {e} {d:e} k, find d (empty d) k = d.
End MapSpec.

Module MkMap (T:T) <: MapSpec (T).
    Import T.
    Definition t (e:Type) {d:e} := list (V * e).
    
    Definition empty {e:Type} d: @t e d:= nil.

    (* Eemaldab tipu v järjendist xs, kui see seal leidub *)
    Fixpoint remove {e:Type} d (v:V) (xs: @t e d) : @t e d :=
        match xs with 
        | nil => nil
        | ((u,y)::xs) => 
            if eqb v u then 
                remove d v xs 
            else 
                (u,y)::(remove d v xs)
        end.

    (* Asendab tipu v järjendis xs, kui see seal leidub *)
    Fixpoint replace {e:Type} d (v:V) (x:e) (xs:@t e d) := 
        match xs with
        | nil => (v,x)::nil
        | ((u,y)::xs) => 
            if eqb v u then 
                (u,x)::(remove d v xs) 
            else 
                (u,y)::(replace d v x xs)
        end.

    (* Uuendab tipust väljuvaid servasid, kui antud tipp leidub xs-is *)
    Fixpoint update {e:Type} d (v:V) (f:e->e) (xs:@t e d) := 
        match xs with
        | nil => (v,f d)::nil
        | ((u,y)::xs) => 
            if eqb v u then 
                (u,f y)::(remove d v xs) 
            else 
                (u,y)::(update d v f xs)
        end.
    
    Fixpoint find {e:Type} d (xs:@t e d) (v:V) := 
        match xs with
        | nil => d
        | ((u,y)::xs) => 
            if eqb v u then 
                y
            else 
                find d xs v
        end.
    
    Lemma FindEmpty: forall {e} {d:e} k, find d (empty d) k = d.
    Proof.
        intros. cbn. reflexivity.
    Qed.
        Lemma FindRemoveEq {e d} {f:e->e} (xs:t e) u  :  
        find d (remove d u xs) u = d.
    Proof.
        intros. induction xs.
        + simpl. reflexivity.
        + simpl. destruct a.
        - destruct (equal u v).
        * auto.
        * simpl. rewrite -> eqb_neq; auto.
        Qed.

    Lemma FindRemoveNeq {e d} (xs:t e) u v  : u<>v -> 
        find d (remove d v xs) u = find d xs u .
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
        find d (replace d u f xs) u = f .
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
        find d (replace d v f xs) u = find d xs u .
    Proof.
        intros. induction xs.
        + simpl. destruct (equal u v); auto.
        - contradiction.
        + simpl. destruct a. destruct (equal v v0).
        - simpl. subst. rewrite -> eqb_neq; auto.
        * rewrite -> FindRemoveNeq; auto. 
        - simpl. destruct (equal u v0); auto.
        Qed.
End MkMap.

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
    Qed.
    Lemma eqb_refl u: eqb u u = true.
    Proof. destruct (equal u u); auto. Qed. 
    Lemma eqb_neq u v: u<>v -> eqb u v = false.
    Proof. intros. destruct (equal u v); auto. contradiction. Qed. 
End Tuple.

Module PR
    (T:T) 
    (Edge : Product (T) (T)) 
    (EdgeMap : MapSpec (Edge))
    (VertexMap : MapSpec (T))
    (ExcessMap : MapSpec (T))
    (EdgeSet : SetSpec (Edge))
    (VertexSet : SetSpec (T))
    .
    
    (* Sisend *)
    Import T.
    Definition R := Q.

    Declare Scope EdgeMap.
    
    Notation "m '[' v ']'" := (EdgeMap.find m v) (at level 12):EdgeMap. 
    Open Scope EdgeMap.

    Notation "v '∈v' s" := (VertexSet.mem v s) (at level 12). 

    Notation "v '∈e' s" := (EdgeSet.mem v s) (at level 12). 

    (* Graaf, mis koosneb tippude ja servade hulkadest*)
    Definition Graph := (VertexSet.t * EdgeSet.t)%type.
    (* Definition Graph := (list Nat.V * list Edge.V)%type. *)

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
        unfold QLt. destruct_guard; constructor; lra.
    Qed.

    Lemma QLt_false x y: (x <? y)%Q = false <-> y<=x .
    Proof. unfold QLt. destruct (Qlt_le_dec x y); split; intros.
    all: auto.
    all: try inversion H. lra.
    Qed.


    Definition QSumList :=
        fold_right Qplus 0 .
    
    (* Arvutab transpordivõrgu fn, millel on eelvoog f, tipu x ülejäägi.
    Algoritmi töö alguses on iga tipu ülejääk -1.
    Ülejäägi arvutamiseks lahutatakse sissetulevate kaarte eelvoogudest maha väljaminevate kaarte eelvood.
    Pärast arvutamist ülejääk salvestatakse ja järgmiste väljakutsete korral kasutatakse meeldejäetud tulemust.*)
    (* Definition excess_update (fn:FlowNet) (f: @EdgeMap.t R 0) (e: @ExcessMap.t R 0) (u: Nat.V) : @ExcessMap.t R 0 :=
        let '((vs, es),c,s,t) := fn in
        let updated_excess := QSumList (map (fun v => f[(v,u)]) vs) - QSumList (map (fun v => f[(u,v)]) vs) in
        ExcessMap.replace u updated_excess e. *)

    (* Vähendab tipu u ülejääki delta võrra ja suurendab tipu v ülejääki delta võrra,
        aga ei lase tpiu ülejäägil negatiivseks minna (vajalik initsialiseerimise juures) *)
    Definition excess_update e u delta : V -> ExcessMap.t R :=
        fun v =>
            let old_excess_u := ExcessMap.find 0 e u in
            let old_excess_v := ExcessMap.find 0 e v in
            let new_map_u := ExcessMap.replace u (old_excess_u - delta) e in
            ExcessMap.replace v (old_excess_v + delta) new_map_u.

    (* Leiab lõpptipu ülejäägi ehk maksimaalse voo transpordivõrgus *)
    Definition max_flow (fn: FlowNet) (f: EdgeMap.t R) : R :=
        let '((vs,es),c,s,t) := fn in
        QSumList (map (fun v => EdgeMap.find 0 f (v,t)) (VertexSet.to_list vs)) - 
        QSumList (map (fun v => EdgeMap.find 0 f (t,v)) (VertexSet.to_list vs)).

    (* Arvutab välja serva (u, v) alles oleva läbilaskevõime ja tagastab selle. 
    c u v tähistab serva läbilaskevõimet ja f[(u,v)] serva voogu. 
    Tingimus (u,v) ∈e es tagastab tõeväärtuse true, siis kui serv (u, v) kuulub servade hulka es.
    Kui serv (u, v) ei kuulu servade hulka, siis tagastatakse voog, mis läheb tagurpidi ehk serva (v, u) voog.*)
    Definition res_cap (fn: FlowNet) (f: EdgeMap.t R) u v : R :=
        let '((vs, es),c,s,t) := fn in
        if (u,v) ∈e es then
            c u v -  EdgeMap.find 0 f (u,v)
        else 
            EdgeMap.find 0 f (v,u)
    .

    Definition E (fn: FlowNet) (f: EdgeMap.t R) :=
        let '((vs, es),c,s,t) := fn in
        EdgeSet.filter (fun '(u, v) => EdgeMap.find 0 f (u,v) <? c u v) es.    
    
    Definition res_net (fn: FlowNet) (f: EdgeMap.t R) : FlowNet :=
        let '((vs, es),c,s,t) := fn in
        ((vs,E fn f),res_cap fn f,s,t).

    (* valib tipu u ülejäägist ning läbilaskevõimest Qmin abil miinimumi ja saadab selle voona edasi järgmisesse tippu v.
     Kui (u,v) ∈e es ehk serv (u, v) kuulub hulka es tagastab true, siis suurendatakse serva (u, v) voogu delta võrra. 
     False korral vähendatakse serva (v, u) voogu delta võrra.
     Töö käigus uuendatakse ka tippude ülejääkide andmestruktuuri. *)
    Definition push fn f e u v : (EdgeMap.t R * ExcessMap.t R) :=
        let '((vs, es),c,s,t) := fn in
        let excess_value := ExcessMap.find 0 e u in
        let delta := Qmin excess_value (res_cap fn f u v) in
        let new_excessmap := excess_update e u delta v in
        if (u,v) ∈e es  then
             ((EdgeMap.update (u,v) (fun x=>x+delta) f), new_excessmap)
        else 
            ((EdgeMap.update (v,u) (fun x=>x-delta) f), new_excessmap)
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
            if (VertexMap.find 0 l r <=? VertexMap.find 0 l v)%nat 
                then smallest_rank l xs (Some r)
                else smallest_rank l xs (Some v)
        end.

    (* Filtreerib välja tipud, mille vahel on läbilaskevõime ära kasutatud ja jätab alles tipud, mille vahel on läbilaskevõime olemas. 
    Peale seda otsib, kas leiab tipu r, mille kõrgus on väiksem või võrdne tipu v kõrgusega. 
    Kui tipu r kõrgus on väiksem või võrdne tipu v kõrgusega siis tagastatakse tipp r, vastasel juhul tagastatakse tipp v. *)
    Definition relabel_find fn f (l: @VertexMap.t nat O) u vs := 
        let fvs := VertexSet.filter (fun v => 0 <? res_cap fn f u v) vs in
        smallest_rank l (VertexSet.to_list fvs) None.
    
    (* Suurendab tipu u kõrgust 1 võrra, leides naabertippude hulgast kõige väiksema kõrgusega tipu.
       Kui leitakse vastab tipp, siis asendatakse tipu u kõrgust leitud kõrguses 1 võrra suuremaga.
       Kui sobivat tippu ei leidu ehk saadakse väärtus None, siis relabel nurjub.
       See juhtum aga algoritmi töö käigus kunagi ei realiseeru.*)
    Definition relabel fn f (l: @VertexMap.t nat O) u : option (VertexMap.t nat):=
        let '((vs, es),c,s,t) := fn in
        match relabel_find fn f l u vs with
        | None => None
        | Some n => Some (VertexMap.replace u (1+ VertexMap.find 0 l n)%nat l)
        end.

    (* Otsib tippude vs’ hulgast tippu v, kuhu saaks voogu saata ning 
       mis oleks tipu u kõrgusest 1 võrra kõrgemal ja servade (u, v) vahel oleks veel läbilaskevõimet. *)
    Definition find_push_node fn f (l: @VertexMap.t nat O) u (vs': VertexSet.t) :=
        let '((vs, es),c,s,t) := fn in
        VertexSet.find_first (fun v => 
            (VertexMap.find 0 l u =? 1+ VertexMap.find 0 l v)%nat &&
                (0 <? res_cap fn f u v)) vs'.

    (* Kontrollib, et antud tipp v ei oleks väljund ega sisend ja ülejääk oleks suurem kui 0. 
    T.eqb tagastab tõeväärtuse true, siis kui argumentideks antud tipud on võrdsed ning 
    0 <? Excess fn f v tagastab true väärtuse, siis kui tipu v ülejääk on suurem kui 0. *)
    Definition has_excess_not_sink (fn: FlowNet) (e: ExcessMap.t R) v :=
        let '((_, _),_,s,t) := fn in
        if T.eqb v t || T.eqb v s then
            false
        else if 0 <? ExcessMap.find 0 e v then 
            true
        else
            false
    .

    Inductive Tr : Type :=
        | Init: @EdgeMap.t Q 0 -> @ExcessMap.t R 0 -> @VertexMap.t nat O -> VertexSet.t ->  Tr
        | Push: V -> V -> @EdgeMap.t Q 0 -> @ExcessMap.t R 0 -> VertexSet.t ->  Tr
        | Relabel : V -> nat -> @VertexMap.t nat O ->  Tr
        | OutOfGas
        | RelabelFailed
        .

    (* Leiab graafis maksimaalse voo, kasutades push ja relabel samme, ning tagastab selle.
        Kui graafis pole tippe või servasid, siis tagastab väärtuse None. *)
    Fixpoint gpr_helper_trace fn f e l ac g tr: (option (EdgeMap.t Q * VertexMap.t nat)*list Tr) :=
        let '((vs, es),c,s,t) := fn in
        match g with
        | O => (None, OutOfGas::tr)
        | S g' => 
            match VertexSet.choice ac with
            | None => (Some (f,l),tr)
            | Some (u,ac') =>
            match find_push_node fn f l u vs with
            | Some v =>
                let (f',e') := push fn f e u v in
                let ac' := if 0 <? (ExcessMap.find 0 e' u) then ac else ac' in
                if has_excess_not_sink fn e' v then 
                    let ac'' := VertexSet.add v ac' in
                    gpr_helper_trace fn f' e' l ac'' g' (Push u v f' e' ac''::tr)
                else 
                    let ac'' := VertexSet.remove v ac' in
                    gpr_helper_trace fn f' e' l ac'' g' (Push u v f' e' ac'::tr)
            | None =>
                match relabel fn f l u with
                | None => (None, RelabelFailed::tr)
                | Some l' =>
                    gpr_helper_trace fn f e l' ac g' (Relabel u (VertexMap.find 0 l' u)%nat l'::tr)
                end
            end
            end 
        end.
    
    Lemma gpr_helper_trace_fn fn f e l ac g tr : 
        gpr_helper_trace fn f e l ac g tr =
            let '((vs, es),c,s,t) := fn in
            match g with
            | O => (None, OutOfGas::tr)
            | S g' => 
                match VertexSet.choice ac with
                | None => (Some (f,l),tr)
                | Some (u,ac') =>
                match find_push_node fn f l u vs with
                | Some v =>
                    let (f',e') := push fn f e u v in
                    let ac' := if 0 <? (ExcessMap.find 0 e' u) then ac else ac' in
                    if has_excess_not_sink fn e' v then 
                        let ac'' := VertexSet.add v ac' in
                        gpr_helper_trace fn f' e' l ac'' g' (Push u v f' e' ac''::tr)
                    else 
                        let ac'' := VertexSet.remove v ac' in
                        gpr_helper_trace fn f' e' l ac'' g' (Push u v f' e' ac'::tr)
                | None =>
                    match relabel fn f l u with
                    | None => (None, RelabelFailed::tr)
                    | Some l' =>
                        gpr_helper_trace fn f e l' ac g' (Relabel u (VertexMap.find 0 l' u)%nat l'::tr)
                    end
                end
                end 
            end.
    Proof. destruct g; auto. Qed.

    (* Teeb push-relabel algoritmi initsialiseerimise ühe sammu, milleks on 
    sisendtipust väljuvatele servadele voo saatmine, kasutades ära serva kogu läbilaskevõime. *)
    (* Fixpoint initial_push fn f e ac es: (@EdgeMap.t R 0*@ExcessMap.t R 0*list Nat.V) :=
        let '((_, _),c,s,t) := fn in
        match es with
        | nil => (f,e,ac)
        | (u,v)::es => 
            if Nat.eqb s u then 
                let f' := EdgeMap.replace (u,v) (c u v) f in
                let e' := ExcessMap.replace v (c u v) e in
                let ac := 
                    if has_excess_not_sink fn e' v then 
                        (VertexSet.add v ac) 
                    else 
                        ac 
                in
                initial_push fn f' e' ac es  
            else
                initial_push fn f e ac es
        end. *)
    Definition initial_push fn (e: @ExcessMap.t R 0): (EdgeMap.t Q * ExcessMap.t R * VertexSet.t) :=
        let '((_, es),c,s,t) := fn in
        let es' := EdgeSet.to_list (EdgeSet.filter (fun '(u,v) => T.eqb s u ) es) in
        fold_left (fun  '(f, e, ac) '(u,v) => 
                let f' := EdgeMap.replace (u,v) (c u v) f in
                let e' := ExcessMap.replace v (c u v) e in
                let ac := 
                    if has_excess_not_sink fn e v then 
                        (VertexSet.add v ac) 
                    else 
                        ac 
                in
                (f', e', ac)
        ) es' (@EdgeMap.empty R 0, @ExcessMap.empty R 0, VertexSet.empty).


    (* Algväärtustab graafi, muutes tippude kõrgused nii, et tipp s on kõrgusega length vs ja kõik teised tipud kõrgusega 0. 
    Seejärel toestab algse push sammu tipust s väljuvate servade peal. 
    Lõpus kutsutakse välja Fixpoint gpr_helper_trace, mis leiab maksimaalse voo ja tagastab leitud väärtuse funktsioonile gpr_trace.*)
    Definition gpr_trace (fn:FlowNet): (option (EdgeMap.t Q * VertexMap.t nat)*list Tr) :=
        let '((vs, es),c,s,t) := fn in
        let vs_size := VertexSet.size vs in
        let labels := VertexMap.replace s vs_size (@VertexMap.empty nat O) in
        let bound := (EdgeSet.size es * vs_size * vs_size)%nat in
        let '(f, e, active) := initial_push fn (@ExcessMap.empty R 0) in
        gpr_helper_trace fn f e labels active bound (Init f e labels active :: nil).
    
    (* Iga serva korral ei ole voog suurem kui läbilaskevõime *)
    Definition CapacityConstraint (fn:FlowNet) (f: @EdgeMap.t Q 0) := 
        let '((vs, es),c,s,t) := fn in
        forall u v, EdgeSet.mem (u,v) es = true -> 
            EdgeMap.find 0 f (u,v) <= c u v.
    
    (* Tagastab true, kui igas tipus v, mis ei ole sisend, on ülejääk mittenegatiivne *)
    Definition NonDeficientFlowConstraint (fn:FlowNet) (f: @EdgeMap.t Q 0) (e: @ExcessMap.t Q 0) := 
        let '((vs, es),c,s,t) := fn in
        forall v, (v ∈v vs) = true -> v<>s -> 0 <= ExcessMap.find 0 e v.

    (* Tagastab true kui igas tipus v.a sisendis ja väljundis on ülejääk 0.  *)
    Definition FlowConservationConstraint (fn:FlowNet) (f: @EdgeMap.t Q 0) (e:ExcessMap.t Q) := 
        let '((vs, es),c,s,t) := fn in
        forall v, (v ∈v vs) = true -> v<>s -> v<>t -> ExcessMap.find 0 e v == 0.
    
    (* Tagastab true kui on täidetud eelvoo nõuded *)
    Definition PreFlowCond (fn:FlowNet) (f: @EdgeMap.t Q 0) (e:ExcessMap.t Q) := 
            CapacityConstraint fn f /\ NonDeficientFlowConstraint fn f e. 

    (* Tagastab true kui voog ja läbilaskevõime on mittenegatiivsed *)
    Definition FlowMapPositiveConstraint (fn:FlowNet) (f: @EdgeMap.t Q 0) := 
        let '((vs, es),c,s,t) := fn in
        forall u v, EdgeMap.find 0 f (u,v) >= 0 /\ c u v >= 0.
    
    (* Tagastab true, kui tipp v on tippude hulgas ja omab ülejääki *)
    Definition ActiveNode (fn:FlowNet) (f: @EdgeMap.t Q 0) (e:ExcessMap.t Q) v := 
        let '((vs, es),c,s,t) := fn in
        (v ∈v vs) = true /\ ExcessMap.find 0 e v > 0.

    (* Tagastab true, kui iga tipu u ja v korral, kui serv (u ,v) kuulub servade hulka on tippudel u ja v korrektsed kõrgused *)
    Definition ValidLabeling  fn (f: @EdgeMap.t Q 0) (l: @VertexMap.t nat O) :=
        forall u v,
        let '((vs, es),c,s,t) := fn in
        ((u,v) ∈e E fn f) = true  ->  (VertexMap.find 0 l u <= VertexMap.find 0 l v + 1)%nat.

    Inductive CPath (fn:FlowNet) (f: @EdgeMap.t Q 0): V -> V -> Prop :=
    | Start u : CPath fn f u u
    | Step u v1 vn: ((u,v1) ∈e E fn f) = true -> CPath fn f v1 vn ->  CPath fn f u vn
    .

    (* Graafis ei leidu enam täiendavaid teid *)
    Definition NoAugPath (fn:FlowNet) (f: @EdgeMap.t Q 0) := 
        let '((vs, es),c,s,t) := fn in
        CPath fn f s t -> False.

    (* Tagastab true, kui iga tipu u ja v korral on täidetud tingimus cf (u, v) > 0, siis l(u) <= l(v) + 1 *)
    Definition NoSteepArc (fn:FlowNet) (f: @EdgeMap.t Q 0) (l: @VertexMap.t nat O):=
        forall u v,
        res_cap fn f u v > 0 -> (VertexMap.find 0 l u <= VertexMap.find 0 l v+1)%nat.

    (* Tagastab true iga tipu u ja v korral kui on täidetud tingimus cf (u, v) > 0 ja tipud u ja v kuuluvad transpordivõrku *)
    Definition ResCapNodes (fn:FlowNet) (f: @EdgeMap.t Q 0) :=
            forall u v,
            res_cap fn f u v > 0 -> u ∈v (nodes fn) = true /\ v ∈v (nodes fn) = true.

    (* Tagastab true, kui ei leidu tippu, kuhu saaks push sammu teha *)
    Definition NoPushCondition fn (f: @EdgeMap.t Q 0) (l: @VertexMap.t nat O) u := 
                forall v, v ∈v (nodes fn) = true -> (VertexMap.find 0 l u <> VertexMap.find 0 l v + 1)%nat.
    
    (* Tagastab true, kui push sammu eeldused on täidetud, ehk tipus on ülejääk ja järgmine tipp on 1 võrra madalamal *)
    Definition PushCondition (fn: FlowNet) (f: @EdgeMap.t Q 0) (e:ExcessMap.t Q) (l: @VertexMap.t nat O) u v := 
        ExcessMap.find 0 e u > 0 /\ (VertexMap.find 0 l u = VertexMap.find 0 l v + 1)%nat.
    
    (* Kui tippudel olid korrektsed kõrgused enne push sammu, siis ka peale push sammu on tippudel korrektsed kõrgused *)
    Lemma PushValidLabel fn (f: @EdgeMap.t Q 0) (e:ExcessMap.t Q) (l: @VertexMap.t nat O) x y:
        let '((vs, es),c,s,t) := fn in
        ValidLabeling fn f l -> PushCondition fn f e l x y (* võib-olla peaks e' asemel e olema *)
                -> ValidLabeling fn (fst (push fn f e x y)) l.
    Proof.
        intros. destruct fn as [[[[vs es] c] s] t]. unfold ValidLabeling, PushCondition.
        intros. unfold push in H1. destruct ((x, y) ∈e es) eqn : E.
        + unfold PR.E in *. apply EdgeSet.in_filter in H1. destruct H1.  
        apply H. apply EdgeSet.filter_in.
        - auto.
        - destruct (Edge.equal (x,y) (u, v)).
        * inversion e0. subst. simpl in H2. rewrite EdgeMap.FindUpdateEq in H2. 
        eapply (reflect_iff _ _ (QLt_spec _ _)). 
        eapply (reflect_iff _ _ (QLt_spec _ _)) in H2.
        unfold res_cap in H2. rewrite E in H2.
        destruct ( Q.min_dec (ExcessMap.find 0 e u) (c u v - EdgeMap.find  0 f (u, v))).
        ** rewrite q in H2. lra.
        ** rewrite q in H2. unfold R in H2. lra.
        * simpl in H2. rewrite EdgeMap.FindUpdateNeq in H2; auto.
        + unfold PR.E in *. apply EdgeSet.in_filter in H1. destruct H1.
        destruct (Edge.equal (y, x) (u, v)).
        - inversion e0. subst. lia.
        - simpl in H2. rewrite EdgeMap.FindUpdateNeq in H2; auto.
        apply H. apply EdgeSet.filter_in; auto.
        Qed.

    Definition RelabelCondition fn (f: @EdgeMap.t Q 0) (e:ExcessMap.t Q) (l: @VertexMap.t nat O) u := 
      ExcessMap.find 0 e u > 0 /\ forall v, v ∈v (nodes fn) = true -> 
      res_cap fn f u v > 0 -> (VertexMap.find 0 l u <= VertexMap.find 0 l v)%nat.


    Lemma minProp: forall a b, (min a b = a /\ a <= b)%nat \/ 
                                (min a b = b /\ b <= a)%nat.
    Proof. lia. Qed. 

    (* muudetud *)
    Lemma RFindResCapCondition fn (f: @EdgeMap.t Q 0) (l: @VertexMap.t nat O) u vs : forall vs' v,
        (VertexSet.filter (fun v0 : V => 0 <? res_cap fn f u v0) vs) = vs' ->
        (v ∈v vs') = true ->  (0 <? res_cap fn f u v) = true .
    Proof. 
        intros vs' v Hfilt Hmem. subst vs'.
        destruct (VertexSet.in_filter v 
                    (fun v0 : V => 0 <? res_cap fn f u v0) vs Hmem)
                    as [_ Hp]. apply Hp.
        Qed. 

    (* Admitted lemma *)
    (* Lemma RFindMinSomeCondition (l: @VertexMap.t nat O) vs': forall v r vs'', 
    (r ∈v vs'') = true ->
    (forall v', (v' ∈v vs'') = true -> (l[r] <= l[v'])%nat) ->
        VertexSet.fold_left (fun r v0 => 
            match r with
            | Some r0 => if (l[r0] <=? l[v0])%nat then Some r0 else Some v0
            | None => Some v0
            end) vs' (Some r) = Some v ->
        forall v', ((v' ∈v vs') = true\/(v' ∈v vs'') = true) -> (l[v] <= l[v'])%nat.
    Proof. Admitted. *)
        (* induction vs'; intros.
        + simpl in H1. inversion H1. subst. apply H0. destruct H2; auto.
        simpl in H2. inversion H2.
        + simpl in H1. destruct (l [r] <=? l [a])%nat eqn : E.
        - simpl in H2. destruct H2. 
        * destruct (equal v' a); auto.
        ** subst. assert (l[v] <= l[r])%nat. { eapply IHvs' in H1; eauto. }
        apply Nat.leb_le in E. lia.
        ** eapply IHvs' in H1; eauto.
        * assert (l[v] <= l[r])%nat. { eapply IHvs' in H1; eauto. }
        specialize (H0 v' H2). lia.
        - simpl in H2. destruct H2. 
        * destruct (equal v' a); auto.
        ** subst. assert (a ∈v (a :: vs'') = true). {simpl. rewrite eqb_refl; auto. } 
        eapply IHvs' in H1; eauto.
        intros. simpl in H4. destruct (equal v' a). subst; auto. specialize (H0 v' H4).
        apply Nat.leb_gt in E. lia.  
        ** eapply IHvs' in H1.
        *** apply H1.
        *** instantiate (1 := a::vs''). simpl. rewrite eqb_refl. reflexivity.
        *** intros. simpl in H3.  destruct (equal v'0 a).
        **** subst. lia. 
        **** apply H0 in H3. apply Nat.leb_gt in E. lia. 
        *** left. apply H2.
        * eapply IHvs' in H1.
        ** apply H1.
        ** instantiate (1 := a::vs''). simpl. rewrite eqb_refl. reflexivity.
        ** intros. simpl in H3.  destruct (equal v'0 a).
        *** subst. lia. 
        *** apply H0 in H3. apply Nat.leb_gt in E. lia. 
        ** right. simpl. destruct (equal v' a); auto.
    Qed. *)

    (* Admitted lemma *)
    (* Lemma RFindMinNoneCondition (l:@VertexMap.t nat O) vs': forall v, 
        VertexSet.fold_left (fun r v0 => 
            match r with
            | Some r0 => if (l[r0] <=? l[v0])%nat then Some r0 else Some v0
            | None => Some v0
            end) vs' None = Some v ->
        forall v', ((v' ∈v vs') = true) -> (l[v] <= l[v'])%nat.
    Proof. Admitted. *)
        (* intros. induction vs'.
        + unfold VertexSet.mem.
        + simpl in H. eapply (RFindMinSomeCondition _ _ _ a (a::nil)) in H.
        - apply H.
        - simpl. rewrite eqb_refl. reflexivity.
        - intros. simpl in H1. destruct (equal v'0 a); subst. auto.
        inversion H1.
        - simpl in H0. destruct (equal v' a).
        * subst. right. simpl. rewrite eqb_refl. reflexivity.
        * left. apply H0.
        Qed. *)

    (* Admitted lemma *)
    (* Lemma RFindMinMemCondition (l:@VertexMap.t nat O) vs': forall v, 
        VertexSet.fold_left (fun r v0 => 
            match r with
            | Some r0 => if (l[r0] <=? l[v0])%nat then Some r0 else Some v0
            | None => Some v0
            end) vs' None = Some v ->
            (v ∈v vs') = true.
    Proof. Admitted. *)
        (* intros. destruct vs'.
        + simpl in H. inversion H.
        + simpl in H. simpl. destruct (equal v v0); auto.
        generalize dependent v0. induction vs'; intros.
        - simpl in H. inversion H. destruct n. auto.
        - simpl in H. destruct ((l [v0] <=? l [a])%nat) eqn : E.
        * apply IHvs' in H; auto.  simpl. destruct (equal v a); auto.
        * simpl. destruct (equal v a); auto. apply IHvs' in H.
        ** simpl. destruct (equal v a); auto.
        ** auto.
        Qed.  *)

    Lemma smallest_rank_In: forall l xs r v,
        smallest_rank l xs (Some r) = Some v -> In v (r::xs).
    Proof.
        intros l xs. induction xs; cbn; intros; auto.
        +   inv_clear H. tauto.
        +   destruct (VertexMap.find 0 l r <=? VertexMap.find 0 l a)%nat.
        ++  apply IHxs in H. cbn in H. tauto.
        ++  apply IHxs in H. cbn in H. tauto.   
    Qed.

    Lemma smaller_rank_leq: forall l xs v0 v v' ,
        smallest_rank l xs (Some v0) = Some v ->
        (In v' xs \/ (VertexMap.find 0 l v0 <= VertexMap.find 0 l v')%nat) ->
        (VertexMap.find 0 l v <= VertexMap.find 0 l v')%nat.
    Proof.
        intros l xs. induction xs; intros v0 v v' Hs H; cbn in *.
        +   inv_clear Hs. destruct H; auto. inv_clear H.
        +  destruct (Nat.leb_spec0 (VertexMap.find 0 l v0)%nat (VertexMap.find 0 l a)%nat).
        ++  eapply IHxs with (v':=v')in Hs; auto.
            destruct H; try lia. 
            destruct H; subst; try lia.
            tauto.
        ++  eapply IHxs with (v':=v')in Hs; auto.
            destruct H; try lia. 
            destruct H; subst; try lia.
            tauto.
    Qed.

    Lemma RFindCondition fn (f: @EdgeMap.t Q 0) (l: @VertexMap.t nat O) u vs: forall v, 
      relabel_find fn f l u vs = Some v  ->
      (0 <? res_cap fn f u v) = true /\ (forall v', (v' ∈v vs) = true 
        -> (0 <? res_cap fn f u v') = true -> (VertexMap.find 0 l v <= VertexMap.find 0 l v')%nat).
    Proof.
        intros. unfold relabel_find in H. split.
        +   destruct (VertexSet.to_list (VertexSet.filter (fun v => 0<?res_cap fn f u v) vs)) eqn:E.
        ++  cbn in H. inversion H.  
        ++  cbn in H. apply smallest_rank_In in H.
            rewrite <- E in H.
            apply VertexSet.to_list_in in H. 
            apply VertexSet.in_filter in H. tauto.
        +   intros.
            destruct (VertexSet.to_list (VertexSet.filter (fun v => 0<?res_cap fn f u v) vs)) eqn:E.
        ++  cbn in H. inversion H.
        ++  cbn in H.
            eapply VertexSet.filter_in  with (p:=(fun v : V => 0 <? res_cap fn f u v)) in H0; auto.
            apply VertexSet.to_list_in in H0.
            rewrite E in H0. clear E.
            cbn in H0. destruct H0.
        +++ subst. clear -H. generalize dependent v'.
            induction l0; intros v' H.
            *   cbn in H. inv_clear H. lia.
            *   cbn in H.
                destruct ((VertexMap.find 0 l v' <=? VertexMap.find 0 l a)%nat) eqn:E.
            **  apply IHl0, H.
            **  destruct (Nat.leb_spec0 (VertexMap.find 0 l v')%nat (VertexMap.find 0 l a)%nat);
                [inversion E|].
                specialize (IHl0 _ H). lia.
        +++ eapply smaller_rank_leq; eauto.
    Qed.

    Lemma RFindMemCondition fn f (l: @VertexMap.t nat O) u vs: forall v, 
        relabel_find fn f l u vs = Some v ->
            (v ∈v vs) = true.
    Proof.        
        intros. unfold relabel_find in H. 
        set (xs:=VertexSet.to_list _) in H.
        destruct xs eqn:E.
        + simpl in H. inversion H.
        + simpl. cbn in H. apply smallest_rank_In in H.
          rewrite <- E in H.
          apply VertexSet.to_list_in in H.
          apply VertexSet.in_filter in H. tauto.
    Qed.

    (* Kui enne relabel sammu olid tippudel korrektsed kõrgused, siis peale relabel sammu on samuti tippudel korrektsed kõrgused *)
    Lemma RelabelValidLabel fn (f: @EdgeMap.t Q 0) (e:ExcessMap.t Q) (l: @VertexMap.t nat O) x l':
        let '((vs, es),c,s,t) := fn in
        (forall u v , ((u, v) ∈e es = true) -> (u ∈v vs) = true /\ (v ∈v vs) = true) ->
        ValidLabeling fn f l -> RelabelCondition fn f e l x 
            -> relabel fn f l x = Some l' -> ValidLabeling fn f l'.
    Proof.
        intros. destruct fn as [[[[vs es] c] s] t]. unfold ValidLabeling, RelabelCondition.
        intros R. intros. unfold relabel in H1. 
        destruct (relabel_find (vs, es, c, s, t) f l x vs) eqn:E0;
            [| inversion H1].
        inversion H1. clear H1 H4. apply H in H2 as P. unfold PR.E in H2. 
        apply EdgeSet.in_filter in H2. destruct H2. destruct H0. 
        apply RFindMemCondition in E0 as P1. apply RFindCondition in E0.
        destruct E0. eapply (reflect_iff _ _ (QLt_spec _ _)) in H4. apply H3 in H4 as P2.
        destruct (equal x u); destruct (equal x v); subst.
        + erewrite -> VertexMap.FindReplaceEq. lia.
        + erewrite -> VertexMap.FindReplaceEq; erewrite -> VertexMap.FindReplaceNeq. 
        - assert ((VertexMap.find 0 l v0) <= VertexMap.find 0 l v)%nat. { apply H5. + edestruct R; eauto. + unfold res_cap.
        rewrite H1. eapply (reflect_iff _ _ (QLt_spec _ _)).
        eapply (reflect_iff _ _ (QLt_spec _ _)) in H2. lra.
        } lia.
        - symmetry. auto.
        + erewrite -> VertexMap.FindReplaceEq; erewrite -> VertexMap.FindReplaceNeq.
        - lia.
        - symmetry; auto.
        + erewrite -> VertexMap.FindReplaceNeq. 
        - erewrite -> VertexMap.FindReplaceNeq. lia. symmetry; auto.
        - symmetry; auto.
        + auto.
    Qed.

    (* Kui tippudel on korrektsed kõrgused ning leidub aktiivseid tippe ja leidub tipp kuhu saab push sammu teha, siis järledub, et 
    on täidetud push sammu eeldused. *)
    Lemma FPNCondition fn f e l u vs': 
        (u ∈v nodes fn) = true -> forall v, 
        ValidLabeling fn f l -> ActiveNode fn f e u ->
        find_push_node fn f l u vs' = Some v -> PushCondition fn f e l u v.
    Proof.
        unfold PushCondition, ValidLabeling, ActiveNode. intros. 
        destruct fn as [[[[vs es] c] s] t]. split.
        + apply H1; apply H.
        +   unfold find_push_node in H2.
            apply VertexSet.find_first_specSome in H2.
            destruct H2. apply andb_true_iff in H2.
            destruct H2. 
            destruct (Nat.eqb_spec (VertexMap.find 0%nat l u) (1 + VertexMap.find 0%nat l v)); [|inversion H2]. 
            lia.
    Qed.

    Lemma SumSame (f: @EdgeMap.t Q 0) (s:V->V*V) vs u v d : 
        (forall v0,  In v0 vs -> s v0 <> (u, v)) ->
        map (fun v0 => EdgeMap.find 0 
            (EdgeMap.update (u, v) (fun x0 => x0 + d) f) 
            (s v0)) vs = 
        map (fun v0 => EdgeMap.find 0 f (s v0)) vs.
    Proof.
        induction vs; intros.
        + simpl. auto.
        + simpl. erewrite IHvs; auto.
        f_equal. clear IHvs. erewrite EdgeMap.FindUpdateNeq.
        - auto.
        - apply H. cbn. auto.
        - intros. apply H. cbn. tauto.
    Qed.

    Lemma PushActiveCondition (fn:FlowNet) (f:EdgeMap.t R) (e:ExcessMap.t Q) u v x: 
        let (f',e') := push fn f e u v in
        ActiveNode fn f e x -> x<>v -> x<>u -> ActiveNode fn f' e' x .
    Proof. Admitted.
            (* unfold ActiveNode. destruct fn as [[[[vs es] c] s] t]. intros.
            unfold push. destruct ((u, v) ∈e es) eqn : E.
            + intros. set (d := Qmin _ _). unfold excess_update. split. 
                - apply H. 
                - rewrite SumSame.
            - rewrite SumSame.
            * apply H. 
            * intros v0 _ q. inversion q. subst. apply H1. auto.
            - intros v0 _ q. inversion q. subst. apply H0. auto. 
            +  set (d := Qmin _ _). unfold excess. unfold Qminus. rewrite SumSame.
            - rewrite SumSame.
            * apply H.
            * intros v0 _ q. inversion q. subst. apply H0. auto.
            - intros v0 _ q. inversion q. subst. apply H1. auto. 
        Qed. *)

    
    Lemma DeltaPositive fn (f: @EdgeMap.t Q 0) (e:ExcessMap.t Q) (l: @VertexMap.t nat O) u v:
        let '((vs, es),c,s,t) := fn in
        (u ∈v vs) = true -> 
        FlowMapPositiveConstraint fn f ->
        PreFlowCond fn f e -> 
        PushCondition fn f e l u v ->
        Qmin (ExcessMap.find 0 e u) (res_cap fn f u v) >= 0.
        Proof.
            unfold FlowMapPositiveConstraint, PreFlowCond, PushCondition.
            destruct fn as [[[[vs es] c] s] t]. unfold CapacityConstraint, NonDeficientFlowConstraint.
            intros. destruct H2. edestruct (Q.min_spec_le); destruct H4; rewrite H5; try lra.
            unfold res_cap. destruct ((u, v) ∈e es) eqn : E.
            + destruct H1. specialize (H1 _ _ E). unfold R in *. lra.
            + apply H0.
        Qed.

    Lemma PushFlowMapPos fn (f: @EdgeMap.t Q 0) (e:ExcessMap.t Q) (l: @VertexMap.t nat O) x y:
        let '((vs, es),c,s,t) := fn in
        (x ∈v vs) = true ->
        FlowMapPositiveConstraint fn f -> 
        PreFlowCond fn f e ->
        PushCondition fn f e l x y ->
        FlowMapPositiveConstraint fn (fst (push fn f e x y)).
    Proof. Admitted.
        (* unfold FlowMapPositiveConstraint, PreFlowCond, PushCondition.
        unfold CapacityConstraint, NonDeficientFlowConstraint.
        destruct fn as [[[[vs es] c] s] t]. intros. split.
        + unfold push. destruct ((x, y) ∈e es) eqn : E.
        - destruct (Edge.equal (x,y) (u,v)).
        * inv_clear e0. simpl. rewrite EdgeMap.FindUpdateEq.
        eapply (DeltaPositive ((vs, es),c,s,t)) in H2; auto.
        specialize (H0 u v). unfold res_cap in H2. rewrite E in H2. rewrite E.
        destruct H0.
         
        * rewrite EdgeMap.FindUpdateNeq; auto.
        apply H0.
        - destruct (Edge.equal (y,x) (u,v)).
        * inv_clear e. rewrite EdgeMap.FindUpdateEq.
        unfold res_cap. rewrite E. edestruct (Q.min_spec_le); destruct H3.
        ** erewrite H4. unfold R in *. lra.
        ** erewrite H4. unfold R in *. lra.
        * rewrite EdgeMap.FindUpdateNeq; auto.
            apply H0.
            + apply H0.
    Qed.    *)

    Lemma SumInR (f: @EdgeMap.t Q 0 ) vs u v d : 
        Distinct vs ->
        In u vs ->
        QSumList (
            map (fun v0 => EdgeMap.find 0
                  (EdgeMap.update (u, v) (fun x0 => x0 + d) f) 
                  (v0, v)) vs) == 
        QSumList (map (fun v0 => EdgeMap.find 0 f (v0, v)) vs) + d.
    Proof. 
        induction vs; intros.
        + simpl. inversion H0.
        + simpl. destruct (equal u a).
        - subst. rewrite EdgeMap.FindUpdateEq. erewrite SumSame.
        * unfold R in *. lra.
        * intros. intro C. inv_clear C. inv_clear H. tauto. 
        - rewrite EdgeMap.FindUpdateNeq.
        * erewrite IHvs.
        ** lra.
        ** inversion H. auto.
        **  simpl in H0.
            destruct H0; subst; try tauto.
        * intro C. inv_clear C. apply n. reflexivity.
    Qed. 

    Lemma SumInL (f: @EdgeMap.t Q 0) vs: forall u v d,
        Distinct vs ->
        In v vs ->
        QSumList (
            map (fun v0 => EdgeMap.find 0 
                  (EdgeMap.update (u, v) (fun x0 => x0 + d) f) 
                  (u,v0)) vs) == 
        QSumList (map (fun v0 => EdgeMap.find 0 f (u,v0)) vs) + d.
    Proof.
        induction vs; intros.
        + simpl. inversion H0.
        + simpl. destruct (equal v a).
        - subst. rewrite EdgeMap.FindUpdateEq. erewrite SumSame.
        * unfold R in *. lra.
        * intros. intro C. inv_clear C. inv_clear H. tauto.
        - rewrite EdgeMap.FindUpdateNeq.
        * erewrite IHvs.
        ** lra.
        ** inversion H. subst. auto.
        ** simpl in H0. destruct H0; subst; try tauto.
        * intro C. inv_clear C. apply n. reflexivity.
    Qed.

    (* Kui on rahuldatud eelvoo tingimused ning vood ja läbilaskevõimed on mittenegatiivsed 
    ja leidub tipp, kuhu saab push sammu teha, siis järeldub, et ka peale push sammu on eelvoo tingimused säilitatud *)
    Lemma PushPreFlow fn (f: @EdgeMap.t Q 0) (e:ExcessMap.t Q) (l: @VertexMap.t nat O) x y:
        let '((vs, es),c,s,t) := fn in
        (* let (f',e') := push fn f e x y in *)
        (x ∈v vs) = true ->
        (y ∈v vs) = true ->
        PreFlowCond fn f e -> 
        FlowMapPositiveConstraint fn f ->
        PushCondition fn f e l x y->
        PreFlowCond fn (fst (push fn f e x y)) (snd (push fn f e x y)).
    Proof. Admitted.
        (* unfold PreFlowCond, FlowMapPositiveConstraint, PushCondition, PreFlowCond.
        unfold CapacityConstraint, NonDeficientFlowConstraint.
        destruct fn as [[[[vs es] c] s] t].
        (* destruct (push ((vs,es), c, s, t) f e x y) as [f' e']. simpl. *)
        intros Hxvs Hyvs [Hcc Hndf] Hfmp Hpc.
        split.
        + intros. unfold push. destruct ((x, y) ∈e es) eqn : E.
        - destruct (Edge.equal (x,y) (u,v)). 
        * inv_clear e0. simpl. rewrite EdgeMap.FindUpdateEq. unfold res_cap.
        rewrite E. edestruct (Q.min_spec_le); destruct H0.
        ** erewrite H1. unfold R in *. lra.
        ** erewrite H1. unfold R in *. lra.
        * simpl. rewrite EdgeMap.FindUpdateNeq; auto.
        - unfold res_cap. rewrite E. destruct (Edge.equal (y,x) (u,v)).
        * inv_clear e0. simpl. rewrite EdgeMap.FindUpdateEq. edestruct (Q.min_spec_le); destruct H0.
        ** erewrite H1. specialize (Hcc _ _ H). lra.
        ** rewrite H1. specialize (Hfmp u v). unfold R in *. lra.
        * simpl. rewrite EdgeMap.FindUpdateNeq; auto.
        +   intros. 
            pose proof (L1:=VertexSet.to_list_distinct vs).
            apply VertexSet.to_list_in in H as L2.
            apply VertexSet.to_list_in in Hxvs as L3.
            apply VertexSet.to_list_in in Hyvs as L4.
            eapply (DeltaPositive ((vs, es),c,s,t)) in Hpc as HDp. auto.
        [| unfold PreFlowCond, CapacityConstraint, NonDeficientFlowConstraint; tauto].        
        unfold push, res_cap in *. destruct ((x, y) ∈e es) eqn : E.
        -   simpl. destruct (equal v y). 
        * subst. destruct (equal x y).
        ** subst. 
            rewrite SumInR; auto.
            rewrite SumInL; auto. destruct Hpc. unfold excess in H1.
            unfold R in *. lra.
        ** rewrite SumInR; auto. 
        rewrite SumSame.
        **** specialize (Hndf y H H0). unfold excess in Hndf.
         unfold R in *. lra.
         **** intros. intro C. inv_clear C. apply n. reflexivity.
         * unfold excess in Hpc. destruct (equal x v). 
         ** subst. rewrite SumSame. 
         *** erewrite SumInL; auto.
          edestruct (Q.min_spec_le); destruct H1.
         **** erewrite H2 in *. unfold excess. unfold R in *. lra.
         **** erewrite H2 in *. unfold excess in H1. unfold R in *. lra.
         *** intros. intro C. inv_clear C. apply n. reflexivity.
         ** rewrite SumSame, SumSame.
         *** apply Hndf in H; auto.
         *** intros. intro C. inv_clear C. apply n0. reflexivity.
         *** intros. intro C. inv_clear C. apply n. reflexivity.  
         - unfold excess. unfold Qminus. destruct (equal v x).
         * subst. destruct (equal x y).
         ** subst. erewrite SumInL; auto.
         erewrite SumInR; auto.
         unfold excess in Hpc. unfold R in *. lra.
         ** erewrite SumInR; auto.
         erewrite SumSame.
         *** unfold excess in Hpc, HDp.
         edestruct (Q.min_spec_le); destruct H1.
         **** erewrite H2 in *. unfold R in *. lra.
         **** erewrite H2 in *. unfold R in *. lra.
         *** intros. intro C. inv_clear C. apply n. reflexivity.
         * destruct (equal v y).
         ** subst. erewrite SumInL; auto.
         rewrite SumSame.
         *** apply Hndf in H; auto.
         unfold excess in H. unfold excess, Qminus in HDp. unfold R in *. lra.
        *** intros. intro C. inv_clear C. apply n. reflexivity.
        ** erewrite SumSame, SumSame.
        *** apply Hndf in H; auto.
        *** intros. intro C. inv_clear C. apply n0. reflexivity.
        *** intros. intro C. inv_clear C. apply n. reflexivity.
    Qed. *)

    Lemma FPNinVs fn f l u v vs': 
    find_push_node fn f l u vs' = Some v -> (v ∈v vs') = true.
    Proof.
        destruct fn as [[[[vs es] c] s] t]. intros H. 
        unfold find_push_node in H. apply VertexSet.find_first_specSome in H as [_ H].
        auto.
    Qed.

    Lemma HENSCondition fn v :forall (f: @EdgeMap.t Q 0) (e:ExcessMap.t Q),
        has_excess_not_sink fn e v = true -> 0 < ExcessMap.find 0 e v /\ v <> sink fn /\ v <> source fn.
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

    Lemma PushActiveInv (fn:FlowNet) (f:EdgeMap.t R) (e:ExcessMap.t Q) (l: @VertexMap.t nat O) u v x:
        (* let (f',e') := push fn f e u v in *)
        u ∈v nodes fn = true ->
        v ∈v nodes fn = true ->
        x<>v ->
        PreFlowCond fn f e ->
        FlowMapPositiveConstraint fn f ->
        PushCondition fn f e l u v ->
        ActiveNode fn (fst (push fn f e u v)) (snd (push fn f e u v)) x ->
        ActiveNode fn f e x.
    Proof. Admitted.
        (* unfold ActiveNode, push, PreFlowCond, 
        FlowConservationConstraint, PushCondition.
        destruct fn as [[[[vs es] c] s] t].
        pose proof (H:= True).
        intros H0 H1 H2 H3 H4 H5 H6.
        cbn in H0, H1.
        pose proof (L1:=VertexSet.to_list_distinct vs).
        apply VertexSet.to_list_in in H0 as L2.
        apply VertexSet.to_list_in in H1 as L3.
        unfold CapacityConstraint, NonDeficientFlowConstraint, FlowMapPositiveConstraint in *.
        destruct ((u, v) ∈e es) eqn:E0.
        + destruct H6. simpl in H7. split; auto. 
        unfold excess_update.
        destruct (equal x u) in H7.
        - 
        * unfold R in *. lra.
        * intros. intro C. inv_clear C. apply H2. reflexivity.
        - erewrite SumSame, SumSame in H7.
        * unfold R in *. lra.
        * intros. intro C. inv_clear C. apply n. reflexivity.
        * intros. intro C. inv_clear C. apply H2. reflexivity.
        + destruct H6. split; auto. 
        unfold excess in *. unfold Qminus in *. set (d:= Qmin _ _) in *.
        destruct (equal x u) in H7.
        - subst. erewrite SumInR, SumSame in H7; auto.
        * unfold R in *. lra.
        * intros. intro C. inv_clear C. apply H2. reflexivity.
        - erewrite SumSame, SumSame in H7; auto.
        * intros. intro C. inv_clear C. apply H2. reflexivity.
        * intros. intro C. inv_clear C. apply n. reflexivity.
    Qed. *)
    
    Lemma FPNConditionNone fn f l u vs': 
        find_push_node fn f l u vs' = None -> 
        forall v, v ∈v vs' = true -> (0 <? res_cap fn f u v = false) 
        \/ (VertexMap.find 0 l u <> VertexMap.find 0 l v + 1)%nat.
    Proof.
        destruct fn as [[[[vs es] c] s] t].
        intros H v Hvs. 
        unfold find_push_node in H.
        eapply VertexSet.find_first_specNone in H; eauto.
        apply andb_false_iff in H. destruct H; try tauto.
        destruct (Nat.eqb_spec (VertexMap.find 0%nat l u) (1 + VertexMap.find 0%nat l v)); lia.
    Qed. 

    Lemma HENSConditionFalse fn v :forall (f: @EdgeMap.t Q 0) (e:ExcessMap.t Q),
        has_excess_not_sink fn e v = false -> 0 >= ExcessMap.find 0 e v \/ v = sink fn \/ v = source fn.
    Proof.
        unfold has_excess_not_sink.
        intros. destruct fn as [[[[vs es] c] s] t].
        destruct (equal v t), (equal v s); subst; auto.
        destruct_guard_in H.
        + inversion E0.
        + destruct_guard_in H.
        - inversion H. 
        - simpl. apply QLt_false in E1. tauto.
    Qed.

    Lemma PushNoSteepArc fn f e l x y:
        (* let (f',e') := push fn f e x y in *)
        (x ∈v nodes fn) = true -> 
        FlowMapPositiveConstraint fn f ->
        PreFlowCond fn f e -> 
        PushCondition fn f e l x y ->
        NoSteepArc fn f l -> NoSteepArc fn (fst (push fn f e x y)) l.
    Proof. 
        unfold FlowMapPositiveConstraint, PreFlowCond, PushCondition,
        NoSteepArc. unfold CapacityConstraint, NonDeficientFlowConstraint.
        destruct fn as [[[[vs es] c] s] t].
        intros. unfold push in H4. set (d:= Qmin _ _) in H4. 
        destruct ((x, y) ∈e es) eqn : E.
        + unfold res_cap in H4. simpl in H4. destruct ((u, v) ∈e es) eqn : E2.
        - destruct (Edge.equal (u, v) (x, y)).
        * inv_clear e0. lia.
        * apply H3. unfold res_cap. rewrite E2. rewrite EdgeMap.FindUpdateNeq in H4; auto.
        - destruct (Edge.equal (v, u) (x, y)).
        * inv_clear e0. lia.
        * rewrite EdgeMap.FindUpdateNeq in H4; auto. 
        apply H3. unfold res_cap. rewrite E2. auto.
        + unfold res_cap in H4. simpl in H4. destruct ((u, v) ∈e es) eqn : E2.
        - destruct (Edge.equal (u, v) (y, x)).
        * inv_clear e0. lia.
        * rewrite EdgeMap.FindUpdateNeq in H4; auto.
        apply H3. unfold res_cap. rewrite E2. auto.
        - destruct (Edge.equal (v, u) (y, x)).
        * inv_clear e0. lia.
        * rewrite EdgeMap.FindUpdateNeq in H4; auto.
        apply H3. unfold res_cap. rewrite E2. auto.
    Qed.

    Lemma PushResCapNodes fn f e x y:
        (* let (f',e') := push fn f e x y in     *)
        x ∈v (nodes fn) = true -> y ∈v (nodes fn) = true ->
        ResCapNodes fn f -> ResCapNodes fn (fst (push fn f e x y)).
    Proof.
        unfold ResCapNodes.
        intros. unfold push in H2. destruct fn as [[[[vs es] c] s] t].
        set (d:= Qmin _ _) in H2. destruct ((x, y) ∈e es) eqn : E. simpl in H2.
        + unfold res_cap in H2. destruct ((u, v) ∈e es) eqn : E2.
        - destruct (Edge.equal (u, v) (x, y)).
        * inv_clear e0. tauto.
        * rewrite EdgeMap.FindUpdateNeq in H2; auto.
        apply H1. unfold res_cap. rewrite E2. auto.
        -  destruct (Edge.equal (v, u) (x, y)).
        * inv_clear e0. tauto.
        * rewrite EdgeMap.FindUpdateNeq in H2; auto.
        apply H1. unfold res_cap. rewrite E2. auto.
        + unfold res_cap in H2. simpl in H2. destruct ((u, v) ∈e es) eqn : E2.
        - destruct (Edge.equal (u, v) (y, x)).
        * inv_clear e0. tauto.
        * rewrite EdgeMap.FindUpdateNeq in H2; auto.
        apply H1. unfold res_cap. rewrite E2. auto.
        - destruct (Edge.equal (v, u) (y, x)).
        * inv_clear e0. tauto.
        * rewrite EdgeMap.FindUpdateNeq in H2; auto.
        apply H1. unfold res_cap. rewrite E2. auto.
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
        + subst. rewrite VertexMap.FindReplaceEq. lia.
        + subst. rewrite VertexMap.FindReplaceEq. rewrite VertexMap.FindReplaceNeq; auto.
        destruct E0. apply H0 in H4 as P. destruct P as [P1 P2].
        eapply (reflect_iff _ _ (QLt_spec _ _)) in H4.
        apply H5 in H4; auto. lia.
        + subst. rewrite VertexMap.FindReplaceEq. rewrite VertexMap.FindReplaceNeq; auto.
        destruct E0 as [E1 E2]. eapply (reflect_iff _ _ (QLt_spec _ _)) in E1. 
        apply H0 in E1 as P. destruct P as [P1 P2]. 
        apply H2 in H4. apply H2 in E1. lia.
        + rewrite VertexMap.FindReplaceNeq; auto. rewrite VertexMap.FindReplaceNeq; auto.
    Qed.


    Lemma RelabelValidCondition fn f e l u : 
        ActiveNode fn f e u ->
        NoSteepArc fn f l ->
        find_push_node fn f l u (nodes fn) = None -> 
        forall v,
        relabel_find fn f l u (nodes fn) = Some v -> 
        RelabelCondition fn f e l u.
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

    (* Siis kui gpr_helper_trace tagastab voo f' ja kõrgused l', siis järeldub, et ainukesed aktiivsed tipud on sisend või väljund,
     täidetud on voo säilivus nõue ja sisendi ning väljundi kõrgused on samad, mis alguses ehk invariante ei rikuta.  *)
    Lemma FlowConservationGpr fn g:forall (f: @EdgeMap.t Q 0) (e:ExcessMap.t Q) (l: @VertexMap.t nat O) ac tr,
        let '((vs, es),c,s,t) := fn in
        (* Iga tipp u ja v korral, kui nende vahel on serv, siis need tipud kuuluvad tippude hulka*)
        (forall u v, ((u, v) ∈e es = true) -> (u ∈v vs) = true /\ (v ∈v vs) = true) ->
        (* Leidub tippusid, mille vahel on läbilaskevõime *)
        ResCapNodes fn f ->
        (* Täidetud on invariant h(u) <= h(v) + 1 *)
        NoSteepArc fn f l ->
        (* Iga tipp n korral, kui n kuulub aktiiVertexSete tippude hulka, siis n kuulub ka tippude hulka*)
        (forall n, n ∈v ac = true -> n ∈v vs = true) ->
        (* Graafis on säilitatud korrektsed kõrgused *)
        ValidLabeling fn f l ->
        (* Iga tipp n korral, kui n kuulub aktiiVertexSete tippude hulka, siis see on ekvivalentne sellega, et tipus n on ülejääk ja 
        tipp n pole sisend ega väljund*)
        (forall n, n ∈v ac = true <-> (ActiveNode fn f e n /\ n<>t /\ n<>s)) ->
        (* Täidetud on eelvoo tingimused *)
        PreFlowCond fn f e ->
        (* Vood ja läbilaskevõimed on mittenegatiivsed *)
        FlowMapPositiveConstraint fn f ->
        (* gpr_helper_trace tagastab voo f' ja kõrgsued l', siis sellest järeldub, et*)
        forall f' l' tr', 
        gpr_helper_trace fn f e l ac g tr = (Some (f', l'),tr') ->
        (* Iga tipu n korral, mis on aktiivne on n väljund või sisend*)
        (forall n, ActiveNode fn f' e n -> n=t \/ n=s) /\
        (* Täidetud on voo säilivuse nõue*)
        FlowConservationConstraint fn f' e /\
        (* Sisendi ja väljundi kõrgus on funktsiooni gpr_helper_trace lõpus sama, mis oli alguses *)
        (VertexMap.find 0 l s)%nat = (VertexMap.find 0 l' s)%nat /\ (VertexMap.find 0 l t)%nat = (VertexMap.find 0 l' s)%nat.
    Proof. Admitted.     
        (* destruct fn as [[[[vs es] c] s] t]. induction g;
        intros f l ac tr Heisn Hrcn Hnsa Hnvs Hvl Han Hprc Hfmpc f' l' tr' H.
        + simpl in H. inversion H.
        + rewrite gpr_helper_trace_fn in H. destruct_guard_in H.
        - destruct p. destruct_guard_in H.
        * cbn zeta in H. destruct_guard_in H.
        ** apply VertexSet.choiceSome in E0. destruct E0. 
         eapply IHg in H; eauto.
        (* *** clear H IHg. destruct_guard.
        **** apply VertexSet.AddIsSet. auto.
        **** apply VertexSet.AddIsSet; auto. *)
        *** clear H IHg. apply PushResCapNodes; auto.
        **** apply FPNinVs in E1. auto.
        *** clear H IHg. apply PushNoSteepArc; auto.
        eapply FPNCondition; eauto.
        apply Han in H0. tauto.
        *** clear H IHg. intros. destruct_guard_in H. simpl VertexSet.mem in H.
        **** destruct (equal n v0).
        ***** subst. eapply FPNinVs; eauto.
        (* ***** rewrite VertexSet.MemRemoveNeq in H; auto.
        **** destruct (equal n v0).
        ***** subst. eapply FPNinVs; eauto. *)
        ***** rewrite VertexSet.MemAddNeq in H; auto.
        **** destruct (equal n v0).
        ***** subst. eapply FPNinVs; eauto.
        ***** rewrite VertexSet.MemAddNeq in H; auto. subst. destruct (equal n v).
        ****** subst. rewrite VertexSet.MemRemoveEq in H. inversion H.
        ****** rewrite VertexSet.MemRemoveNeq in H; auto.
        *** clear H IHg. eapply (PushValidLabel (vs, es, c ,s, t)); auto.
        eapply FPNCondition; eauto. apply Han in H0. tauto.
        *** intros. split; intros.
        **** destruct (equal n v0).
        ***** subst. clear H IHg. apply HENSCondition in E2. split; try tauto.
        split.
        ****** eapply FPNinVs in E1. auto.
        ****** tauto.
        ***** clear H IHg. rewrite VertexSet.MemAddNeq in H2; eauto.
        destruct_guard_in H2.
        ****** eapply Han in H2. destruct H2. split; eauto.
        destruct (equal n v). subst.
        *******  eapply (reflect_iff _ _ (QLt_spec _ _)) in E0. split; eauto.
        ******* eapply PushActiveCondition; eauto.
        ****** subst. destruct (equal n v).
        ******* subst. rewrite VertexSet.MemRemoveEq in H2. inversion H2.
        ******* rewrite VertexSet.MemRemoveNeq in H2; eauto. 
        eapply Han in H2. destruct H2. split; eauto. 
         eapply PushActiveCondition; eauto.
        **** clear H IHg. destruct (equal n v0).
        ***** subst. apply VertexSet.MemAddEq. 
        ***** rewrite VertexSet.MemAddNeq; auto.
        destruct_guard.
        ****** eapply Han. destruct H2. split; auto. destruct (equal n v).
        ******* subst. eapply Han in H0. tauto.
        ******* eapply PushActiveInv in H; auto. 
        ******** eapply FPNinVs in E1. auto.
        ******** eapply FPNCondition in E1; eauto.
        apply Han in H0; tauto.
        ****** subst. rewrite VertexSet.MemRemoveNeq.
        ******* eapply FPNinVs in E1 as P. eapply FPNCondition in E1; eauto;
        [| eapply Han in H0; tauto]. destruct H2. eapply PushActiveInv in H; eauto.
        eapply Han. split; auto.
        ******* intro C. subst. destruct H2. destruct H. apply QLt_false in E0. lra.
        *** clear H IHg. eapply (PushPreFlow (vs, es, c, s, t)); auto. 
        **** eapply FPNinVs in E1. auto.
        **** eapply FPNCondition; eauto. eapply Han in H0; tauto.
        *** clear H IHg. eapply (PushFlowMapPos (vs, es, c, s, t)); eauto.
        eapply FPNCondition; eauto. eapply Han in H0. tauto.
        ** eapply VertexSet.choiceSome in E0 as P; auto. destruct P.
        eapply FPNinVs in E1 as P. apply Han in H0 as W. destruct W. 
        eapply FPNCondition in E1 as P2; auto.
        eapply HENSConditionFalse in E2 as Q.
        eapply IHg in H; eauto.
        *** eapply PushResCapNodes; auto.
        *** eapply PushNoSteepArc; auto.
        *** intros. destruct (equal n v0).
        **** subst. auto.
        **** rewrite VertexSet.MemRemoveNeq in H4; auto. eapply Hnvs.
         destruct_guard_in H4; auto. subst.
         rewrite VertexSet.MemRemoveNeq in H4; auto.
         intro C. subst. rewrite VertexSet.MemRemoveEq in H4. inversion H4.
        *** eapply (PushValidLabel (vs, es, c, s, t)); eauto.
        *** intros. destruct (equal n v0).
        **** subst. rewrite VertexSet.MemRemoveEq. split; intros; [inversion H1 |].
        destruct Q.
        ***** destruct H1. destruct H1. lra.
        ***** simpl in H4. tauto.
        **** rewrite VertexSet.MemRemoveNeq; auto. destruct_guard; split; intros.
        ***** eapply Han in H4. destruct H4. split; auto. destruct (equal n v).
        ****** subst. split; auto.  eapply (reflect_iff _ _ (QLt_spec _ _)) in E3.
        auto.
        ****** eapply PushActiveCondition; eauto.
        ***** eapply Han. destruct H4. split; auto.
        eapply PushActiveInv in P2; eauto.
        ***** subst. destruct (equal n v).
        ****** subst. rewrite VertexSet.MemRemoveEq in H4. inversion H4.
        ****** rewrite VertexSet.MemRemoveNeq in H4; auto. 
        eapply Han in H4. destruct H4. split; auto. 
        eapply PushActiveCondition; eauto.
        ***** subst. destruct (equal n v).
        ****** subst. eapply QLt_false in E3. destruct H4, H1. lra.
        ****** rewrite VertexSet.MemRemoveNeq; auto. eapply Han. destruct H4. split; auto.
        eapply PushActiveInv in P2; eauto.
        *** eapply (PushPreFlow (vs, es, c, s, t)); eauto.
        *** eapply (PushFlowMapPos (vs, es, c, s, t)); eauto.
        * destruct_guard_in H.
        ** eapply VertexSet.choiceSome in E0; auto. destruct E0, H1.
         eapply IHg in H; eauto.
        *** split; try tauto. split; try tauto.
            destruct H, H1, H2. rewrite <- H2, <- H3. subst.
            unfold relabel in E2. destruct_guard_in E2; [|inversion E2]. inv_clear E2.
            destruct (equal s v).
        **** subst. exfalso. apply Han in H0. destruct H0, H4. auto.
        **** rewrite VertexMap.FindReplaceNeq; auto. split; auto.
            destruct (equal t v). 
        ***** subst. exfalso. apply Han in H0. destruct H0. destruct H4; auto.
        ***** rewrite VertexMap.FindReplaceNeq; auto.
        *** eapply RelabelNoSteepArc; eauto.
        *** eapply (RelabelValidLabel (vs, es, c, s, t)); eauto. 
        unfold relabel in E2. destruct_guard_in E2; [| inversion E2].
        eapply RelabelValidCondition; eauto.
        **** apply Han. auto.
        ** inversion H. 
        - apply VertexSet.choiceNone in E0. subst. inv_clear H. split.
        * intros. destruct (equal n t); auto. 
        destruct (equal n s); subst; try tauto.
        assert (n ∈v VertexSet.empty = true).
        ** eapply Han. tauto.
        ** rewrite VertexSet.MemEmpty in H0. inversion H0.
        * split; try tauto.
         unfold FlowConservationConstraint. intros. unfold PreFlowCond in Hprc.
        destruct Hprc. unfold NonDeficientFlowConstraint in H3.
        apply H3 in H as P; auto. clear IHg. 
        destruct (Qeq_bool (excess (vs, es, c, s, t) f' v) 0) eqn : E.
        ** eapply Qeq_bool_iff in E. auto.
        ** eapply Qeq_bool_neq in E. assert (v ∈v VertexSet.empty = true).
        *** eapply Han. split; auto. split; auto. lra.
        *** rewrite VertexSet.MemEmpty in H4. inversion H4.
    Qed. *)

    Lemma SumSameReplace (f: @EdgeMap.t Q 0) (s:V->V*V) vs u v d : 
        (forall v0, In v0 vs -> s v0 <> (u, v)) ->
        map (fun v0 => EdgeMap.find 0 
            (EdgeMap.replace (u, v) d f) 
            (s v0)) vs = 
        map (fun v0 => EdgeMap.find 0 f (s v0)) vs.
    Proof.
        induction vs; intros.
        + simpl. auto.
        + simpl. rewrite IHvs; auto.
        f_equal. clear IHvs.
        - erewrite EdgeMap.FindReplaceNeq; auto.
        apply H. cbn. auto.
        - intros. apply H. cbn. auto.
    Qed.

    (* Kui (s,y) voog ei ole suurem d-st, siis tipu n ülejääk ei ole suurem kui sinna suunata (s,y) voog *)
    Lemma NDFinitial s d y n f e: 
        EdgeMap.find 0 f (s,y) <= d ->
        n<>s ->
        ExcessMap.find 0 e n <= 
            let flow := EdgeMap.find 0 f (s, y) in
            let e' := ExcessMap.replace n flow e in
            ExcessMap.find 0 e' n .
    Proof. Admitted.
        (* intros Hd Hnns. simpl. destruct (equal n y).
        + inv_clear e0. rewrite ExcessMap.FindReplaceEq.
        set (xs := VertexSet.to_list vs).
        induction xs; intros.
        + simpl. lra. 
        + unfold excess in *. simpl. destruct (equal n y).
        - subst. destruct (equal a s).
        * subst. erewrite EdgeMap.FindReplaceEq. erewrite EdgeMap.FindReplaceNeq.
        ** unfold R in *. lra.
        ** intro C. inv_clear C. auto.
        * erewrite EdgeMap.FindReplaceNeq, EdgeMap.FindReplaceNeq.
        ** unfold R in *. lra.
        ** intro C. inv_clear C. auto.
        ** intro C. inv_clear C. auto.
        - erewrite EdgeMap.FindReplaceNeq, EdgeMap.FindReplaceNeq.
        * lra.
        *  intro C. inv_clear C. auto.
        * intro C. inv_clear C. auto.
    Qed. *)

    Lemma SourceDeficient c s y f e: 
        (forall a, EdgeMap.find 0 f (a,s) <= EdgeMap.find 0 f (s,a)) ->
        EdgeMap.find 0 f (s,y) <= c s y ->
        (* let f' := EdgeMap.replace (s, y) (c s y) f in *)
        (* let e' := ExcessMap.replace y (c s y) e in *)
        let e' := excess_update e s (c s y) y in (* suuname maksimaalse võimaliku voo s-st y-sse *)
        ExcessMap.find 0 e' s <= 0.
    Proof. Admitted.
        (* intros Has Hcap. unfold excess.
        set (xs := VertexSet.to_list vs).
        induction xs; intros.
        + simpl. lra.
        + unfold excess in *. simpl. destruct (Edge.equal (s,y) (a,s)).
        - inv_clear e. erewrite EdgeMap.FindReplaceEq. lra.
        - destruct (equal y a).
        * subst. erewrite EdgeMap.FindReplaceEq. erewrite EdgeMap.FindReplaceNeq.
        ** specialize (Has a). lra.
        ** auto.
        * erewrite EdgeMap.FindReplaceNeq, EdgeMap.FindReplaceNeq.
        ** specialize (Has a). lra.
        ** intro C. inv_clear C. auto.
        ** auto.
    Qed. *)

    Lemma ExcessSame c s y f e n: 
        (forall a, EdgeMap.find 0 f (a,s) <= EdgeMap.find 0 f (s,a)) ->
        EdgeMap.find 0 f (s,y) <= c s y ->
        n<>s ->
        n<>y ->
        ExcessMap.find 0 e n ==
        ExcessMap.find 0 (excess_update e s (c s y) y) n.
    Proof.
        intros Has Hcap Hnns Hnny. unfold excess_update.
        erewrite ExcessMap.FindReplaceNeq.
        + erewrite ExcessMap.FindReplaceNeq. reflexivity. apply Hnns.
        + apply Hnny.
    Qed.

    Lemma SumNoR: forall f vs v t c n, n <> t ->
        QSumList (map (fun v0 : V => EdgeMap.find 0 (EdgeMap.replace (v, t) c f) (v0, n)) vs) =
         QSumList (map (fun v0 : V => EdgeMap.find 0 f (v0, n)) vs).
    Proof.
        intros f vs. induction vs; intros; cbn; auto.
        assert ((a, n) <> (v, t)). { 
            intro q. inv_clear q. tauto. 
        }
        rewrite EdgeMap.FindReplaceNeq; auto.
        eapply (IHvs v t c) in H. rewrite H. 
        reflexivity.
    Qed.
        
    Lemma SumNoL: forall f vs v t c s, s <> v ->
        QSumList (map (fun v0 : V => EdgeMap.find 0 (EdgeMap.replace (v, t) c f) (s,v0)) vs) =
         QSumList (map (fun v0 : V => EdgeMap.find 0 f (s,v0)) vs).
    Proof.
        intros f vs. induction vs; intros; cbn; auto.
        assert ((s, a) <> (v, t)). { 
            intro q. inv_clear q. tauto. 
        }
        rewrite EdgeMap.FindReplaceNeq; auto.
        eapply (IHvs v t c) in H. rewrite H. 
        reflexivity.
    Qed.

    Lemma InitialUpdateBigger: forall f s v0 n c, 
        (forall u v, EdgeMap.find 0 f (u, v) <= c u v) -> forall xs,
        QSumList (map (fun v1 : V => EdgeMap.find 0 (EdgeMap.replace (s, v0) (c s v0) f) (v1, n)) xs) >=
         QSumList (map (fun v1 : V => EdgeMap.find 0 f (v1, n)) xs).
    Proof.
        intros f s v0 n c P xs.
        induction xs; cbn; intros; try lra.
        destruct (Edge.equal (a,n) (s,v0)).
        +   inv_clear e.
            rewrite EdgeMap.FindReplaceEq.
            specialize (P s v0). lra.
        +   rewrite EdgeMap.FindReplaceNeq; auto. lra.
    Qed.

    (* Peale initsialiseerimist on aktiivsete tippude hulgas tipud, mis ei ole sisend ega väljund ja on täidetud eelvoo nõuded
     ja vood ning läbilaskevõimed on mittenegatiivsed*)
    Lemma InitialGpr fn :
        let '((vs, es),c,s,t) := fn in
        (* Iga tipp u ja v korral, kui nende vahel on serv, siis need tipud kuuluvad tippude hulka*)
        (forall u v, ((u, v) ∈e es = true) -> (u ∈v vs) = true /\ (v ∈v vs) = true) ->
        (forall u v, c u v >= 0) ->
        forall f' e' ac' ,
        (* Kui algoritmi initsialiseerimise samm, kus tehakse push samm sisendist väljuvate servade peal
        tagastab voo f' ja aktiivsed tipud ac', siis sellest järeldub all olev konjuktsioon*)
        initial_push fn e' = (f',e',ac') ->
        ResCapNodes fn f' /\
        (forall u v, EdgeMap.find 0 f' (u, v) <= c u v) /\
        (forall n, n ∈v ac' = true -> n ∈v vs = true) /\
        (forall n, n ∈v ac' = true <-> (ActiveNode fn f' e' n /\ n<>t /\ n<>s)) /\
        PreFlowCond fn f' e' /\
        FlowMapPositiveConstraint fn f'.
    Proof. Admitted.
        (* destruct fn as [[[[vs es] c] s] t].
        intros Hvs Hc.
        unfold initial_push.
        set (es' := EdgeSet.filter _ _).
        rewrite <- fold_left_rev_right.
        set (xs := rev _).
        assert (K:forall x, In x xs -> EdgeSet.mem x es = true). {
            intros. apply in_rev in H.
            apply EdgeSet.to_list_in in H.
            apply EdgeSet.in_filter in H. tauto.
        }
        assert (G: forall x, In x xs -> fst x = s). {
            intros. apply in_rev in H.
            apply EdgeSet.to_list_in in H.
            apply EdgeSet.in_filter in H.
            destruct x. destruct (equal s v); subst;cbn; auto.
            destruct H. inversion H0.
        }
        set (F := (fun y => _)).
        induction xs; intros f' ac' H.
        +   cbn in H. inv_clear H.
             repeat split; auto.
        ++  cbn in H. destruct_guard_in H.
        +++ apply Hvs in E0. tauto.
        +++ rewrite EdgeMap.FindEmpty in H. lra.
        ++  cbn in H. destruct_guard_in H.
        +++ apply Hvs in E0. tauto.
        +++ rewrite EdgeMap.FindEmpty in H. lra.
        ++  intros. rewrite EdgeMap.FindEmpty. apply Hc.
        ++  intros. rewrite VertexSet.MemEmpty in H. inversion H.
        ++  rewrite VertexSet.MemEmpty in H. inversion H.
        ++  rewrite VertexSet.MemEmpty in H. inversion H.
        ++  rewrite VertexSet.MemEmpty in H. inversion H.
        ++  rewrite VertexSet.MemEmpty in H. inversion H.
        ++  intros [[H0 H1] [H2 H3]]. cbn in H1.
            set (ys:=VertexSet.to_list vs) in H1. exfalso. clear -H1.
            induction ys.
        +++ cbn in H1. lra.
        +++ cbn in *. repeat rewrite EdgeMap.FindEmpty in H1. lra.
        ++  cbn. intros. rewrite EdgeMap.FindEmpty. apply Hc.
        ++  cbn. intros. set (ys:=VertexSet.to_list vs). clear -ys .
            induction ys.
        +++ cbn. lra.
        +++ cbn. repeat rewrite EdgeMap.FindEmpty. lra.
        ++  rewrite EdgeMap.FindEmpty. lra.
        +   simpl fold_right in H. destruct a.
            destruct (fold_right F (EdgeMap.empty, VertexSet.empty) xs) eqn:E.
            assert (K' : forall x : V * V, In x xs -> x ∈e es = true). {
                clear -K. intros. apply K. cbn. tauto.
            }
            assert (G' : forall x, In x xs -> fst x = s). {
                clear -G. intros. apply G. cbn. tauto.
            }
            specialize (IHxs K' G' _ _ eq_refl).
            unfold F in H. unfold has_excess_not_sink in H.
            apply pair_equal_spec in H. destruct H. subst.
            destruct IHxs as [H1 [H2 [H3 [H4 H5]]]].
            assert (J: v ∈v vs = true /\ v0 ∈v vs = true). {
                apply Hvs, K. constructor; auto.
            }
            specialize  (G (v,v0)). cbn in G. rewrite G in *; auto. clear G.
            repeat split; auto.
        ++  unfold res_cap in H. 
            specialize (H1 u v1).
            unfold res_cap in H1.
            destruct ((u, v1) ∈e es) eqn:E1.
        +++ apply Hvs in E1. tauto.
        +++ destruct (Edge.equal (s,v0) (v1,u)).
            *   inv_clear e. cbn. tauto.
            *   rewrite EdgeMap.FindReplaceNeq in H; auto.
                apply H1 in H. cbn. tauto.
        ++  unfold res_cap in H. 
            specialize (H1 u v1).
            unfold res_cap in H1.
            destruct ((u, v1) ∈e es) eqn:E1.
        +++ apply Hvs in E1. tauto.
        +++ destruct (Edge.equal (s,v0) (v1,u)).
            *   inv_clear e. cbn. tauto.
            *   rewrite EdgeMap.FindReplaceNeq in H; auto.
                apply H1 in H. cbn. tauto.
        ++  intros. 
            destruct (Edge.equal (s,v0) (u,v1)).
        +++ inv_clear e. rewrite EdgeMap.FindReplaceEq. lra.
        +++ rewrite EdgeMap.FindReplaceNeq; auto.
        ++  intros. 
            destruct (equal v0 t); cbn in H; subst; auto.
            destruct (equal v0 s); cbn in H; subst; auto.
            destruct_guard_in H; auto.
            destruct (equal n v0); cbn in H; subst; try  tauto.
            erewrite VertexSet.MemAddNeq in H; auto.
        ++  intros. 
            destruct (equal v0 t); cbn in H; subst; auto.
            destruct (equal v0 s); cbn in H; subst; auto.
            destruct_guard_in H; auto.
            destruct (equal n v0); cbn in H; subst; try  tauto.
            erewrite VertexSet.MemAddNeq in H; auto.
        ++  cbn.
            destruct (equal v0 t); cbn in H; subst.
        +++ apply H4 in H. destruct H.
            unfold ActiveNode in H.
            rewrite SumNoR; [|tauto].
            destruct H. unfold excess in H6.
            rewrite SumNoL; [|tauto]. auto.
        +++ destruct (equal v0 s); cbn in H; subst; auto.
            *   apply H4 in H. destruct H.
                unfold ActiveNode in H. cbn in H.
                subst.
                rewrite SumNoR; [|tauto].
                rewrite SumNoL; [|tauto].
                lra.
            *   destruct_guard_in H; destruct_guard_in E0;
                try (inversion E0; fail).
            **  set (d:= _ - _) in E1.
                destruct (QLt_spec 0 d); try lra.
                destruct (equal n v0); cbn in H; subst; auto.
                rewrite SumNoR; [|tauto]. 
                rewrite VertexSet.MemAddNeq in H; auto.
                apply H4 in H. destruct H. cbn in H. destruct H.
                rewrite SumNoL; [|tauto].
                auto.
            **  apply H4 in H. destruct H. cbn in H. destruct H.
                rewrite SumNoL; [|tauto].
                rewrite SumNoL in E1; [|tauto].
                eapply InitialUpdateBigger  with (n:=n) (xs:=VertexSet.to_list vs) (v0:=v0) (s:=s)in H2. 
                set (d:= _ - _) in E1.
                destruct (QLt_spec 0 d); try lra.
                clear -H2 H6.
                set (q1:= QSumList _) in H2, H6.
                set (q2:= QSumList _) in H2 |- *.
                set (q3:= QSumList _) in H6 |- *.
                lra.
        ++  destruct (equal v0 t); subst; cbn in H.
        +++ apply H4 in H. tauto.
        +++ destruct (equal v0 s); subst; cbn in H.
            *   apply H4 in H. tauto.
            *   set (d := _ - _) in H.
                destruct (0 <? d) eqn:E3.
            **  destruct (equal n v0); cbn in H; subst; try  tauto.
                rewrite VertexSet.MemAddNeq in H; auto.
                apply H4 in H; tauto.
            **  apply H4 in H. tauto.
        ++  destruct (equal v0 t); subst; cbn in H.
        +++ apply H4 in H. tauto.
        +++ destruct (equal v0 s); subst; cbn in H.
            *   apply H4 in H. tauto.
            *   set (d := _ - _) in H.
                destruct (0 <? d) eqn:E3.
            **  destruct (equal n v0); cbn in H; subst; try  tauto.
                rewrite VertexSet.MemAddNeq in H; auto.
                apply H4 in H; tauto.
            **  apply H4 in H. tauto.
        ++  intros.
            destruct (equal v0 t); subst.
        +++ apply H4. destruct H. split; try tauto.
            unfold ActiveNode in H |- *.
            destruct H. split; auto.
            unfold excess in H6 |- *.
            rewrite SumNoR in H6; [|tauto].
            rewrite SumNoL in H6; [|tauto].
            lra.
        +++ destruct (equal v0 s); subst.
            *   apply H4. destruct H. split; try tauto.
                unfold ActiveNode in H |- *.
                destruct H. split; auto.
                unfold excess in H6 |- *.
                rewrite SumNoR in H6; [|tauto].
                rewrite SumNoL in H6; [|tauto].
                lra.
            *   set (d := excess _ _ _). 
                destruct (0 <? d) eqn:E3.
            **  destruct (equal n v0); subst.
            *** apply VertexSet.MemAddEq.
            *** cbn.
                rewrite VertexSet.MemAddNeq; auto.
                apply H4. split; try tauto.
                unfold ActiveNode in H |- *.
                destruct H. split; try tauto.
                unfold excess in H |- *.
                rewrite SumNoR in H; [|tauto].
                rewrite SumNoL in H; [|tauto].
                lra.
            **  apply H4. split; try tauto.
                unfold ActiveNode in H |- *.
                destruct H. split; try tauto.
                destruct H. 
                destruct (QLt_spec 0 d); try lra.
                destruct (equal n v0); subst.
            *** clear -H6 n2. fold d in H6. lra.
            *** cbn in *. clear d.
                rewrite SumNoR in H6; [|tauto].
                rewrite SumNoL in H6; [|tauto].
                auto.
            ++  unfold CapacityConstraint. intros.
                destruct (Edge.equal (s,v0) (u, v1)).
                *   inv_clear e.
                    rewrite EdgeMap.FindReplaceEq. lra.
                *   rewrite EdgeMap.FindReplaceNeq; auto.
            ++  unfold NonDeficientFlowConstraint. intros.
                destruct H5, H5.
                unfold NonDeficientFlowConstraint in H7.
                specialize (H7 _ H H0). clear -H7 H0 H2 Hc.
                unfold excess in *.
                destruct (equal v0 v1); subst.
            +++ rewrite SumNoL; auto.
                eapply InitialUpdateBigger  with (n:=v1) (xs:=VertexSet.to_list vs) (v0:=v1) (s:=s)in H2.
                set (q1:= QSumList _) in H2, H7.
                set (q2:= QSumList _) in H2 |- *.
                set (q3:= QSumList _) in H2, H7 |- *.
                lra. 
            +++ rewrite SumNoL; auto.
                rewrite SumNoR; auto.
            ++  destruct (Edge.equal (s,v0) (u,v1)).
            +++ inv_clear e. rewrite EdgeMap.FindReplaceEq. apply Hc.
            +++ rewrite EdgeMap.FindReplaceNeq; auto. 
                destruct H5, H. unfold FlowMapPositiveConstraint in H0.
                destruct (H0 u v1). auto.
    Qed. *)


    (* Kui Iga serva e korral e kuulub hulka e' või e'', siis ta kuulub hulka es ja iga tipu v korral, kui puudub serv
    (s, v), siis sellel serva läbilaskevõime on 0 ning 
    iga tipu v korral, kui serv (s, v) kuulub hulka e', siis sellel serva läbilaskevõime on 0, sellest järeldub, et
    peale initsialiseerimist on kõik sisendist väljuvate servade läbilaskevõime ära kasutatud *)
    Lemma InitialPushResCap0 vs es c s t v : 
        v<>s -> forall  f' e' ac',
        initial_push (vs,es,c,s,t) e' = (f',e',ac') ->
        res_cap (vs,es,c,s,t) f' s v == 0.
    Proof. Admitted.
        (* unfold initial_push.
        set (es' := EdgeSet.filter _ _).
        rewrite <- fold_left_rev_right.
        set (xs := rev _). intros L.
        destruct ((s, v) ∈e es) eqn:E.
        +   assert (K: In (s,v) xs). {
                unfold xs. rewrite <- in_rev.
                apply EdgeSet.to_list_in. unfold es'.
                apply EdgeSet.filter_in; auto. 
                apply eqb_refl.
            }
            generalize dependent K.
            set (F := (fun y => _)).
            induction xs; intros K f' ac' H.
        ++  inversion K.
        ++  cbn in K, H. 
            destruct (fold_right F (EdgeMap.empty, VertexSet.empty) xs) eqn:E1.
            cbn in K. destruct a. destruct K.
        +++ inv_clear H0. inv_clear H. cbn. rewrite E.
            rewrite EdgeMap.FindReplaceEq. lra.
        +++ inv_clear H. cbn. rewrite E.
            eapply IHxs with (f':=t0) (ac':=t1) in H0; auto.
            unfold res_cap in H0.
            rewrite E in H0.
            destruct (Edge.equal (s,v) (v0,v1)).
            *   inv_clear e. rewrite EdgeMap.FindReplaceEq. lra.   
            *   rewrite EdgeMap.FindReplaceNeq; auto.
        +   set (F := (fun y => _)).
            assert (G : forall x, In x xs -> fst x = s). {
                intros. unfold xs in H. rewrite <- in_rev in H.
                apply EdgeSet.to_list_in in H. unfold es' in H.
                eapply EdgeSet.in_filter in H; auto.
                destruct x. destruct (equal s v0); subst; try lia.
                reflexivity. 
            }
            induction xs; intros f' ac' H.
        ++  cbn in H. inv_clear H. cbn. rewrite E.
            rewrite EdgeMap.FindEmpty. lra.
        ++  cbn in  H.
            destruct (fold_right F (EdgeMap.empty, VertexSet.empty) xs) eqn:E1.
            destruct a.
            assert ((t0, t1) = (t0, t1)) by reflexivity.
            apply IHxs in H0; auto.
        +++ cbn in H0 |- *.
            rewrite E in H0 |- *.
            cbn in H. inv_clear H.
            destruct (Edge.equal (v0, v1) (v, s)).
            *   exfalso. inv_clear e.
                apply L. erewrite <- (G (v, s)); eauto. constructor; auto.
            *   rewrite EdgeMap.FindReplaceNeq; auto. 
        +++ intros. apply G. constructor 2; auto.
    Qed. *)

    (* Kui tipud u ja v kuuluvad tippude hulka ning servade (u, v) läbilaskevõime on mittenegatiivne ja sisend pole väljund ning
     gpr_trace tagastab voo f' ja kõrgused l', siis järeldub, et aktiivsed tipud on ainult sisend või väljund,
     on täidetud voo nõuded ja on säilitatud invariandid, et sisendi kõrgus on võrdne tippude arvuga ja väljundi kõrgus on 0 *)
    Lemma FlowConservationGprMain fn (l: @VertexMap.t nat O):
        let '((vs, es),c,s,t) := fn in
        (forall u v, ((u, v) ∈e es = true) -> (u ∈v vs) = true /\ (v ∈v vs) = true) ->
        True ->
        (forall u v, c u v >= 0) ->
        s<>t ->
        forall f' e' l' tr', 
        gpr_trace fn = (Some (f',l'),tr') ->
        (forall n, ActiveNode fn f' e' n -> n=t \/ n=s) /\ 
        FlowConservationConstraint fn f' e' /\
        (VertexSet.size vs = VertexMap.find 0 l' s)%nat /\ (O=VertexMap.find 0 l' t)%nat.
    Proof. Admitted.
        (* destruct fn as [[[[vs es] c] s] t]. 
        intros H H0 H1 Hst f' l' tr' H2. unfold gpr_trace in H2.
        destruct_guard_in H2. 
        eapply (InitialGpr (vs, es, c, s, t)) in E0 as P; eauto.
        + destruct P, H4, H5, H6, H7. 
        eapply (FlowConservationGpr (vs, es, c, s, t)) in H2; eauto.
        - destruct H2, H9, H10. split; auto. split; auto.
        simpl in H10, H11. rewrite NMap.FindReplaceEq in H10.
        rewrite NMap.FindReplaceNeq, NMap.FindEmpty in H11; auto.
        - simpl. unfold NoSteepArc. intros. simpl. destruct (equal u s).
        * subst. rewrite NMap.FindReplaceEq.
        destruct (equal v s);
        [subst; rewrite NMap.FindReplaceEq; lia|].        
        unfold PreFlowCond in H7.
            eapply InitialPushResCap0 with (v := v) in E0; auto.
            set (r := res_cap _) in *. lra.
        * rewrite NMap.FindReplaceNeq, NMap.FindEmpty; auto. lia.
        - simpl. unfold ValidLabeling. intros. simpl. destruct (equal u s), (equal v s).
        * subst. lia.
        * subst. unfold PR.E in H9. eapply ESet.in_filter in H9. destruct H9.
         eapply InitialPushResCap0 with (v := v) in E0; auto.
          unfold res_cap in E0. rewrite H9 in E0. 
         eapply (reflect_iff _ _ (QLt_spec _ _)) in H10. lra.
         * subst. rewrite NMap.FindReplaceNeq, NMap.FindEmpty; auto. lia.
         * rewrite NMap.FindReplaceNeq, NMap.FindEmpty; auto. lia.
    Qed. *)

End PR.

Module Edge := Tuple (Nat) (Nat).
(* Module EdgeMap := MkMap(Edge).

Module VertexMap := MkMap(Nat).

Module ExcessMap := MkMap(Nat).

Module EdgeSet := MkSet(Edge).

Module VertexSet := MkSet(Nat). *)

Module EdgeMap : MapSpec(Edge).
    Include MkMap(Edge).
End EdgeMap.

Module VertexMap : MapSpec(Nat).
    Include MkMap(Nat). 
End VertexMap.

Module ExcessMap : MapSpec(Nat).
    Include MkMap(Nat).
End ExcessMap.

Module EdgeSet : SetSpec(Edge).
    Include MkSet(Edge).
End EdgeSet.

Module VertexSet : SetSpec(Nat).
    Include MkSet(Nat).
End VertexSet.

Module PRNat := PR (Nat) (Edge) (EdgeMap) (VertexMap) (ExcessMap) (EdgeSet) (VertexSet).

Import ListNotations.
Open Scope nat.

Definition vset_list := fold_right VertexSet.add VertexSet.empty.
Definition eset_list := fold_right EdgeSet.add EdgeSet.empty.

(* Näited, et algoritm tagastab korrektse maksimaalse voo*)
Definition FN1 : PRNat.FlowNet := 
    let c := fun (x y: nat) => 10%Q in
    ((vset_list [0;1],eset_list[(0,1)]),c,0,1).

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
    ((vset_list [0;1;2;3;4;5]),(eset_list[(0,1);(0,3);(1,2);(2,3);(2,5);(3,4);(4,1);(4,5)]),c,0,5).

(* Definition FN3 : PRNat.FlowNet := 
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
    (([0;1;2;3;4;5],[(0,1);(0,2);(1,3);(1,4);(2,4);(3,5);(4,5)]),c,0,5). *)

(* Compute (PRNat.gpr_trace FN1).

Compute (PRNat.gpr_trace FN2).

Compute (@PRNat.excess FN1 [(0,1,10%Q)] 1).

Compute (@PRNat.excess FN2 [(0, 1, 10%Q); (0, 3, 4%Q); (3, 4, 7%Q); (
    4, 1, 0%Q); (1, 2, 10%Q); (2, 5, 7%Q); (
    4, 5, 7%Q); (2, 3, 3%Q)] 5).

Compute (@PRNat.excess FN3 [(0, 1, 4%Q); (0, 2, 2%Q); 
(2, 4, 2%Q); (4, 5, 2%Q); (1, 3, 4%Q); (3, 5, 4%Q)] 5). *)

(* Definition FN_excess : (list nat * list (nat * nat) * (nat -> nat -> Q) * nat * nat)%type :=
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
  (([0;1;2;3;4;5;6],[(0,5);(1,2);(1,4);(2,3);(3,4);(3,6);(4,2);(5,1);(5,2)]), c, 0, 6). *)

(* Definition FN_rand_test : (list nat * list (nat * nat) * (nat -> nat -> Q) * nat * nat)%type :=
  let c := fun (x y : nat) =>
    match x, y with
    | 0, 1 => 8%Q
    | 0, 2 => 19%Q
    | 1, 2 => 18%Q
    | _, _ => 0%Q
    end
  in
  (([0;1;2],[(0,1);(0,2);(1,2)]), c, 0, 2). *)

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

(* Print Lists.List. *)
Extraction Language OCaml.
(* Require Import ZArith. *)
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlZInt.
Require Import ExtrOcamlNatInt.
Extract Inductive Q => "(int * int)" [ "" ].
Extract Constant length => "List.length".
Extract Constant map => "List.map".
Set Extraction File Comment "Extracted from the push-relabel algorithm proof in Rocq.".


Extract Constant VertexMap.t "'e" => "'e VertexMap'.t".
Extract Constant VertexMap.empty => "fun _d -> VertexMap'.create 1".
Extract Constant VertexMap.find => 
    "fun d k m -> 
    try VertexMap'.find k m with Not_found -> d".
Extract Constant VertexMap.replace => "fun _d k v m -> VertexMap'.replace m k v; m".
Extract Constant VertexMap.update => 
    "fun d k f m -> 
        let old = try VertexMap'.find m k with Not_found -> d
        in VertexMap'.replace m k (f old); m".

Extract Constant EdgeMap.t "'e" => "'e EdgeMap'.t".
Extract Constant EdgeMap.empty => "fun _d -> EdgeMap'.create 1".
Extract Constant EdgeMap.find => 
    "fun d k m -> 
    try EdgeMap'.find k m with Not_found -> d".
Extract Constant EdgeMap.replace => "fun _d k v m -> EdgeMap'.replace m k v; m".
Extract Constant EdgeMap.update => 
    "fun d k f m -> 
        let old = try EdgeMap'.find m k with Not_found -> d
        in EdgeMap'.replace m k (f old); m".

Extract Constant ExcessMap.t "'e" => "'e ExcessMap'.t".
Extract Constant ExcessMap.empty => "fun _d -> ExcessMap'.create 1".
Extract Constant ExcessMap.find => 
    "fun d k m -> 
    try ExcessMap'.find k m with Not_found -> d".
Extract Constant ExcessMap.replace => "fun _d k v m -> ExcessMap'.replace m k v; m".
Extract Constant ExcessMap.update => 
    "fun d k f m -> 
        let old = try ExcessMap'.find m k with Not_found -> d
        in ExcessMap'.replace m k (f old); m".

Extract Constant VertexSet.t => "VertexSet'.t".
Extract Constant VertexSet.empty => "VertexSet'.empty".
Extract Constant VertexSet.remove => "VertexSet'.remove".
Extract Constant VertexSet.add => "VertexSet'.add".
Extract Constant VertexSet.mem => "VertexSet'.mem".
Extract Constant VertexSet.choice => "fun xs -> 
    match VertexSet'.choose_opt xs with
    | None -> None
    | Some x -> Some (x, VertexSet'.remove x xs)".
Extract Constant VertexSet.filter => "VertexSet'.filter".
Extract Constant VertexSet.to_list => "VertexSet'.elements".
Extract Constant VertexSet.find_first => 
    "fun p xs -> Seq.find p (VertexSet'.to_seq xs)".
Extract Constant VertexSet.size => "VertexSet'.cardinal".

Extract Constant EdgeSet.t => "EdgeSet'.t".
Extract Constant EdgeSet.empty => "EdgeSet'.empty".
Extract Constant EdgeSet.remove => "EdgeSet'.remove".
Extract Constant EdgeSet.add => "EdgeSet'.add".
Extract Constant EdgeSet.mem => "EdgeSet'.mem".
Extract Constant EdgeSet.choice => "fun xs -> 
    match EdgeSet'.choose_opt xs with
    | None -> None
    | Some x -> Some (x, EdgeSet'.remove x xs)".
Extract Constant EdgeSet.filter => "EdgeSet'.filter".
Extract Constant EdgeSet.to_list => "EdgeSet'.elements".
Extract Constant EdgeSet.find_first => "EdgeSet'.find_first_opt".
Extract Constant EdgeSet.size => "EdgeSet'.cardinal".


Recursive Extraction PRNat.gpr_trace.






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
Muudatused 2: 0.0670ms
Muudatused 3: 0.0276ms

1: täis- ja ratsionaalarvud muudetud + tõeväärtused, listid jne (OCamlBasic jne)
2: VertexMap ja EdgeMap asemel OCamli mapid/paisktabelid.
3: OCamlis servade compare ja equal, listide length ja map asendatud. 
    Excessi cache-mine mapiga, VertexSet ja EdgeSet on hulgad.
*)


Recursive Extraction PRNat.gpr_trace.
(* Recursive Extraction FN_rand40_250. *)
(* dune exec push-relabel *)