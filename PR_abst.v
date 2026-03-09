(* by Kalmer Apinis *)

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
    Qed.
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

    Definition E (fn: FlowNet) (f: EMap.t R)  :=
        let '((vs, es),c,s,t) := fn in
        ESet.filter (fun '(u, v) => EMap.find 0 f (u,v) <? c u v) es.    
    
    Definition res_net (fn: FlowNet) (f: EMap.t R)  : FlowNet :=
        let '((vs, es),c,s,t) := fn in
        ((vs,E fn f),res_cap fn f,s,t).

    (* valib tipu u ülejäägist ning läbilaskevõimest Qmin abil miinimumi ja saadab selle voona edasi järgmisesse tippu v.
     Kui (u,v) ∈e es ehk serv (u, v) kuulub hulka es tagastab true, siis suurendatakse serva (u, v) voogu delta võrra. 
     False korral vähendatakse serva (v, u) voogu delta võrra. *)
    Definition push fn f u v : EMap.t R :=
        let '((vs, es),c,s,t) := fn in
        let delta := Qmin (excess fn f u) (res_cap fn f u v) in
        if (u,v) ∈e es  then
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
    Definition has_excess_not_sink fn f v  :=
        let '((vs, es),c,s,t) := fn in
        if T.eqb v t || T.eqb v s then
            false
        else if 0 <? excess fn f v then 
            true
        else
            false
    .

    Inductive Tr : Type :=
        | Init: EMap.t Q -> NMap.t nat -> VSet.t ->  Tr
        | Push: V -> V -> EMap.t Q -> VSet.t ->  Tr
        | Relabel : V -> nat -> NMap.t nat ->  Tr
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
                if has_excess_not_sink fn f' v  then 
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
                    if has_excess_not_sink fn f' v  then 
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
        fold_left (fun  '(f, ac) '(u,v) => 
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

    
    (* Iga serva korral ei ole voog suurem kui läbilaskevõime *)
    Definition CapacityConstraint (fn:FlowNet) (f:EMap.t Q) := 
        let '((vs, es),c,s,t) := fn in
        forall u v, ESet.mem (u,v) es = true -> 
            EMap.find 0 f (u,v) <= c u v.
    
    (* Tagastab true, kui igas tipus v, mis ei ole sisend, on ülejääk mittenegatiivne *)
    Definition NonDeficientFlowConstraint (fn:FlowNet) (f:EMap.t Q) := 
        let '((vs, es),c,s,t) := fn in
        forall v, (v ∈v vs) = true -> v<>s -> 0 <= excess fn f v.

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
    Lemma PushValidLabel fn (f:EMap.t Q) (l:NMap.t nat) x y:
        let '((vs, es),c,s,t) := fn in
        ValidLabeling fn f l -> PushCondition fn f l x y
                -> ValidLabeling fn (push fn f x y) l.
    Proof.
        intros. destruct fn as [[[[vs es] c] s] t]. unfold ValidLabeling, PushCondition.
        intros. unfold push in H1. destruct ((x, y) ∈e es) eqn : E.
        + unfold PR.E in *. apply ESet.in_filter in H1. destruct H1.  
        apply H. apply ESet.filter_in.
        - auto.
        - destruct (Edge.equal (x,y) (u, v)).
        * inversion e. subst. rewrite EMap.FindUpdateEq in H2. 
        eapply (reflect_iff _ _ (QLt_spec _ _)). 
        eapply (reflect_iff _ _ (QLt_spec _ _)) in H2.
        unfold res_cap in H2. rewrite E in H2.
        destruct ( Q.min_dec (excess (vs, es, c, s, t) f u) (c u v - EMap.find  0 f (u, v))).
        ** rewrite q in H2. lra.
        ** rewrite q in H2. unfold R in H2. lra.
        * rewrite EMap.FindUpdateNeq in H2; auto.
        + unfold PR.E in *. apply ESet.in_filter in H1. destruct H1.
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

    (* Lemma RFindMinSomeCondition (l:NMap.t nat) vs': forall v r vs'', 
    In r vs'' ->
    (forall v', In v' vs'' -> (NMap.find 0 l r <= NMap.find 0 l v')%nat) ->

    smallest_rank l vs' (Some r)

        List.fold_left (fun r v0 => 
            match r with
            | Some r0 => if (NMap.find 0 l r0 <=? NMap.find 0 l v0)%nat then Some r0 else Some v0
            | None => Some v0
            end) vs' (Some r) = Some v ->
        forall v', (In v' vs' \/In v' vs'') -> (NMap.find 0 l v <= NMap.find 0 l v')%nat.
    Proof. (*
        induction vs'; intros.
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
    Admitted.

    Lemma RFindMinNoneCondition (l:NMap.t nat) vs': forall v, 
        List.fold_left (fun r v0 => 
            match r with
            | Some r0 => if (NMap.find 0 l r0 <=? NMap.find 0 l v0)%nat then Some r0 else Some v0
            | None => Some v0
            end) vs' None = Some v ->
        forall v', (In v' vs') -> (NMap.find 0 l v <= NMap.find 0 l v')%nat.
    Proof.
        (* intros. induction vs'.
        + simpl in H0. inversion H0.
        + simpl in H. eapply (RFindMinSomeCondition _ _ _ a (a::nil)) in H.
        - apply H.
        - simpl. rewrite eqb_refl. reflexivity.
        - intros. simpl in H1. destruct (equal v'0 a); subst. auto.
        inversion H1.
        - simpl in H0. destruct (equal v' a).
        * subst. right. simpl. rewrite eqb_refl. reflexivity.
        * left. apply H0.
        Qed. *)
    Admitted.

    Lemma RFindMinMemCondition (l:NMap.t nat) vs': forall v, 
        List.fold_left (fun r v0 => 
            match r with
            | Some r0 => if (NMap.find 0 l r0 <=? NMap.find 0 l v0)%nat then Some r0 else Some v0
            | None => Some v0
            end) vs' None = Some v ->
            In v vs'.    
    Proof.
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
    Admitted. *)

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

    Lemma SumSame (f:EMap.t Q) (s:V->V*V) vs u v d : 
        (forall v0,  In v0 vs -> s v0 <> (u, v)) ->
        map (fun v0 => EMap.find 0 
            (EMap.update 0 (u, v) (fun x0 => x0 + d) f) 
            (s v0)) vs = 
        map (fun v0 => EMap.find 0 f (s v0)) vs.
    Proof.
        induction vs; intros.
        + simpl. auto.
        + simpl. erewrite IHvs; auto.
        f_equal. clear IHvs. erewrite EMap.FindUpdateNeq.
        - auto.
        - apply H. cbn. auto.
        - intros. apply H. cbn. tauto.
    Qed.
    
    Lemma PushActiveCondition (fn:FlowNet) (f:EMap.t R ) u v x: 
        ActiveNode fn f x -> x<>v -> x<>u -> ActiveNode fn (push fn f u v) x .
        Proof.
            unfold ActiveNode. destruct fn as [[[[vs es] c] s] t]. intros.
            unfold push. destruct ((u, v) ∈e es) eqn : E.
            + unfold excess. set (d := Qmin _ _). rewrite SumSame.
            - rewrite SumSame.
            * apply H. 
            * intros v0 _ q. inversion q. subst. apply H1. auto.
            - intros v0 _ q. inversion q. subst. apply H0. auto. 
            +  set (d := Qmin _ _). unfold excess. unfold Qminus. rewrite SumSame.
            - rewrite SumSame.
            * apply H.
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

    Lemma PushFlowMapPos fn (f:EMap.t Q) (l:NMap.t nat) x y:
        let '((vs, es),c,s,t) := fn in
        (x ∈v vs) = true ->
        FlowMapPositiveConstraint fn f -> 
        PreFlowCond fn f ->
        PushCondition fn f l x y ->
        FlowMapPositiveConstraint fn (push fn f x y).
    Proof.
        unfold FlowMapPositiveConstraint, PreFlowCond, PushCondition.
        unfold CapacityConstraint, NonDeficientFlowConstraint.
        destruct fn as [[[[vs es] c] s] t]. intros. split.
        + unfold push. destruct ((x, y) ∈e es) eqn : E.
        - destruct (Edge.equal (x,y) (u,v)).
        * inv_clear e. rewrite EMap.FindUpdateEq.
        eapply (DeltaPositive ((vs, es),c,s,t)) in H2; auto.
        specialize (H0 u v). lra.
        * rewrite EMap.FindUpdateNeq; auto.
        apply H0.
        - destruct (Edge.equal (y,x) (u,v)).
        * inv_clear e. rewrite EMap.FindUpdateEq.
        unfold res_cap. rewrite E. edestruct (Q.min_spec_le); destruct H3.
        ** erewrite H4. unfold R in *. lra.
        ** erewrite H4. unfold R in *. lra.
        * rewrite EMap.FindUpdateNeq; auto.
            apply H0.
            + apply H0.
    Qed.        


    Lemma SumInR (f:EMap.t Q ) vs u v d : 
        Distinct vs ->
        In u vs ->
        QSumList (
            map (fun v0 => EMap.find 0
                  (EMap.update 0 (u, v) (fun x0 => x0 + d) f) 
                  (v0, v)) vs) == 
        QSumList (map (fun v0 => EMap.find 0 f (v0, v)) vs) + d.
    Proof. 
        induction vs; intros.
        + simpl. inversion H0.
        + simpl. destruct (equal u a).
        - subst. rewrite EMap.FindUpdateEq. erewrite SumSame.
        * unfold R in *. lra.
        * intros. intro C. inv_clear C. inv_clear H. tauto. 
        - rewrite EMap.FindUpdateNeq.
        * erewrite IHvs.
        ** lra.
        ** inversion H. auto.
        **  simpl in H0.
            destruct H0; subst; try tauto.
        * intro C. inv_clear C. apply n. reflexivity.
    Qed. 


    Lemma SumInL (f:EMap.t Q) vs: forall u v d,
        Distinct vs ->
        In v vs ->
        QSumList (
            map (fun v0 => EMap.find 0 
                  (EMap.update 0 (u, v) (fun x0 => x0 + d) f) 
                  (u,v0)) vs) == 
        QSumList (map (fun v0 => EMap.find 0 f (u,v0)) vs) + d.
    Proof.
        induction vs; intros.
        + simpl. inversion H0.
        + simpl. destruct (equal v a).
        - subst. rewrite EMap.FindUpdateEq. erewrite SumSame.
        * unfold R in *. lra.
        * intros. intro C. inv_clear C. inv_clear H. tauto.
        - rewrite EMap.FindUpdateNeq.
        * erewrite IHvs.
        ** lra.
        ** inversion H. subst. auto.
        ** simpl in H0. destruct H0; subst; try tauto.
        * intro C. inv_clear C. apply n. reflexivity.
    Qed.

    (* Kui on rahuldatud eelvoo tingimused ning vood ja läbilaskevõimed on mittenegatiivsed 
    ja leidub tipp, kuhu saab push sammu teha, siis järeldub, et ka peale push sammu on eelvoo tingimused säilitatud *)
    Lemma PushPreFlow fn (f:EMap.t Q) (l:NMap.t nat) x y:
        let '((vs, es),c,s,t) := fn in
        (* VSet.IsSet vs -> *)
        (x ∈v vs) = true ->
        (y ∈v vs) = true ->
        PreFlowCond fn f -> 
        FlowMapPositiveConstraint fn f ->
        PushCondition fn f l x y->
        PreFlowCond fn (push fn f x y).
    Proof.
        unfold PreFlowCond, FlowMapPositiveConstraint, PushCondition, PreFlowCond.
        unfold CapacityConstraint, NonDeficientFlowConstraint.
        destruct fn as [[[[vs es] c] s] t].
        intros Hxvs Hyvs [Hcc Hndf] Hfmp Hpc.
        split.
        + intros. unfold push. destruct ((x, y) ∈e es) eqn : E.
        - destruct (Edge.equal (x,y) (u,v)). 
        * inv_clear e. rewrite EMap.FindUpdateEq. unfold res_cap.
        rewrite E. edestruct (Q.min_spec_le); destruct H0.
        ** erewrite H1. unfold R in *. lra.
        ** erewrite H1. unfold R in *. lra.
        * rewrite EMap.FindUpdateNeq; auto.
        - unfold res_cap. rewrite E. destruct (Edge.equal (y,x) (u,v)).
        * inv_clear e. rewrite EMap.FindUpdateEq. edestruct (Q.min_spec_le); destruct H0.
        ** erewrite H1. specialize (Hcc _ _ H). lra.
        ** rewrite H1. specialize (Hfmp u v). unfold R in *. lra.
        * rewrite EMap.FindUpdateNeq; auto.
        +   intros. 
            pose proof (L1:=VSet.to_list_distinct vs).
            apply VSet.to_list_in in H as L2.
            apply VSet.to_list_in in Hxvs as L3.
            apply VSet.to_list_in in Hyvs as L4.
            eapply (DeltaPositive ((vs, es),c,s,t)) in Hpc as HDp; auto;
        [| unfold PreFlowCond, CapacityConstraint, NonDeficientFlowConstraint; tauto].        
        unfold push, res_cap in *. destruct ((x, y) ∈e es) eqn : E.
        -   unfold excess at 1. destruct (equal v y). 
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
    Qed.

    Lemma FPNinVs fn f l u v vs': 
        find_push_node fn f l u vs' = Some v -> (v ∈v vs') = true.
    Proof.
        destruct fn as [[[[vs es] c] s] t]. intros H. 
        unfold find_push_node in H. apply VSet.find_first_specSome in H as [_ H].
        auto.
    Qed.

    Lemma HENSCondition fn v :forall (f:EMap.t Q),
        has_excess_not_sink fn f v = true -> 0 < excess fn f v /\ v <> sink fn /\ v <> source fn.
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

    Lemma PushActiveInv (fn:FlowNet) (f:EMap.t R) (l:NMap.t nat) u v x:
        (* VSet.IsSet (nodes fn) -> *)
        u ∈v nodes fn = true ->
        v ∈v nodes fn = true ->
        x<>v ->
        PreFlowCond fn f ->
        FlowMapPositiveConstraint fn f ->
        PushCondition fn f l u v ->
        ActiveNode fn (push fn f u v) x ->
        ActiveNode fn f x.
    Proof.
        unfold ActiveNode, push, PreFlowCond, 
        FlowConservationConstraint, PushCondition.
        destruct fn as [[[[vs es] c] s] t].
        pose proof (H:= True).
        intros H0 H1 H2 H3 H4 H5 H6.
        cbn in H0, H1.
        pose proof (L1:=VSet.to_list_distinct vs).
        apply VSet.to_list_in in H0 as L2.
        apply VSet.to_list_in in H1 as L3.
        destruct ((u, v) ∈e es) eqn:E0.
        + destruct H6. split; auto. 
        unfold excess in *.
        destruct (equal x u) in H7.
        -   subst. 
            erewrite SumSame, SumInL in H7; auto.
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

    Lemma HENSConditionFalse fn v :forall (f:EMap.t Q),
        has_excess_not_sink fn f v = false -> 0 >= excess fn f v \/ v = sink fn \/ v = source fn.
    Proof.
        unfold has_excess_not_sink.
        intros. destruct fn as [[[[vs es] c] s] t].
        destruct (equal v t), (equal v s); subst; auto.
        cbn in H. set (q := _ <? _) in H.
        destruct q eqn:E0; [inversion H|].
        unfold q in E0. apply QLt_false in E0. 
        cbn. left. apply E0.
    Qed.

    Lemma PushNoSteepArc fn f l x y:
        (x ∈v nodes fn) = true -> 
        FlowMapPositiveConstraint fn f ->
        PreFlowCond fn f -> 
        PushCondition fn f l x y ->
        NoSteepArc fn f l -> NoSteepArc fn (push fn f x y) l.
    Proof.
        unfold FlowMapPositiveConstraint, PreFlowCond, PushCondition,
        NoSteepArc. unfold CapacityConstraint, NonDeficientFlowConstraint.
        destruct fn as [[[[vs es] c] s] t].
        intros. unfold push in H4. set (d:= Qmin _ _) in H4. 
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

    Lemma PushResCapNodes fn f x y:        
        x ∈v (nodes fn) = true -> y ∈v (nodes fn) = true ->
        ResCapNodes fn f -> ResCapNodes fn (push fn f x y).
    Proof.
        unfold ResCapNodes.
        intros. unfold push in H2. destruct fn as [[[[vs es] c] s] t].
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

    (* Siis kui gpr_helper_trace tagastab voo f' ja kõrgused l', siis järeldub, et ainukesed aktiivsed tipud on sisend või väljund,
     täidetud on voo säilivus nõue ja sisendi ning väljundi kõrgused on samad, mis alguses ehk invariante ei rikuta.  *)
    Lemma FlowConservationGpr fn g:forall (f:EMap.t Q) (l:NMap.t nat) ac tr,
        let '((vs, es),c,s,t) := fn in
        (* Iga tipp u ja v korral, kui nende vahel on serv, siis need tipud kuuluvad tippude hulka*)
        (forall u v, ((u, v) ∈e es = true) -> (u ∈v vs) = true /\ (v ∈v vs) = true) ->
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
        forall f' l' tr', 
        gpr_helper_trace fn f l ac g tr = (Some (f', l'),tr') ->
        (* Iga tipu n korral, mis on aktiivne on n väljund või sisend*)
        (forall n, ActiveNode fn f' n -> n=t \/ n=s) /\
        (* Täidetud on voo säilivuse nõue*)
        FlowConservationConstraint fn f' /\
        (* Sisendi ja väljundi kõrgus on funktsiooni gpr_helper_trace lõpus sama, mis oli alguses *)
        (NMap.find 0 l s)%nat = (NMap.find 0 l' s)%nat /\ (NMap.find 0 l t)%nat = (NMap.find 0 l' t)%nat.
    Proof.        
        destruct fn as [[[[vs es] c] s] t]. induction g;
        intros f l ac tr Heisn Hrcn Hnsa Hnvs Hvl Han Hprc Hfmpc f' l' tr' H.
        + simpl in H. inversion H.
        + rewrite gpr_helper_trace_fn in H. destruct_guard_in H.
        - destruct p. destruct_guard_in H.
        * cbn zeta in H. destruct_guard_in H.
        ** apply VSet.choiceSome in E0. destruct E0. 
         eapply IHg in H; eauto.
        (* *** clear H IHg. destruct_guard.
        **** apply VSet.AddIsSet. auto.
        **** apply VSet.AddIsSet; auto. *)
        *** clear H IHg. apply PushResCapNodes; auto.
        **** apply FPNinVs in E1. auto.
        *** clear H IHg. apply PushNoSteepArc; auto.
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
        *** clear H IHg. eapply (PushValidLabel (vs, es, c ,s, t)); auto.
        eapply FPNCondition; eauto. apply Han in H0. tauto.
        *** intros. split; intros.
        **** destruct (equal n v0).
        ***** subst. clear H IHg. apply HENSCondition in E2. split; try tauto.
        split.
        ****** eapply FPNinVs in E1. auto.
        ****** tauto.
        ***** clear H IHg. rewrite VSet.MemAddNeq in H2; eauto.
        destruct_guard_in H2.
        ****** eapply Han in H2. destruct H2. split; eauto.
        destruct (equal n v). subst.
        *******  eapply (reflect_iff _ _ (QLt_spec _ _)) in E0. split; eauto.
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
        ******* intro C. subst. destruct H2. destruct H. apply QLt_false in E0. lra.
        *** clear H IHg. eapply (PushPreFlow (vs, es, c, s, t)); auto. 
        **** eapply FPNinVs in E1. auto.
        **** eapply FPNCondition; eauto. eapply Han in H0; tauto.
        *** clear H IHg. eapply (PushFlowMapPos (vs, es, c, s, t)); eauto.
        eapply FPNCondition; eauto. eapply Han in H0. tauto.
        ** eapply VSet.choiceSome in E0 as P; auto. destruct P.
        eapply FPNinVs in E1 as P. apply Han in H0 as W. destruct W. 
        eapply FPNCondition in E1 as P2; auto.
        eapply HENSConditionFalse in E2 as Q.
        eapply IHg in H; eauto.
        *** eapply PushResCapNodes; auto.
        *** eapply PushNoSteepArc; auto.
        *** intros. destruct (equal n v0).
        **** subst. auto.
        **** rewrite VSet.MemRemoveNeq in H4; auto. eapply Hnvs.
         destruct_guard_in H4; auto. subst.
         rewrite VSet.MemRemoveNeq in H4; auto.
         intro C. subst. rewrite VSet.MemRemoveEq in H4. inversion H4.
        *** eapply (PushValidLabel (vs, es, c, s, t)); eauto.
        *** intros. destruct (equal n v0).
        **** subst. rewrite VSet.MemRemoveEq. split; intros; [inversion H1 |].
        destruct Q.
        ***** destruct H1. destruct H1. lra.
        ***** simpl in H4. tauto.
        **** rewrite VSet.MemRemoveNeq; auto. destruct_guard; split; intros.
        ***** eapply Han in H4. destruct H4. split; auto. destruct (equal n v).
        ****** subst. split; auto.  eapply (reflect_iff _ _ (QLt_spec _ _)) in E3.
        auto.
        ****** eapply PushActiveCondition; eauto.
        ***** eapply Han. destruct H4. split; auto.
        eapply PushActiveInv in P2; eauto.
        ***** subst. destruct (equal n v).
        ****** subst. rewrite VSet.MemRemoveEq in H4. inversion H4.
        ****** rewrite VSet.MemRemoveNeq in H4; auto. 
        eapply Han in H4. destruct H4. split; auto. 
        eapply PushActiveCondition; eauto.
        ***** subst. destruct (equal n v).
        ****** subst. eapply QLt_false in E3. destruct H4, H1. lra.
        ****** rewrite VSet.MemRemoveNeq; auto. eapply Han. destruct H4. split; auto.
        eapply PushActiveInv in P2; eauto.
        *** eapply (PushPreFlow (vs, es, c, s, t)); eauto.
        *** eapply (PushFlowMapPos (vs, es, c, s, t)); eauto.
        * destruct_guard_in H.
        ** eapply VSet.choiceSome in E0; auto. destruct E0, H1.
         eapply IHg in H; eauto.
        *** split; try tauto. split; try tauto.
            destruct H, H1, H2. rewrite <- H2, <- H3. subst.
            unfold relabel in E2. destruct_guard_in E2; [|inversion E2]. inv_clear E2.
            destruct (equal s v).
        **** subst. exfalso. apply Han in H0. destruct H0, H4. auto.
        **** rewrite NMap.FindReplaceNeq; auto. split; auto.
            destruct (equal t v). 
        ***** subst. exfalso. apply Han in H0. destruct H0. destruct H4; auto.
        ***** rewrite NMap.FindReplaceNeq; auto.
        *** eapply RelabelNoSteepArc; eauto.
        *** eapply (RelabelValidLabel (vs, es, c, s, t)); eauto. 
        unfold relabel in E2. destruct_guard_in E2; [| inversion E2].
        eapply RelabelValidCondition; eauto.
        **** apply Han. auto.
        ** inversion H. 
        - apply VSet.choiceNone in E0. subst. inv_clear H. split.
        * intros. destruct (equal n t); auto. 
        destruct (equal n s); subst; try tauto.
        assert (n ∈v VSet.empty = true).
        ** eapply Han. tauto.
        ** rewrite VSet.MemEmpty in H0. inversion H0.
        * split; try tauto.
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
        EMap.find 0 f (s,y) <= d ->
        n<>s ->
        excess (vs, es, c, s, t) f n <= 
            excess (vs, es, c, s, t) (EMap.replace (s, y) d f) n .
    Proof.
        intros Hd Hnns. unfold excess.
        set (xs := VSet.to_list vs).
        induction xs; intros.
        + simpl. lra. 
        + unfold excess in *. simpl. destruct (equal n y).
        - subst. destruct (equal a s).
        * subst. erewrite EMap.FindReplaceEq. erewrite EMap.FindReplaceNeq.
        ** unfold R in *. lra.
        ** intro C. inv_clear C. auto.
        * erewrite EMap.FindReplaceNeq, EMap.FindReplaceNeq.
        ** unfold R in *. lra.
        ** intro C. inv_clear C. auto.
        ** intro C. inv_clear C. auto.
        - erewrite EMap.FindReplaceNeq, EMap.FindReplaceNeq.
        * lra.
        *  intro C. inv_clear C. auto.
        * intro C. inv_clear C. auto.
    Qed.

    Lemma SourceDeficient vs es c s t y f: 
        (forall a, EMap.find 0 f (a,s) <= EMap.find 0 f (s,a)) ->
        EMap.find 0 f (s,y) <= c s y ->
        excess (vs, es, c, s, t) (EMap.replace (s, y) (c s y) f) s <= 0.
    Proof.
        intros Has Hcap. unfold excess.
        set (xs := VSet.to_list vs).
        induction xs; intros.
        + simpl. lra.
        + unfold excess in *. simpl. destruct (Edge.equal (s,y) (a,s)).
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
        excess (vs, es, c, s, t) f n  == excess (vs, es, c, s, t) (EMap.replace (s, y) (c s y) f) n.
    Proof.
        intros Has Hcap Hnns Hnny. unfold excess.
        set (xs := VSet.to_list vs).
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

    Lemma InitialUpdateBigger: forall f s v0 n c, 
        (forall u v, EMap.find 0 f (u, v) <= c u v) -> forall xs,
        QSumList (map (fun v1 : V => EMap.find 0 (EMap.replace (s, v0) (c s v0) f) (v1, n)) xs) >= QSumList (map (fun v1 : V => EMap.find 0 f (v1, n)) xs).
    Proof.
        intros f s v0 n c P xs.
        induction xs; cbn; intros; try lra.
        destruct (Edge.equal (a,n) (s,v0)).
        +   inv_clear e.
            rewrite EMap.FindReplaceEq.
            specialize (P s v0). lra.
        +   rewrite EMap.FindReplaceNeq; auto. lra.
    Qed.

    (* Peale initsialiseerimist on aktiivsete tippude hulgas tipud, mis ei ole sisend ega väljund ja on täidetud eelvoo nõuded
     ja vood ning läbilaskevõimed on mittenegatiivsed*)
    Lemma InitialGpr fn :
        let '((vs, es),c,s,t) := fn in
        (* Iga tipp u ja v korral, kui nende vahel on serv, siis need tipud kuuluvad tippude hulka*)
        (forall u v, ((u, v) ∈e es = true) -> (u ∈v vs) = true /\ (v ∈v vs) = true) ->
        (forall u v, c u v >= 0) ->
        forall f' ac' ,
        (* Kui algoritmi initsialiseerimise samm, kus tehakse push samm sisendist väljuvate servade peal
        tagastab voo f' ja aktiivsed tipud ac', siis sellest järeldub all olev konjuktsioon*)
        initial_push fn = (f',ac') ->
        ResCapNodes fn f' /\
        (forall u v, EMap.find 0 f' (u, v) <= c u v) /\
        (forall n, n ∈v ac' = true -> n ∈v vs = true) /\
        (forall n, n ∈v ac' = true <-> (ActiveNode fn f' n /\ n<>t /\ n<>s)) /\
        PreFlowCond fn f' /\
        FlowMapPositiveConstraint fn f'.
    Proof.
        destruct fn as [[[[vs es] c] s] t].
        intros Hvs Hc.
        unfold initial_push.
        set (es' := ESet.filter _ _).
        rewrite <- fold_left_rev_right.
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
        set (F := (fun y => _)).
        induction xs; intros f' ac' H.
        +   cbn in H. inv_clear H.
             repeat split; auto.
        ++  cbn in H. destruct_guard_in H.
        +++ apply Hvs in E0. tauto.
        +++ rewrite EMap.FindEmpty in H. lra.
        ++  cbn in H. destruct_guard_in H.
        +++ apply Hvs in E0. tauto.
        +++ rewrite EMap.FindEmpty in H. lra.
        ++  intros. rewrite EMap.FindEmpty. apply Hc.
        ++  intros. rewrite VSet.MemEmpty in H. inversion H.
        ++  rewrite VSet.MemEmpty in H. inversion H.
        ++  rewrite VSet.MemEmpty in H. inversion H.
        ++  rewrite VSet.MemEmpty in H. inversion H.
        ++  rewrite VSet.MemEmpty in H. inversion H.
        ++  intros [[H0 H1] [H2 H3]]. cbn in H1.
            set (ys:=VSet.to_list vs) in H1. exfalso. clear -H1.
            induction ys.
        +++ cbn in H1. lra.
        +++ cbn in *. repeat rewrite EMap.FindEmpty in H1. lra.
        ++  cbn. intros. rewrite EMap.FindEmpty. apply Hc.
        ++  cbn. intros. set (ys:=VSet.to_list vs). clear -ys .
            induction ys.
        +++ cbn. lra.
        +++ cbn. repeat rewrite EMap.FindEmpty. lra.
        ++  rewrite EMap.FindEmpty. lra.
        +   simpl fold_right in H. destruct a.
            destruct (fold_right F (EMap.empty, VSet.empty) xs) eqn:E.
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
            *   rewrite EMap.FindReplaceNeq in H; auto.
                apply H1 in H. cbn. tauto.
        ++  unfold res_cap in H. 
            specialize (H1 u v1).
            unfold res_cap in H1.
            destruct ((u, v1) ∈e es) eqn:E1.
        +++ apply Hvs in E1. tauto.
        +++ destruct (Edge.equal (s,v0) (v1,u)).
            *   inv_clear e. cbn. tauto.
            *   rewrite EMap.FindReplaceNeq in H; auto.
                apply H1 in H. cbn. tauto.
        ++  intros. 
            destruct (Edge.equal (s,v0) (u,v1)).
        +++ inv_clear e. rewrite EMap.FindReplaceEq. lra.
        +++ rewrite EMap.FindReplaceNeq; auto.
        ++  intros. 
            destruct (equal v0 t); cbn in H; subst; auto.
            destruct (equal v0 s); cbn in H; subst; auto.
            destruct_guard_in H; auto.
            destruct (equal n v0); cbn in H; subst; try  tauto.
            erewrite VSet.MemAddNeq in H; auto.
        ++  intros. 
            destruct (equal v0 t); cbn in H; subst; auto.
            destruct (equal v0 s); cbn in H; subst; auto.
            destruct_guard_in H; auto.
            destruct (equal n v0); cbn in H; subst; try  tauto.
            erewrite VSet.MemAddNeq in H; auto.
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
                rewrite VSet.MemAddNeq in H; auto.
                apply H4 in H. destruct H. cbn in H. destruct H.
                rewrite SumNoL; [|tauto].
                auto.
            **  apply H4 in H. destruct H. cbn in H. destruct H.
                rewrite SumNoL; [|tauto].
                rewrite SumNoL in E1; [|tauto].
                eapply InitialUpdateBigger  with (n:=n) (xs:=VSet.to_list vs) (v0:=v0) (s:=s)in H2. 
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
                rewrite VSet.MemAddNeq in H; auto.
                apply H4 in H; tauto.
            **  apply H4 in H. tauto.
        ++  destruct (equal v0 t); subst; cbn in H.
        +++ apply H4 in H. tauto.
        +++ destruct (equal v0 s); subst; cbn in H.
            *   apply H4 in H. tauto.
            *   set (d := _ - _) in H.
                destruct (0 <? d) eqn:E3.
            **  destruct (equal n v0); cbn in H; subst; try  tauto.
                rewrite VSet.MemAddNeq in H; auto.
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
            *** apply VSet.MemAddEq.
            *** cbn.
                rewrite VSet.MemAddNeq; auto.
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
                    rewrite EMap.FindReplaceEq. lra.
                *   rewrite EMap.FindReplaceNeq; auto.
            ++  unfold NonDeficientFlowConstraint. intros.
                destruct H5, H5.
                unfold NonDeficientFlowConstraint in H7.
                specialize (H7 _ H H0). clear -H7 H0 H2 Hc.
                unfold excess in *.
                destruct (equal v0 v1); subst.
            +++ rewrite SumNoL; auto.
                eapply InitialUpdateBigger  with (n:=v1) (xs:=VSet.to_list vs) (v0:=v1) (s:=s)in H2.
                set (q1:= QSumList _) in H2, H7.
                set (q2:= QSumList _) in H2 |- *.
                set (q3:= QSumList _) in H2, H7 |- *.
                lra. 
            +++ rewrite SumNoL; auto.
                rewrite SumNoR; auto.
            ++  destruct (Edge.equal (s,v0) (u,v1)).
            +++ inv_clear e. rewrite EMap.FindReplaceEq. apply Hc.
            +++ rewrite EMap.FindReplaceNeq; auto. 
                destruct H5, H. unfold FlowMapPositiveConstraint in H0.
                destruct (H0 u v1). auto.
    Qed.

    (* Kui Iga serva e korral e kuulub hulka e' või e'', siis ta kuulub hulka es ja iga tipu v korral, kui puudub serv
    (s, v), siis sellel serva läbilaskevõime on 0 ning 
    iga tipu v korral, kui serv (s, v) kuulub hulka e', siis sellel serva läbilaskevõime on 0, sellest järeldub, et
    peale initsialiseerimist on kõik sisendist väljuvate servade läbilaskevõime ära kasutatud *)
    Lemma InitialPushResCap0 vs es c s t v : 
        v<>s -> forall  f' ac',
        initial_push (vs,es,c,s,t) = (f',ac') ->
        res_cap (vs,es,c,s,t) f' s v == 0.
    Proof.
    unfold initial_push.
    set (es' := ESet.filter _ _).
    rewrite <- fold_left_rev_right.
    set (xs := rev _). intros L.
    destruct ((s, v) ∈e es) eqn:E.
    +   assert (K: In (s,v) xs). {
            unfold xs. rewrite <- in_rev.
            apply ESet.to_list_in. unfold es'.
            apply ESet.filter_in; auto. 
            apply eqb_refl.
        }
        generalize dependent K.
        set (F := (fun y => _)).
        induction xs; intros K f' ac' H.
    ++  inversion K.
    ++  cbn in K, H. 
        destruct (fold_right F (EMap.empty, VSet.empty) xs) eqn:E1.
        cbn in K. destruct a. destruct K.
    +++ inv_clear H0. inv_clear H. cbn. rewrite E.
        rewrite EMap.FindReplaceEq. lra.
    +++ inv_clear H. cbn. rewrite E.
        eapply IHxs with (f':=t0) (ac':=t1) in H0; auto.
        unfold res_cap in H0.
        rewrite E in H0.
        destruct (Edge.equal (s,v) (v0,v1)).
        *   inv_clear e. rewrite EMap.FindReplaceEq. lra.   
        *   rewrite EMap.FindReplaceNeq; auto.
    +   set (F := (fun y => _)).
        assert (G : forall x, In x xs -> fst x = s). {
            intros. unfold xs in H. rewrite <- in_rev in H.
            apply ESet.to_list_in in H. unfold es' in H.
            eapply ESet.in_filter in H; auto.
            destruct x. destruct (equal s v0); subst; try lia.
            reflexivity. 
        }
        induction xs; intros f' ac' H.
    ++  cbn in H. inv_clear H. cbn. rewrite E.
        rewrite EMap.FindEmpty. lra.
    ++  cbn in  H.
        destruct (fold_right F (EMap.empty, VSet.empty) xs) eqn:E1.
        destruct a.
        assert ((t0, t1) = (t0, t1)) by reflexivity.
        apply IHxs in H0; auto.
    +++ cbn in H0 |- *.
        rewrite E in H0 |- *.
         cbn in H. inv_clear H.
        destruct (Edge.equal (v0, v1) (v, s)).
        *   exfalso. inv_clear e.
            apply L. erewrite <- (G (v, s)); eauto. constructor; auto.
        *   rewrite EMap.FindReplaceNeq; auto. 
    +++ intros. apply G. constructor 2; auto.
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
        forall f' l' tr', 
        gpr_trace fn = (Some (f',l'),tr') ->
        (forall n, ActiveNode fn f' n -> n=t \/ n=s) /\ 
        FlowConservationConstraint fn f'/\
        (VSet.size vs = NMap.find 0 l' s)%nat /\ (O=NMap.find 0 l' t)%nat.
    Proof.
        destruct fn as [[[[vs es] c] s] t]. 
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
    Qed.
End PR.

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

Module Edge := Tuple (Nat) (Nat).
Module EMap := Map (Edge).
Module VSet := MkSet (Nat).
Module ESet := MkSet (Edge).
Module NMap := Map (Nat).

Module PRNat := PR (Nat) (Edge) (EMap) (VSet) (ESet) (NMap).

Import ListNotations.
Open Scope nat.

Definition vset_list := fold_right VSet.add VSet.empty.
Definition eset_list := fold_right ESet.add ESet.empty.

(* Näited, et algoritm tagastab korrektse maksimaalse voo*)
Definition FN1 : PRNat.FlowNet := 
    let c := fun (x y: nat) => 10%Q in
    ((vset_list [0;1],eset_list[(0,1)]),c,0,1).

Compute (snd (PRNat.gpr_trace FN1)).

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

Compute (PRNat.gpr_trace FN2).

Compute (@PRNat.excess FN2 [(0, 1, 10%Q); (0, 3, 4%Q); (3, 4, 7%Q); (
    4, 1, 0%Q); (1, 2, 10%Q); (2, 5, 7%Q); (
    4, 5, 7%Q); (2, 3, 3%Q)] 5).


Definition FN3 : PRNat.FlowNet := 
    let c := fun (x y: nat) => 
        match x, y with
        | 0, 1 => 5%Q
        | 0, 2 => 3%Q
        | 1, 3 => 4%Q
        | 1, 4 => 3%Q
        | 2, 4 => 9%Q
        | 3, 5 => 20%Q
        | 4, 5 => 2%Q
        | _, _ => 0%Q
        end
    in
    (([0;1;2;3;4;5],[(0,1);(0,2);(1,3);(1,4);(2,4);(3,5);(4,5)]),c,0,5).

Compute (PRNat.gpr_trace FN3).
Compute (@PRNat.excess FN3 [(0, 1, 4%Q); (0, 2, 2%Q); 
(2, 4, 2%Q); (4, 5, 2%Q); (1, 3, 4%Q); (3, 5, 4%Q)] 5).
