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
Require Extraction.
Require Setoid.

(* Tõestamistaktikad *)

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

Ltac Qred_correct := repeat (let n := fresh in set (n:=Qred _); rewrite (Qred_correct); unfold n; clear n).


(* Geneeriline tüüp T, millega algoritm on tõestatud *)
    
Module Type T.
    Parameter V: Type.
    Parameter eqb: V -> V -> bool.
    Parameter equal: forall x y, reflect (x=y) (eqb x y).
    Lemma eqb_refl u: eqb u u = true.
    Proof. destruct (equal u u); auto. Qed. 
    Lemma eqb_neq u v: u<>v -> eqb u v = false.
    Proof. intros. destruct (equal u v); auto. contradiction. Qed. 
End T.

(* Naturaalarvude tüüp Nat, millega algoritmi praktiliselt kasutada saab.
    Sellega on algoritm ka ekstraheeritud. *)

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

(* Elementide mittekorduvus hulkades *)

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

(* Vastavuste (mappide) defineerimine
    Kasutusel andmestruktuurides EdgeMap, VertexMap ja ExcessMap. *)

Module Type MapSpec (T:T).
    Import T.
    (* Arvutamine *)
    Parameter t: forall (e:Type) {d:e}, Type.
    Parameter eq_nat: @t nat O -> @t nat O -> Prop.
    Parameter eq_rat: @t Q 0 -> @t Q 0 -> Prop.
    Parameter empty: forall {e:Type} (d:e), @t e d.
    Parameter replace: forall {e:Type} {d:e}, V -> e -> @t e d -> @t e d.
    Parameter find: forall {e:Type} (d:e), @t e d -> V -> e.
    Parameter update: forall {e:Type} {d:e}, V -> (e->e) -> @t e d -> @t e d. 
    Parameter remove: forall {e:Type} (d:e), V -> @t e d -> @t e d.
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
    
    Fixpoint eq_nat (map1: @t Datatypes.nat O) (map2: @t Datatypes.nat O) := 
        match map1, map2 with
        | nil, nil => True
        | nil, (_::map2') => False
        | (_::map1'), nil => False
        | ((k1,v1)::map1'), ((k2,v2)::map2') => 
            if (T.eqb k1 k2) && (v1 =? v2) then
                    eq_nat map1' map2'
            else
                False
        end.

    Fixpoint eq_rat (map1: @t Q 0) (map2: @t Q 0) := 
        match map1, map2 with
        | nil, nil => True
        | nil, (_::map2') => False
        | (_::map1'), nil => False
        | ((k1,v1)::map1'), ((k2,v2)::map2') => 
            if (T.eqb k1 k2) && (Qeq_bool v1 v2) then
                    eq_rat map1' map2'
            else
                False
        end.

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

    (* Tõestamine *)
    
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

(* Hulkade defineerimine. Kasutusel andmestruktuurides VertexSet ja EdgeSet. *)

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

(* Tipupaaride defineerimine *)

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

(* Algoritmi defineerimine ja tõestamine *)

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
    Declare Scope VertexMap.
    Declare Scope ExcessMap.
    Notation "m '[' v ']f'" := (EdgeMap.find 0 m v) (at level 12):EdgeMap.
    Notation "m '[' v ']l'" := (VertexMap.find O m v) (at level 12):VertexMap. 
    Notation "m '[' v ']e'" := (ExcessMap.find 0 m v) (at level 12):ExcessMap. 
    Local Open Scope EdgeMap.
    Local Open Scope VertexMap.
    Local Open Scope ExcessMap.
    

    Notation "v '∈v' s" := (VertexSet.mem v s) (at level 12). 

    Notation "v '∈e' s" := (EdgeSet.mem v s) (at level 12). 

    (* Graaf, mis koosneb tippude ja servade hulkadest*)
    Definition Graph := (VertexSet.t * EdgeSet.t)%type.

    (* Transpordivõrk kujul (Graaf, serva läbilaskevõime, algustipp, lõpptipp)*)
    Definition FlowNet := (Graph * (V -> V -> R) * V * V)%type.

    Definition nodes (fn:FlowNet) := 
        let '((vs, es),c,s,t) := fn in vs.

    (* sihttipp *)
    Definition sink (fn:FlowNet) := 
        let '((vs, es),c,s,t) := fn in t.        

    (* lähtetipp *)
    Definition source (fn:FlowNet) := 
        let '((vs, es),c,s,t) := fn in s.   

    (* Ratsionaalarvude jaoks vajalikud definitsioonid *)
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
    
    (* Arvutab transpordivõrgu fn, millel on eelvoog f, tipu x ülejäägi,
    lahutades väljaminevast voost maha sissetuleva voo. *)
    Definition excess (fn:FlowNet) (f: EdgeMap.t R) : V -> R :=
        let '((vs, es),c,s,t) := fn in
        fun u => 
        Qred (
            QSumList (map (fun v => f[(v,u)]f) (VertexSet.to_list vs)) -
            QSumList (map (fun v => f[(u,v)]f) (VertexSet.to_list vs))).

    (* Uuendab ülejääkide andmestruktuuri,
    vähendades tipu u ülejääki delta võrra ja suurendades tipu v ülejääki delta võrra *)
    Definition excess_update e u delta : V -> ExcessMap.t R :=
        fun v =>
            let new_map_u := @ExcessMap.update R 0 u (fun x => Qred (x - delta)) e in
            @ExcessMap.update R 0 v (fun x => Qred (x + delta)) new_map_u.

    (* Arvutab välja serva (u, v) alles oleva läbilaskevõime. 
    c u v tähistab serva läbilaskevõimet ja f[(u,v)]f serva voogu. 
    Tingimus (u,v) ∈e es tagastab tõeväärtuse true, siis kui serv (u, v) kuulub servade hulka es.
    Kui serv (u, v) ei kuulu servade hulka, siis tagastatakse voog, mis läheb tagurpidi ehk serva (v, u) voog.*)
    Definition res_cap (fn: FlowNet) (f: EdgeMap.t R) u v : R :=
        let '((vs, es),c,s,t) := fn in
        if (u,v) ∈e es then
            c u v - f[(u,v)]f
        else 
            f[(v,u)]f
    .

    Definition E (fn: FlowNet) (f: EdgeMap.t R) :=
        let '((vs, es),c,s,t) := fn in
        EdgeSet.filter (fun '(u, v) => f[(u,v)]f <? c u v) es.    
    
    (* Jääkvõrk *)
    Definition res_net (fn: FlowNet) (f: EdgeMap.t R) : FlowNet :=
        let '((vs, es),c,s,t) := fn in
        ((vs,E fn f),res_cap fn f,s,t).


    (* valib tipu u ülejäägist ning kaares (u,v) alles olevast läbilaskevõimest Qmin abil miinimumi 
     ja saadab selle voona edasi järgmisesse tippu v.
     Kui (u,v) ∈e es ehk serv (u, v) kuulub hulka es, siis suurendatakse serva (u, v) voogu delta võrra. 
     False korral vähendatakse serva (v, u) voogu delta võrra.
     Töö käigus uuendatakse ka tippude ülejääkide andmestruktuuri. *)
    Definition push fn f e u v : (EdgeMap.t R * ExcessMap.t R) :=
        let '((vs, es),c,s,t) := fn in
        let delta := Qmin (e[u]e) (res_cap fn f u v) in
        let new_excessmap := excess_update e u delta v in
        if (u,v) ∈e es  then
             ((EdgeMap.update (u,v) (fun x=> Qred (x+delta)) f), new_excessmap)
        else 
            ((EdgeMap.update (v,u) (fun x=> Qred(x-delta)) f), new_excessmap)
    .

    (* Leiab vähima kõrgusega tipu. *)
    Fixpoint smallest_rank l xs r :=
        match xs, r with
        | nil, _ => r
        | v::xs, None   => smallest_rank l xs (Some v)
        | v::xs, Some r => 
            if (l[r]l <=? l[v]l)%nat 
                then smallest_rank l xs (Some r)
                else smallest_rank l xs (Some v)
        end.

    (* Leiab sellised tipud v, mille korral on kaarel (u,v) veel läbilaskevõimet.
    Nende seast leiab vähima kõrgusega tipu. *)
    Definition relabel_find fn f (l: @VertexMap.t nat O) u vs := 
        let fvs := VertexSet.filter (fun v => 0 <? res_cap fn f u v) vs in
        smallest_rank l (VertexSet.to_list fvs) None.
    
    (* Otsib tipu u naabertippude seast kõige väiksema kõrgusega tipu v ja määrab tipu u kõrguseks 
    tipu v kõrgusest ühe võrra suurema arvu.
    Kui sobivat tippu ei leidu ehk saadakse väärtus None, siis relabel nurjub.
    See olukord aga algoritmi töö käigus kunagi ei realiseeru. *)
    Definition relabel fn f (l: @VertexMap.t nat O) u : option (VertexMap.t nat):=
        let '((vs, es),c,s,t) := fn in
        match relabel_find fn f l u vs with
        | None => None
        | Some v => Some (VertexMap.replace u (1+ l[v]l)%nat l)
        end.

    (* Otsib tippude hulgast vs' tippu v, kuhu voogu saata, kusjuures:
    - tipu v kõrgus peab olema tipu u kõrgusest ühe võrra väiksem;
    - kaarel (u,v) peab olema läbilaskevõimet. *)
    Definition find_push_node fn f (l: @VertexMap.t nat O) u (vs': VertexSet.t) :=
        let '((vs, es),c,s,t) := fn in
        VertexSet.find_first (fun v => 
            (l[u]l =? 1+ l[v]l)%nat &&
                (0 <? res_cap fn f u v)) vs'.

    (* Kontrollib, et antud tipp v ei oleks lähtetipp ega sihttipp ja tipu ülejääk oleks suurem kui 0. *)
    Definition has_excess_not_sink (fn: FlowNet) (e: ExcessMap.t R) v :=
        let '((_, _),_,s,t) := fn in
        if T.eqb v t || T.eqb v s then
            false
        else if 0 <? e[v]e then 
            true
        else
            false
    .

    (* Leiab transpordivõrgus maksimaalse voo. Selleks:
    - kontrollib piiraja g suurust (kui see on O, siis algoritm nurjub. 
        Korrektse sisendi puhul see juht ei realiseeru);
    - võimalusel sooritab push-sammu;
    - kui push ei ole võimalik, sooritab relabel-sammu;
    - kui relabel nurjub, siis lõpetab töö (see juht korrektse sisendi puhul ei realiseeru);
    - tagastab kaarte vood, tippude ülejäägid ja tippude kõrgused. *)
    Fixpoint gpr_helper fn f e l ac g: (option (EdgeMap.t R * ExcessMap.t R * VertexMap.t nat)) :=
        let '((vs, es),c,s,t) := fn in
        match g with
        | O => None
        | S g' => 
            match VertexSet.choice ac with
            | None => Some (f,e,l)
            | Some (u,ac') =>
            match find_push_node fn f l u vs with
            | Some v =>
                let (f',e') := push fn f e u v in
                let ac' := if 0 <? (ExcessMap.find (Qred 0) e' u) then ac else ac' in
                if has_excess_not_sink fn e' v then 
                    let ac'' := VertexSet.add v ac' in
                    gpr_helper fn f' e' l ac'' g' 
                else 
                    let ac'' := VertexSet.remove v ac' in
                    gpr_helper fn f' e' l ac'' g' 
            | None =>
                match relabel fn f l u with
                | None => None
                | Some l' =>
                    gpr_helper fn f e l' ac g' 
                end
            end
            end 
        end.
    
    Lemma gpr_helper_fn fn f e l ac g : 
        gpr_helper fn f e l ac g =
            let '((vs, es),c,s,t) := fn in
            match g with
            | O => None
            | S g' => 
                match VertexSet.choice ac with
                | None => (Some (f,e,l))
                | Some (u,ac') =>
                match find_push_node fn f l u vs with
                | Some v =>
                    let (f',e') := push fn f e u v in
                    let ac' := if 0 <? (ExcessMap.find (Qred 0) e' u) then ac else ac' in
                    if has_excess_not_sink fn e' v then 
                        let ac'' := VertexSet.add v ac' in
                        gpr_helper fn f' e' l ac'' g' 
                    else 
                        let ac'' := VertexSet.remove v ac' in
                        gpr_helper fn f' e' l ac'' g'
                | None =>
                    match relabel fn f l u with
                    | None => None
                    | Some l' =>
                        gpr_helper fn f e l' ac g'
                    end
                end
                end 
            end.
    Proof. destruct g; auto. Qed.

    (* Teeb initsialiseerimissammus ühe push-sammu. *)
    Definition initial_push_step fn '(f, e, ac) '(u, v) :=
        let '((_, es),c,s,t) := fn in
        let f' := @EdgeMap.update R 0 (u,v) (fun x=>Qred (x+c u v)) f in
        let e' := ExcessMap.update v (fun x=>Qred (x+c u v)) 
            (ExcessMap.update u (fun x=>Qred (x-c u v)) e) in
        let ac' := 
            if has_excess_not_sink fn e' v then 
                (VertexSet.add v ac) 
            else 
                ac 
        in
        (f', e', ac').

    (* Sooritab algoritmi initsialiseerimise, mille käigus saadetakse 
    lähtetipust mööda kõiki sealt väljuvaid kaari maksimaalne eelvoog. *)
    Definition initial_push fn: (EdgeMap.t R * ExcessMap.t R * VertexSet.t) :=
        let '((_, es),c,s,t) := fn in
        let es' := EdgeSet.to_list (EdgeSet.filter (fun '(u,v) => T.eqb s u) es) in
        let start_st := (EdgeMap.empty 0, ExcessMap.empty 0, VertexSet.empty) in
        fold_left (initial_push_step fn) es' start_st.

    (* Algväärtustab graafi, muutes tippude kõrgused nii, et tipp s on kõrgusega length vs 
    ja kõik teised tipud kõrgusega 0. 
    Seejärel teostab algse push-sammu tipust s väljuvate kaarte peal. 
    Lõpus kutsutakse välja gpr_helper, 
    mis leiab maksimaalse voo ja tagastab leitud väärtuse funktsioonile gpr.*)
    Definition gpr (fn:FlowNet): (option (EdgeMap.t R * ExcessMap.t R * VertexMap.t nat)) :=
        let '((vs, es),c,s,t) := fn in
        let vs_size := VertexSet.size vs in
        let labels := VertexMap.replace s vs_size (@VertexMap.empty nat O) in
        let bound := (EdgeSet.size es * vs_size * vs_size)%nat in
        let '(f, e, active) := initial_push fn in
        gpr_helper fn f e labels active bound.

    (* Algoritmi sammud. Vajalik vaid funktsioonides, mis tagastavad järjendi list Tr. *)
    Inductive Tr : Type :=
        | Init: @EdgeMap.t R 0 -> @ExcessMap.t R 0 -> @VertexMap.t nat O -> VertexSet.t ->  Tr
        | Push: V -> V -> @EdgeMap.t R 0 -> @ExcessMap.t R 0 -> VertexSet.t ->  Tr
        | Relabel : V -> nat -> @VertexMap.t nat O ->  Tr
        | OutOfGas
        | RelabelFailed
        .

    (* Sama funktsioon kui gpr_helper, aga tagastab ka listi tehtud operatsioonidest
    algoritmi töö kontrolliks. *)
    Fixpoint gpr_helper_trace fn f e l ac g tr: (option (EdgeMap.t R * ExcessMap.t R * VertexMap.t nat)*list Tr) :=
        let '((vs, es),c,s,t) := fn in
        match g with
        | O => (None, OutOfGas::tr)
        | S g' => 
            match VertexSet.choice ac with
            | None => (Some (f,e,l),tr)
            | Some (u,ac') =>
            match find_push_node fn f l u vs with
            | Some v =>
                let (f',e') := push fn f e u v in
                let ac' := if 0 <? (e'[u]e) then ac else ac' in
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
                    gpr_helper_trace fn f e l' ac g' (Relabel u (l'[u]l)%nat l'::tr)
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
                | None => (Some (f,e,l),tr)
                | Some (u,ac') =>
                match find_push_node fn f l u vs with
                | Some v =>
                    let (f',e') := push fn f e u v in
                    let ac' := if 0 <? (e'[u]e) then ac else ac' in
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
                        gpr_helper_trace fn f e l' ac g' (Relabel u (l'[u]l)%nat l'::tr)
                    end
                end
                end 
            end.
    Proof. destruct g; auto. Qed. 

    (* Sama funktsioon kui gpr, aga tagastab lisaks ka järjendi tehtud operatsioonidest. *)
    (* Annab ülevaate täpsest algoritmi tööst. *)
    Definition gpr_trace (fn:FlowNet): (option (EdgeMap.t R * ExcessMap.t R * VertexMap.t nat)*list Tr) :=
        let '((vs, es),c,s,t) := fn in
        let vs_size := VertexSet.size vs in
        let labels := VertexMap.replace s vs_size (@VertexMap.empty nat O) in
        let bound := (EdgeSet.size es * vs_size * vs_size)%nat in
        let '(f, e, active) := initial_push fn in
        gpr_helper_trace fn f e labels active bound (Init f e labels active :: nil).

    (* Nii gpr kui gpr_trace tagastavad samad vood, ülejäägid ja kõrgused. *)
    Lemma gpr_trace_eq_gpr: forall fn,
    match gpr fn, gpr_trace fn with
    | None, (None,_) => True
    | Some (f,e,l), (None,_) => False 
    | None, (Some (f',e',l'), _) => False
    | Some (f,e,l), (Some (f',e',l'), _) =>
        EdgeMap.eq_rat f f' /\ ExcessMap.eq_rat e e' /\ VertexMap.eq_nat l l'
    end.
    Proof. Admitted.

    (* Iga kaare voog ei ole suurem selle läbilaskevõimest. *)
    Definition CapacityConstraint (fn:FlowNet) (f: @EdgeMap.t R 0) := 
        let '((vs, es),c,s,t) := fn in
        forall u v, EdgeSet.mem (u,v) es = true -> 
            f[(u,v)]f <= c u v.
    

    (* ExcessMapis on õige ülejääk *)
    Definition ExcessCached (fn:FlowNet) (f:EdgeMap.t Q) (e: ExcessMap.t R) := 
        let '((vs, es),c,s,t) := fn in
        forall v, excess fn f v = ExcessMap.find (Qred 0) e v.


    (* Tagastab true, kui igas tipus v, mis ei ole sisend, on ülejääk mittenegatiivne. *)
    Definition NonDeficientFlowConstraint (fn:FlowNet) (f: @EdgeMap.t R 0) := 
        let '((vs, es),c,s,t) := fn in
        forall v, (v ∈v vs) = true -> v<>s -> 0 <= excess fn f v.

    (* Tagastab true kui igas tipus v.a sisendis ja väljundis on ülejääk 0 
    ehk kontrollib voo säilivuse tingimust.  *)
    Definition FlowConservationConstraint (fn:FlowNet) (f: @EdgeMap.t R 0) (e:ExcessMap.t R) := 
        let '((vs, es),c,s,t) := fn in
        forall v, (v ∈v vs) = true -> v<>s -> v<>t -> e[v]e == 0.

    (* Tagastab true kui on täidetud eelvoo nõuded *)
    Definition PreFlowCond (fn:FlowNet) (f: @EdgeMap.t R 0) := 
            CapacityConstraint fn f /\ NonDeficientFlowConstraint fn f. 

    (* Tagastab true kui voog ja läbilaskevõime on mittenegatiivsed *)
    Definition FlowMapPositiveConstraint (fn:FlowNet) (f: @EdgeMap.t R 0) := 
        let '((vs, es),c,s,t) := fn in
        forall u v, f[(u,v)]f >= 0 /\ c u v >= 0.
    
    (* Tagastab true, kui tipp v on tippude hulgas ja omab ülejääki *)
    Definition ActiveNode (fn:FlowNet) (f: @EdgeMap.t R 0) v := 
        let '((vs, es),c,s,t) := fn in
        (v ∈v vs) = true /\ excess fn f v > 0.

    (* Tagastab true, kui iga tipu u ja v korral, kui serv (u ,v) kuulub servade hulka on tippudel u ja v korrektsed kõrgused *)
    Definition ValidLabeling  fn (f: @EdgeMap.t R 0) (l: @VertexMap.t nat O) :=
        forall u v,
        let '((vs, es),c,s,t) := fn in
        ((u,v) ∈e E fn f) = true  ->  (l[u]l <= l[v]l + 1)%nat.

    (* Tagastab true, kui iga tipu u ja v korral,
    kus kaarel (u,v) on läbilaskevõimet alles, kehtib l(u) <= l(v) + 1 *)
    Definition NoSteepArc (fn:FlowNet) (f: @EdgeMap.t R 0) (l: @VertexMap.t nat O):=
        forall u v,
        res_cap fn f u v > 0 -> (l[u]l <= l[v]l+1)%nat.

    (* Tagastab true iga tipu u ja v korral kui on täidetud tingimus c u v - f(u,v) > 0
    ja tipud u ja v kuuluvad transpordivõrku *)
    Definition ResCapNodes (fn:FlowNet) (f: @EdgeMap.t R 0) :=
            forall u v,
            res_cap fn f u v > 0 -> u ∈v (nodes fn) = true /\ v ∈v (nodes fn) = true.

    (* Tagastab true, kui push sammu eeldused on täidetud, ehk tipus on ülejääk ja järgmise tipu kõrgus on 1 võrra väiksem. *)
    Definition PushCondition (fn: FlowNet) (f: @EdgeMap.t R 0) (l: @VertexMap.t nat O) u v := 
        excess fn f u > 0 /\ (l[u]l = l[v]l + 1)%nat.
    
    (* Kui tippudel olid korrektsed kõrgused enne push sammu, siis ka peale push sammu on tippudel korrektsed kõrgused *)
    Lemma PushValidLabel fn (f: @EdgeMap.t R 0) (e:ExcessMap.t R) (l: @VertexMap.t nat O) x y:
        let '((vs, es),c,s,t) := fn in
        ExcessCached fn f e ->
        ValidLabeling fn f l -> PushCondition fn f l x y
                -> ValidLabeling fn (fst (push fn f e x y)) l.
    Proof.
        intros. destruct fn as [[[[vs es] c] s] t]. unfold ValidLabeling, PushCondition, ExcessCached. 
        intros Hex H H0 u v H1. unfold push in H1.
        repeat rewrite <- Hex in H1. 
        destruct ((x, y) ∈e es) eqn : E.
        + unfold PR.E, fst in *. apply EdgeSet.in_filter in H1. destruct H1.  
        apply H. apply EdgeSet.filter_in.
        - auto.
        - destruct (Edge.equal (x,y) (u, v)).
        * inversion e0. subst. rewrite EdgeMap.FindUpdateEq in H2. 
        eapply (reflect_iff _ _ (QLt_spec _ _)). 
        eapply (reflect_iff _ _ (QLt_spec _ _)) in H2.
        unfold res_cap in H2. rewrite E in H2.
        destruct ( Q.min_dec (excess (vs, es, c, s, t) f u) (c u v - f[(u, v)]f)).
        ** rewrite q in H2. rewrite Qred_correct in *. rewrite Hex in H2. destruct H0. rewrite Hex in H0. lra.
        ** rewrite q in H2. unfold R in H2. 
            rewrite Qred_correct in *. lra.
        * rewrite EdgeMap.FindUpdateNeq in H2; auto.
        + unfold PR.E, fst in *. apply EdgeSet.in_filter in H1. destruct H1.
        destruct (Edge.equal (y, x) (u, v)).
        - inversion e0. subst. lia.
        - rewrite EdgeMap.FindUpdateNeq in H2; auto.
        apply H. apply EdgeSet.filter_in; auto.
        Qed.

    (* Tagastab true, kui tingimustest, et tipu u ülejääk on positiivne,
        v on tipp ja kaarel (u,v) on veel läbilaskevõimet, järeldub, et
        u kõrgus ei ole suurem v kõrgusest. *)
    Definition RelabelCondition fn (f: @EdgeMap.t R 0) (l: @VertexMap.t nat O) u := 
      excess fn f u > 0 /\ forall v, v ∈v (nodes fn) = true -> 
      res_cap fn f u v > 0 -> (l[u]l <= l[v]l)%nat.

    Lemma smallest_rank_In: forall l xs r v,
        smallest_rank l xs (Some r) = Some v -> In v (r::xs).
    Proof.
        intros l xs. induction xs; cbn; intros; auto.
        +   inv_clear H. tauto.
        +   destruct (l[r]l <=? l[a]l)%nat.
        ++  apply IHxs in H. cbn in H. tauto.
        ++  apply IHxs in H. cbn in H. tauto.   
    Qed.

    Lemma smaller_rank_leq: forall l xs v0 v v' ,
        smallest_rank l xs (Some v0) = Some v ->
        (In v' xs \/ (l[v0]l <= l[v']l)%nat) ->
        (l[v]l <= l[v']l)%nat.
    Proof.
        intros l xs. induction xs; intros v0 v v' Hs H; cbn in *.
        +   inv_clear Hs. destruct H; auto. inv_clear H.
        +  destruct (Nat.leb_spec0 (l[v0]l)%nat (l[a]l)%nat).
        ++  eapply IHxs with (v':=v')in Hs; auto.
            destruct H; try lia. 
            destruct H; subst; try lia.
            tauto.
        ++  eapply IHxs with (v':=v')in Hs; auto.
            destruct H; try lia. 
            destruct H; subst; try lia.
            tauto.
    Qed.

    (* Kui relabel_find tipus u tagastab tipu v ja kaarel (u,v) on läbilaskevõimet,
    siis iga tipp v', kus kaarel (u,v') on läbilaskevõimet, ei ole väiksema kõrgusega kui v. *)
    Lemma RFindCondition fn (f: @EdgeMap.t R 0) (l: @VertexMap.t nat O) u vs: forall v, 
      relabel_find fn f l u vs = Some v  ->
      (0 <? res_cap fn f u v) = true /\ (forall v', (v' ∈v vs) = true 
        -> (0 <? res_cap fn f u v') = true -> (l[v]l <= l[v']l)%nat).
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
                destruct ((l[v']l <=? l[a]l)%nat) eqn:E.
            **  apply IHl0, H.
            **  destruct (Nat.leb_spec0 (l[v']l)%nat (l[a]l)%nat);
                [inversion E|].
                specialize (IHl0 _ H). lia.
        +++ eapply smaller_rank_leq; eauto.
    Qed.

    (* relabel_find tagastab transpordivõrgus eksisteeriva tipu *)
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

    (* Kui enne relabel sammu olid tippudel korrektsed kõrgused,
    siis peale relabel sammu on samuti tippudel korrektsed kõrgused *)
    Lemma RelabelValidLabel fn (f: @EdgeMap.t R 0) (l: @VertexMap.t nat O) x l':
        let '((vs, es),c,s,t) := fn in
        (forall u v , ((u, v) ∈e es = true) -> (u ∈v vs) = true /\ (v ∈v vs) = true) ->
        ValidLabeling fn f l -> RelabelCondition fn f l x 
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
        - assert ((l[v0]l) <= l[v]l)%nat. { apply H5. + edestruct R; eauto. + unfold res_cap.
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

    (* Kui tippudel on korrektsed kõrgused ning leidub aktiivseid tippe
    ja leidub tipp kuhu saab push sammu teha, siis järeldub, et 
    push sammu eeldused on täidetud. *)
    Lemma FPNCondition fn f l u vs': 
        (u ∈v nodes fn) = true -> forall v, 
        ValidLabeling fn f l -> ActiveNode fn f u ->
        find_push_node fn f l u vs' = Some v -> PushCondition fn f l u v.
    Proof.
        unfold PushCondition, ValidLabeling, ActiveNode. intros. 
        destruct fn as [[[[vs es] c] s] t]. split.
        + apply H1; apply H.
        +   unfold find_push_node in H2.
            apply VertexSet.find_first_specSome in H2.
            destruct H2. apply andb_true_iff in H2.
            destruct H2. 
            destruct (Nat.eqb_spec (l[u]l)%nat (1 + l[v]l)); [|inversion H2]. 
            lia.
    Qed.

    Lemma map_fn A B (f:A->B) x xs : map f (x::xs) =  f x :: map f xs.
    Proof. reflexivity. Qed.

    (* Eeldusel, et kaar (s,v0) on erinev kaarest (u,v) iga v0 puhul, siis
    pole vahet, kas suurendada kaare (u,v) voogu d võrra või mitte,
    tipust s väljuvate kaarte voogude summa on sama. *)
    Lemma SumSame (f: @EdgeMap.t R 0) (s:V->V*V) vs u v d : 
        (forall v0,  In v0 vs -> s v0 <> (u, v)) ->
        map (fun v0 => EdgeMap.find 0 
            (EdgeMap.update (u, v) (fun x0 => Qred (x0 + d)) f) 
            (s v0)) vs = 
        map (fun v0 => f[(s v0)]f) vs.
    Proof.
        induction vs; intros.
        + simpl. auto.
        +   do 2 rewrite map_fn.
            erewrite IHvs.
        ++  f_equal. erewrite EdgeMap.FindUpdateNeq; auto.
            apply H. cbn. auto.
        ++  intros. apply H. constructor 2. auto.
    Qed.

    (* Kui tipp x on aktiivne enne push-sammu tipust u tippu v, siis on tipp x aktiivne ka pärast seda. *)
    Lemma PushActiveCondition (fn:FlowNet) (f:EdgeMap.t R) (e:ExcessMap.t R) u v x: 
        ActiveNode fn f x -> x<>v -> x<>u -> ActiveNode fn (fst (push fn f e u v)) x .
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

    (* Tipu u ülejääk ja kaare (u,v) alles olev läbilaskevõime on
    mittenegatiivsed. *)
    Lemma DeltaPositive fn (f: @EdgeMap.t R 0) (l: @VertexMap.t nat O) u v:
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

    (* Eeldustel, et ülejäägid on õigesti salvestatud, voog ja läbilaskevõime on mittenegatiivsed,
    eelvoo tingimused on täidetud ja push-sammu eeltingimused on täidetud, siis
    on voog ja läbilaskevõime mittenegatiivsed ka pärast push-sammu. *)
    Lemma PushFlowMapPos fn (f: @EdgeMap.t R 0) (e:ExcessMap.t R) (l: @VertexMap.t nat O) x y:
        let '((vs, es),c,s,t) := fn in
        (x ∈v vs) = true ->
        ExcessCached fn f e ->
        FlowMapPositiveConstraint fn f -> 
        PreFlowCond fn f ->
        PushCondition fn f l x y ->
        FlowMapPositiveConstraint fn (fst (push fn f e x y)).
    Proof.
        unfold FlowMapPositiveConstraint, PreFlowCond, PushCondition.
        unfold CapacityConstraint, NonDeficientFlowConstraint, ExcessCached.
        destruct fn as [[[[vs es] c] s] t]. 
        intros H Hex H0 H1 H2 u v. split.
        + unfold push. repeat rewrite <- Hex.
         destruct ((x, y) ∈e es) eqn : E.
        - destruct (Edge.equal (x,y) (u,v)).
        * inv_clear e0. unfold fst. rewrite EdgeMap.FindUpdateEq.
        eapply (DeltaPositive ((vs, es),c,s,t) f l u v) in H; auto.
        specialize (H0 u v). rewrite Qred_correct. lra.
        * unfold fst. rewrite EdgeMap.FindUpdateNeq; auto.
        apply H0.
        - destruct (Edge.equal (y,x) (u,v)).
        * inv_clear e0. unfold fst. rewrite EdgeMap.FindUpdateEq.
        unfold res_cap. rewrite E. edestruct (Q.min_spec_le); destruct H3.
        ** erewrite H4. unfold R in *. rewrite Qred_correct. lra.
        ** erewrite H4. unfold R in *. rewrite Qred_correct. lra.
        * unfold fst. rewrite EdgeMap.FindUpdateNeq; auto.
            apply H0.
            + apply H0.
    Qed.   

    Lemma QSumListFn x xs: QSumList (x::xs) = x + QSumList xs.
    Proof. reflexivity. Qed.

    Lemma SumInR (f: @EdgeMap.t R 0 ) vs u v d : 
        Distinct vs ->
        In u vs ->
        QSumList (
            map (fun v0 => EdgeMap.find 0
                  (EdgeMap.update (u, v) (fun x0 => Qred (x0 + d)) f) 
                  (v0, v)) vs) == 
        QSumList (map (fun v0 => f[(v0, v)]f) vs) + d.
    Proof. 
         induction vs; intros.
        + simpl. inversion H0.
        + do 2 rewrite map_fn. destruct (equal u a).
        - subst. rewrite EdgeMap.FindUpdateEq. erewrite SumSame.
        *   do 2 rewrite QSumListFn.
            unfold R in *. rewrite Qred_correct. lra.
        * intros. intro C. inv_clear C. inv_clear H. tauto. 
        - rewrite EdgeMap.FindUpdateNeq.
        * do 2 rewrite QSumListFn. erewrite IHvs.
        ** lra.
        ** inversion H. auto.
        **  simpl in H0.
            destruct H0; subst; try tauto.
        * intro C. inv_clear C. apply n. reflexivity.
    Qed. 

    Lemma SumInL (f: @EdgeMap.t R 0) vs: forall u v d,
        Distinct vs ->
        In v vs ->
        QSumList (
            map (fun v0 => EdgeMap.find 0 
                  (EdgeMap.update (u, v) (fun x0 => Qred (x0 + d)) f) 
                  (u,v0)) vs) == 
        QSumList (map (fun v0 =>
        f[(u, v0)]f) vs) + d.
    Proof.
        induction vs; intros.
        + simpl. inversion H0.
        + do 2 rewrite map_fn. destruct (equal v a).
        - subst. rewrite EdgeMap.FindUpdateEq. erewrite SumSame.
        *   do 2 rewrite QSumListFn.
            unfold R in *. rewrite Qred_correct. lra.
        * intros. intro C. inv_clear C. inv_clear H. tauto. 
        - rewrite EdgeMap.FindUpdateNeq.
        * do 2 rewrite QSumListFn. erewrite IHvs.
        ** lra.
        ** inversion H. auto.
        **  simpl in H0.
            destruct H0; subst; try tauto.
        * intro C. inv_clear C. apply n. reflexivity.
    Qed.

    Lemma SumNoUpdateL: forall f vs v t c s, s <> v ->
        QSumList (map (fun v0 : V =>
        EdgeMap.find 0 (EdgeMap.update (v, t) c f) (s,v0)) vs) =
        QSumList (map (fun v0 : V => f[(s, v0)]f) vs).
    Proof.
        intros f vs. induction vs; intros; cbn; auto.
        assert ((s, a) <> (v, t)). { 
            intro q. inv_clear q. tauto. 
        }
        rewrite EdgeMap.FindUpdateNeq; auto.
        eapply (IHvs v t c) in H. rewrite H. 
        reflexivity.
    Qed.

    Lemma SumNoUpdateR: forall f vs v t c s, t <> v ->
        QSumList (map (fun v0 : V =>
        EdgeMap.find 0 (EdgeMap.update (s, v) c f) (v0, t)) vs) =
        QSumList (map (fun v0 : V => f[(v0, t)]f) vs).
    Proof.
        intros f vs. induction vs; intros; cbn; auto.
        assert ((a, t) <> (s, v)). { 
            intro q. inv_clear q. tauto. 
        }
        rewrite EdgeMap.FindUpdateNeq; auto.
        eapply (IHvs v t c) in H. rewrite H. 
        reflexivity.
    Qed.

    (* Kui on rahuldatud eelvoo tingimused ning vood ja läbilaskevõimed on mittenegatiivsed 
    ja leidub tipp, kuhu saab push sammu teha, siis järeldub, et ka peale push sammu on eelvoo tingimused säilitatud *)
    Lemma PushPreFlow fn (f: @EdgeMap.t R 0) (e:ExcessMap.t R) (l: @VertexMap.t nat O) x y:
        let '((vs, es),c,s,t) := fn in
        (x ∈v vs) = true ->
        (y ∈v vs) = true ->
        ExcessCached fn f e ->
        PreFlowCond fn f -> 
        FlowMapPositiveConstraint fn f ->
        PushCondition fn f l x y ->
        PreFlowCond fn (fst (push fn f e x y)).
    Proof. 
        unfold PreFlowCond, FlowMapPositiveConstraint, PushCondition, PreFlowCond, ExcessCached.
        unfold CapacityConstraint, NonDeficientFlowConstraint.
        destruct fn as [[[[vs es] c] s] t].
        intros Hxvs Hyvs Hex [Hcc Hndf] Hfmp Hpc.
        split.
        + intros. unfold push.
        repeat rewrite <- Hex. destruct ((x, y) ∈e es) eqn : E.
        - destruct (Edge.equal (x,y) (u,v)). 
        * inv_clear e0. unfold fst. rewrite EdgeMap.FindUpdateEq. unfold res_cap.
        rewrite E. edestruct (Q.min_spec_le); destruct H0.
        ** erewrite H1. unfold R in *. rewrite Qred_correct. lra.
        ** erewrite H1. unfold R in *. rewrite Qred_correct. lra.
        * unfold fst. rewrite EdgeMap.FindUpdateNeq; auto.
        - unfold res_cap. rewrite E. destruct (Edge.equal (y,x) (u,v)).
        * inv_clear e0. unfold fst. rewrite EdgeMap.FindUpdateEq. edestruct (Q.min_spec_le); destruct H0.
        ** erewrite H1. specialize (Hcc _ _ H). 
            rewrite Qred_correct. lra.
        ** rewrite H1. specialize (Hfmp u v). unfold R in *. 
            rewrite Qred_correct. lra.
        * unfold fst. rewrite EdgeMap.FindUpdateNeq; auto.
        +   intros. 
            pose proof (L1:=VertexSet.to_list_distinct vs).
            apply VertexSet.to_list_in in H as L2.
            apply VertexSet.to_list_in in Hxvs as L3.
            apply VertexSet.to_list_in in Hyvs as L4.
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

    (* find_push_node tagastab alati transpordivõrgus eksisteeriva tipu *)
    Lemma FPNinVs fn f l u v vs': 
    find_push_node fn f l u vs' = Some v -> (v ∈v vs') = true.
    Proof.
        destruct fn as [[[[vs es] c] s] t]. intros H. 
        unfold find_push_node in H. apply VertexSet.find_first_specSome in H as [_ H].
        auto.
    Qed.

    (* has_excess_not_sink tagastab true vaid siis, kui selle argumendiks antud tipu
    ülejääk on positiivne, see pole lähte- ega sihttipp. *)
    Lemma HENSCondition fn v :forall (f: @EdgeMap.t R 0) (e:ExcessMap.t R),
        has_excess_not_sink fn e v = true -> 0 < e[v]e /\ v <> sink fn /\ v <> source fn.
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

    (* Eeldusel, et u ja v on tipud ning x on neist erinev, ülejäägid on õigesti salvestatud,
    eelvoo tingimused on täidetud, voog ja läbilaskevõime on mittenegatiivsed,
    push-sammu tingimused on täidetud ja x on aktiivne tipp pärast push(u,v)-sammu, 
    siis x oli aktiivne tipp ka enne push-sammu. *)
    Lemma PushActiveInv (fn:FlowNet) (f:EdgeMap.t R) (e:ExcessMap.t R) (l: @VertexMap.t nat O) u v x:
        u ∈v nodes fn = true ->
        v ∈v nodes fn = true ->
        x<>v ->
        ExcessCached fn f e ->
        PreFlowCond fn f ->
        FlowMapPositiveConstraint fn f ->
        PushCondition fn f l u v ->
        ActiveNode fn (fst (push fn f e u v)) x ->
        ActiveNode fn f x.
    Proof.
        unfold ActiveNode, push, PreFlowCond, 
        FlowConservationConstraint, PushCondition, ExcessCached.
        destruct fn as [[[[vs es] c] s] t].
        pose proof (H:= True).
        intros H0 H1 H2 Hex H3 H4 H5 H6.
        repeat rewrite <- Hex in H6.
        cbn in H0, H1.
        pose proof (L1:=VertexSet.to_list_distinct vs).
        apply VertexSet.to_list_in in H0 as L2.
        apply VertexSet.to_list_in in H1 as L3.
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
    
    (* kui find_push_node ei leia tippu, kuhu tipust u voogu suunata, siis 
    on iga tipust u väljuva kaare läbilaskevõime ära kasutatud või ei leidu
    tipu u kõrgusest ühe võrra madalamat naabertippu. *)
    Lemma FPNConditionNone fn f l u vs': 
        find_push_node fn f l u vs' = None -> 
        forall v, v ∈v vs' = true -> (0 <? res_cap fn f u v = false) 
        \/ (l[u]l <> l[v]l + 1)%nat.
    Proof.
        destruct fn as [[[[vs es] c] s] t].
        intros H v Hvs. 
        unfold find_push_node in H.
        eapply VertexSet.find_first_specNone in H; eauto.
        apply andb_false_iff in H. destruct H; try tauto.
        destruct (Nat.eqb_spec (l[u]l)%nat (1 + l[v]l)); lia.
    Qed. 

    Lemma HENSConditionFalse fn v :forall (f: @EdgeMap.t R 0) (e:ExcessMap.t R),
        has_excess_not_sink fn e v = false -> 0 >= e[v]e \/ v = sink fn \/ v = source fn.
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

    (* Pärast push-sammu ei teki kaari (u,v), 
    kus u on kõrgemal kui l(v)+1 ja (u,v) läbilaskevõime pole ära kasutatud. *)
    Lemma PushNoSteepArc fn f e l x y:
        (x ∈v nodes fn) = true -> 
        FlowMapPositiveConstraint fn f ->
        PreFlowCond fn f -> 
        PushCondition fn f l x y ->
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

    (* Kui enne push-sammu kehtib c x y >= f(x,y),
    siis kehtib see ka pärast push-sammu. *)
    Lemma PushResCapNodes fn f e x y:
        x ∈v (nodes fn) = true -> y ∈v (nodes fn) = true ->
        ExcessCached fn f e ->
        ResCapNodes fn f -> ResCapNodes fn (fst (push fn f e x y)).
    Proof.
        unfold ResCapNodes, ExcessCached.
        intros H H0 Hex H1 u v H2. 
        unfold push, fst in H2. destruct fn as [[[[vs es] c] s] t].
        repeat rewrite <- Hex in H2.
        set (d:= Qmin _ _) in H2. destruct ((x, y) ∈e es) eqn : E.
        + unfold res_cap in H2. destruct ((u, v) ∈e es) eqn : E2.
        - destruct (Edge.equal (u, v) (x, y)).
        * inv_clear e0. tauto.
        * rewrite EdgeMap.FindUpdateNeq in H2; auto.
        apply H1. unfold res_cap. rewrite E2. auto.
        -  destruct (Edge.equal (v, u) (x, y)).
        * inv_clear e0. tauto.
        * rewrite EdgeMap.FindUpdateNeq in H2; auto.
        apply H1. unfold res_cap. rewrite E2. auto.
        + unfold res_cap in H2. destruct ((u, v) ∈e es) eqn : E2.
        - destruct (Edge.equal (u, v) (y, x)).
        * inv_clear e0. tauto.
        * rewrite EdgeMap.FindUpdateNeq in H2; auto.
        apply H1. unfold res_cap. rewrite E2. auto.
        - destruct (Edge.equal (v, u) (y, x)).
        * inv_clear e0. tauto.
        * rewrite EdgeMap.FindUpdateNeq in H2; auto.
        apply H1. unfold res_cap. rewrite E2. auto.
    Qed.

    Definition excess_loop f u xs := 
        QSumList (map (fun v => f[(v, u)]f) xs) -
            QSumList (map (fun v => f[(u, v)]f) xs) .

    (* Kui silmuse voogu suurendada, siis ei muutu tippu
    sisenevate ja väljuvate kaarte voogude summade vahe. *)
    Lemma PushExcessCycle f xs x d z:
        excess_loop (EdgeMap.update (x,x) (fun x=> Qred (x+d)) f) z xs == excess_loop f z xs .
    Proof.
        destruct (equal x z); subst.
        +   unfold excess_loop.
            induction xs.
        ++  cbn. lra.
        ++  repeat rewrite map_fn.
            repeat rewrite QSumListFn. 
            destruct (equal a z); subst.
        +++ repeat rewrite EdgeMap.FindUpdateEq. lra.  
        +++ rewrite EdgeMap.FindUpdateNeq; [|intro C; inv_clear C; contradiction].
            rewrite EdgeMap.FindUpdateNeq; [|intro C; inv_clear C; contradiction].
            lra.
        +   unfold excess_loop.
            induction xs.
        ++  cbn. lra.
        ++  repeat rewrite map_fn.
            repeat rewrite QSumListFn. 
            rewrite EdgeMap.FindUpdateNeq; [|intro C; inv_clear C; contradiction].
            rewrite EdgeMap.FindUpdateNeq; [|intro C; inv_clear C; contradiction].
            lra.
    Qed.

    (* Pärast push sammu on pushi teise tipu ülejääk delta võrra suurem. *)
    Lemma PushExcessIn f xs x y d:
        x<>y ->
        Distinct xs ->
        (In x xs /\ excess_loop (EdgeMap.update (x,y) (fun x=> Qred (x+d)) f) y xs == excess_loop f y xs + d) \/
        (~In x xs /\ excess_loop (EdgeMap.update (x,y) (fun x=> Qred (x+d)) f) y xs == excess_loop f y xs) .
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
        +++ rewrite EdgeMap.FindUpdateNeq;
            [|intros C; inv_clear C; contradiction].
            set (r1 := QSumList _) in IH |- *.
            set (r2 := QSumList _) in IH |- *.
            set (r3 := QSumList _) in IH |- *.
            set (r4 := QSumList _) in IH |- *.
            set (r5 := EdgeMap.find _ _ _) in IH |- *.            
            lra.
        +++ rewrite EdgeMap.FindUpdateNeq;
            [|intros C; inv_clear C; contradiction].
            rewrite EdgeMap.FindUpdateNeq;
            [|intros C; inv_clear C; contradiction].
            set (r1 := QSumList _) in IH |- *.
            set (r2 := QSumList _) in IH |- *.
            set (r3 := QSumList _) in IH |- *.
            set (r4 := QSumList _) in IH |- *.
            set (r5 := EdgeMap.find _ _ _) in IH |- *.            
            lra.
        ++  destruct (equal x a); subst.
        +++ left. split; [cbn;auto|].
            do 4 (rewrite map_fn; rewrite QSumListFn).
            repeat rewrite EdgeMap.FindUpdateEq.
            repeat rewrite EdgeMap.FindUpdateNeq; 
            [|intros C; inv_clear C; contradiction].
            set (r1 := QSumList _) in IH |- *.
            set (r2 := QSumList _) in IH |- *.
            set (r3 := QSumList _) in IH |- *.
            set (r4 := QSumList _) in IH |- *.
            set (r5 := EdgeMap.find _ _ _) in IH |- *.            
            set (r6 := EdgeMap.find _ _ _) in IH |- *.
            rewrite Qred_correct.    
            lra.
        +++ destruct (equal y a); subst.
            *   right. split; [intros C; inv_clear C; contradiction|].
                do 4 (rewrite map_fn; rewrite QSumListFn).
                repeat rewrite EdgeMap.FindUpdateEq.
                rewrite EdgeMap.FindUpdateNeq; 
                [|intros C; inv_clear C; contradiction].
                set (r1 := QSumList _) in IH |- *.
                set (r2 := QSumList _) in IH |- *.
                set (r3 := QSumList _) in IH |- *.
                set (r4 := QSumList _) in IH |- *.
                set (r5 := EdgeMap.find _ _ _) in IH |- *.            
                lra.
            *   right. split; [intros C; inv_clear C; contradiction|].
                do 4 (rewrite map_fn; rewrite QSumListFn).
                repeat rewrite EdgeMap.FindUpdateEq.
                repeat (rewrite EdgeMap.FindUpdateNeq; 
                [|intros C; inv_clear C; contradiction]).
                set (r1 := QSumList _) in IH |- *.
                set (r2 := QSumList _) in IH |- *.
                set (r3 := QSumList _) in IH |- *.
                set (r4 := QSumList _) in IH |- *.
                set (r5 := EdgeMap.find _ _ _) in IH |- *.            
                lra.
    Qed.

    (* Pärast push sammu on pushi esimese tipu ülejääk delta võrra väiksem. *)
    Lemma PushExcessOut f xs x y d:
        x<>y ->
        Distinct xs ->
        (In y xs /\ excess_loop (EdgeMap.update (x,y) (fun x=> Qred (x+d)) f) x xs == excess_loop f x xs - d) \/
        (~In y xs /\ excess_loop (EdgeMap.update (x,y) (fun x=> Qred (x+d)) f) x xs == excess_loop f x xs ) .
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
        +++ rewrite EdgeMap.FindUpdateNeq;
            [|intros C; inv_clear C; contradiction].
            set (r1 := QSumList _) in IH |- *.
            set (r2 := QSumList _) in IH |- *.
            set (r3 := QSumList _) in IH |- *.
            set (r4 := QSumList _) in IH |- *.
            set (r5 := EdgeMap.find _ _ _) in IH |- *.                           
            lra.
        +++ rewrite EdgeMap.FindUpdateNeq;
            [|intros C; inv_clear C; contradiction].
            rewrite EdgeMap.FindUpdateNeq;
            [|intros C; inv_clear C; contradiction].
            set (r1 := QSumList _) in IH |- *.
            set (r2 := QSumList _) in IH |- *.
            set (r3 := QSumList _) in IH |- *.
            set (r4 := QSumList _) in IH |- *.
            set (r5 := EdgeMap.find _ _ _) in IH |- *.            
            lra.
        ++  destruct (equal y a); subst.
        +++ left. split; [cbn;auto|].
            do 4 (rewrite map_fn; rewrite QSumListFn).
            repeat rewrite EdgeMap.FindUpdateEq.
            repeat rewrite EdgeMap.FindUpdateNeq; 
            [|intros C; inv_clear C; contradiction].
            set (r1 := QSumList _) in IH |- *.
            set (r2 := QSumList _) in IH |- *.
            set (r3 := QSumList _) in IH |- *.
            set (r4 := QSumList _) in IH |- *.
            set (r5 := EdgeMap.find _ _ _) in IH |- *.            
            set (r6 := EdgeMap.find _ _ _) in IH |- *.
            rewrite Qred_correct.     
            lra.
        +++ destruct (equal x a); subst.
            *   right. split; [intros C; inv_clear C; contradiction|].
                do 4 (rewrite map_fn; rewrite QSumListFn).
                repeat rewrite EdgeMap.FindUpdateEq.
                rewrite EdgeMap.FindUpdateNeq; 
                [|intros C; inv_clear C; contradiction].
                set (r1 := QSumList _) in IH |- *.
                set (r2 := QSumList _) in IH |- *.
                set (r3 := QSumList _) in IH |- *.
                set (r4 := QSumList _) in IH |- *.
                set (r5 := EdgeMap.find _ _ _) in IH |- *.            
                lra.
            *   right. split; [intros C; inv_clear C; contradiction|].
                do 4 (rewrite map_fn; rewrite QSumListFn).
                repeat rewrite EdgeMap.FindUpdateEq.
                repeat (rewrite EdgeMap.FindUpdateNeq; 
                [|intros C; inv_clear C; contradiction]).
                set (r1 := QSumList _) in IH |- *.
                set (r2 := QSumList _) in IH |- *.
                set (r3 := QSumList _) in IH |- *.
                set (r4 := QSumList _) in IH |- *.
                set (r5 := EdgeMap.find _ _ _) in IH |- *.            
                lra.
    Qed.

    (* Kui mingi kaare voogu suurendatakse, siis see ei mõjuta tippu,
    mis pole selle kaare üks otstippudest. *)
    Lemma PushExcessOther f xs x y z d:
        x<>y -> z<>x -> z<>y ->
        Distinct xs ->
        excess_loop (EdgeMap.update (x,y) (fun x=> Qred (x+d)) f) z xs == excess_loop f z xs .
    Proof.
        intros Hxy Hxz Hyz Hd.
        unfold excess_loop.
        induction xs.
        +   cbn. lra.
        +   cbn in Hd. destruct Hd as [Hd1 Hd2].
            specialize (IHxs Hd2).
            do 4 rewrite map_fn, QSumListFn.
            destruct (equal a x); subst.
        +++ rewrite EdgeMap.FindUpdateNeq;
            [|intros C; inv_clear C; contradiction].
            rewrite EdgeMap.FindUpdateNeq;
            [|intros C; inv_clear C; contradiction].
            lra.
        +++ rewrite EdgeMap.FindUpdateNeq;
            [|intros C; inv_clear C; contradiction].
            rewrite EdgeMap.FindUpdateNeq;
            [|intros C; inv_clear C; contradiction].
            lra.
    Qed.

    Definition ExcessCacheNormal e:= forall v,
        ExcessMap.find (Qred 0) e v = Qred (ExcessMap.find (Qred 0) e v).

    (* Kui ülejäägid on õigesti salvestatud, siis on need õigesti salvestatud ka pärast järgmiste
    tegevuste tegemist:
    1) suurendatakse kaare (x,y) voogu d võrra;
    2) ülejääkide andmestruktuuris suurendatakse tipu y ülejääki d võrra;
    3) ülejääkide andmestruktuurid vähendatakse tipu x ülejääki d võrra. *)
    Lemma ExcessCachedNe fn f e x y d:
        x<>y ->
        x ∈v nodes fn = true ->
        y ∈v nodes fn = true ->
        ExcessCacheNormal e ->
        ExcessCached fn f e ->
        ExcessCached fn 
            (EdgeMap.update (x, y) (fun x0 : Q => Qred (x0 + d)) f)
            (ExcessMap.update y (fun x0 : Q => Qred (x0 + d)) 
                (ExcessMap.update x (fun x0 : Q => Qred (x0 - d)) e)).
    Proof. 
        destruct fn as [[[[vs es] c] s] t].
        intros Hxy Hx Hy Hexn Hex v.
        unfold excess.
        destruct (equal y v), (equal x v); subst; try contradiction.
        ++  rewrite ExcessMap.FindUpdateEq.
            rewrite ExcessMap.FindUpdateNeq; auto.
            apply Qred_complete.
            assert (In x (VertexSet.to_list vs)). {
                apply VertexSet.to_list_in. auto.
            }
            pose proof (PushExcessIn f (VertexSet.to_list vs) x v d Hxy (VertexSet.to_list_distinct _)).
            destruct H0; destruct H0; [|contradiction].
            unfold excess_loop in H1.
            rewrite H1. rewrite <- Hex. unfold excess.
            rewrite Qred_correct.
            reflexivity.
        ++  rewrite ExcessMap.FindUpdateNeq; auto.
            rewrite ExcessMap.FindUpdateEq.
            apply Qred_complete.
            assert (In y (VertexSet.to_list vs)). {
                apply VertexSet.to_list_in. auto.
            }
            pose proof (PushExcessOut f (VertexSet.to_list vs) v y d Hxy (VertexSet.to_list_distinct _)).
            destruct H0; destruct H0; [|contradiction].
            unfold excess_loop in H1.
            rewrite H1. rewrite <- Hex. unfold excess.
            rewrite Qred_correct.
            reflexivity.
        ++  rewrite ExcessMap.FindUpdateNeq; auto.
            rewrite ExcessMap.FindUpdateNeq; auto.
            rewrite Hexn. apply Qred_complete.
            rewrite SumNoUpdateL; auto. 
            rewrite SumNoUpdateR; auto. 
            rewrite <- Hex. unfold excess.
            rewrite Qred_correct.
            reflexivity.
    Qed.
 
    (* alternatiivne tõestus eelmisele *)
    Lemma ExcessCachedNe' fn f e x y d:
        x<>y ->
        x ∈v nodes fn = true ->
        y ∈v nodes fn = true ->
        ExcessCacheNormal e ->
        ExcessCached fn f e ->
        ExcessCached fn 
            (EdgeMap.update (y, x) (fun x0 : Q => Qred (x0 - d)) f)
            (ExcessMap.update y (fun x0 : Q => Qred (x0 + d)) 
                (ExcessMap.update x (fun x0 : Q => Qred (x0 - d)) e)).
    Proof.
        destruct fn as [[[[vs es] c] s] t].
        intros Hxy Hx Hy Hexn Hex v.
        unfold excess.
        destruct (equal y v), (equal x v); subst; try contradiction.
        ++  rewrite ExcessMap.FindUpdateEq.
            rewrite ExcessMap.FindUpdateNeq; auto.
            apply Qred_complete.
            assert (In x (VertexSet.to_list vs)). { 
                apply VertexSet.to_list_in. auto.
            }
            assert (Hyx: v<>x). { auto. }
            pose proof (PushExcessOut f (VertexSet.to_list vs) v x (-d) Hyx (VertexSet.to_list_distinct _)).
            destruct H0; destruct H0; [|contradiction].
            unfold excess_loop in H1.
            rewrite H1. rewrite <- Hex. unfold excess.
            rewrite Qred_correct. lra.
        ++  rewrite ExcessMap.FindUpdateNeq; auto.
            rewrite ExcessMap.FindUpdateEq.
            apply Qred_complete.
            assert (In y (VertexSet.to_list vs)). { 
                apply VertexSet.to_list_in. auto.
            }
            pose proof (PushExcessIn f (VertexSet.to_list vs) y v (-d) n (VertexSet.to_list_distinct _)).
            destruct H0; destruct H0; [|contradiction].
            unfold excess_loop in H1.
            rewrite H1. rewrite <- Hex. unfold excess.
            rewrite Qred_correct.
            reflexivity.
        ++  rewrite ExcessMap.FindUpdateNeq; auto.
            rewrite ExcessMap.FindUpdateNeq; auto.
            rewrite Hexn. apply Qred_complete.
            rewrite SumNoUpdateL; auto. 
            rewrite SumNoUpdateR; auto. 
            rewrite <- Hex. unfold excess.
            rewrite Qred_correct.
            reflexivity.
    Qed.
    

    (* Kui enne push-sammu on ülejäägid õigesti meelde jäetud, siis on nad seda ka pärast push-sammu. *)
    Lemma PushExcessCached fn f e x y f' e':
        y<>x ->
        x ∈v nodes fn = true ->
        y ∈v nodes fn = true ->
        ExcessCacheNormal e ->
        ExcessCached fn f e ->
        push fn f e x y = (f', e') ->
        ExcessCached fn f' e'.
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

    (* Sama nagu ExcessCachedNe, aga ühe tipuga. *)
    Lemma ExcessCachedLoop fn f e x d:
        x ∈v nodes fn = true ->
        ExcessCacheNormal e ->
        ExcessCached fn f e ->
        ExcessCached fn 
            (EdgeMap.update (x, x) (fun x0 : Q => Qred (x0 + d)) f)
            (ExcessMap.update x (fun x0 : Q => Qred (x0 + d)) 
                (ExcessMap.update x (fun x0 : Q => Qred (x0 - d)) e)).
    Proof.
        destruct fn as [[[[vs es] c] s] t].
        intros Hx Hexn Hex v.
        unfold excess.
        pose proof (PushExcessCycle f (VertexSet.to_list vs) x d v).
        unfold excess_loop in H.
        destruct (equal v x); subst.
        ++  repeat rewrite ExcessMap.FindUpdateEq.
            apply Qred_complete. rewrite H. 
            rewrite <- Hex. unfold excess.
            repeat rewrite Qred_correct.
            lra.
        ++  repeat (rewrite ExcessMap.FindUpdateNeq; auto).
            rewrite Hexn.
            apply Qred_complete. rewrite H. 
            rewrite <- Hex. unfold excess.
            repeat (rewrite Qred_correct; auto).
            lra.
    Qed.

    Lemma ExcessCachedLoop' fn f e x d:
        x ∈v nodes fn = true ->
        ExcessCacheNormal e ->
        ExcessCached fn f e ->
        ExcessCached fn 
            (EdgeMap.update (x, x) (fun x0 : Q => Qred (x0 - d)) f)
            (ExcessMap.update x (fun x0 : Q => Qred (x0 + d)) 
                (ExcessMap.update x (fun x0 : Q => Qred (x0 - d)) e)).
    Proof.
        destruct fn as [[[[vs es] c] s] t].
        intros Hx Hexn Hex v.
        unfold excess.
        pose proof (PushExcessCycle f (VertexSet.to_list vs) x (-d) v).
        unfold excess_loop in H.
        destruct (equal v x); subst.
        ++  repeat rewrite ExcessMap.FindUpdateEq.
            apply Qred_complete. rewrite H. 
            rewrite <- Hex. unfold excess.
            repeat rewrite Qred_correct.
            lra.
        ++  repeat (rewrite ExcessMap.FindUpdateNeq; auto).
            rewrite Hexn.
            apply Qred_complete. rewrite H. 
            rewrite <- Hex. unfold excess.
            repeat (rewrite Qred_correct; auto).
            lra.
    Qed.

    Lemma PushExcessCachedLoop fn f e x f' e':
        x ∈v nodes fn = true ->
        ExcessCacheNormal e ->
        ExcessCached fn f e ->
        push fn f e x x = (f', e') ->
        ExcessCached fn f' e'.
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
    
    (* Pärast relabel-sammu ei teki "järskeid kaari" ehk kaari, kus oleks alles läbilaskevõimet ja
    kaare lähtetipu kõrgus oleks suurem kui kaare sihttipu kõrgus + 1. *)
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

    (* Kui u on aktiivne tipp, "järskeid" kaari pole, push-sammuks
    sobilikku tippu ei leita, relabel-sammuks leitakse sobilik tipp,
    siis relabel-sammu eeldused on täidetud. *)
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

    (* Siis kui gpr_helper tagastab voo f', ülejäägid e' ja kõrgused l', siis järeldub, et ainukesed aktiivsed tipud on sisend või väljund,
     täidetud on voo säilivuse nõue ja sisendi ning väljundi kõrgused on samad, mis alguses ehk invariante ei rikuta.  *)
    Lemma FlowConservationGpr fn g:forall (f: @EdgeMap.t R 0) (e:ExcessMap.t R) (l: @VertexMap.t nat O) ac,
        let '((vs, es),c,s,t) := fn in
        (* Iga tipp u ja v korral, kui nende vahel on serv, siis need tipud kuuluvad tippude hulka*)
        (forall u v, ((u, v) ∈e es = true) -> (u ∈v vs) = true /\ (v ∈v vs) = true) ->
        ExcessCacheNormal e ->
        ExcessCached fn f e ->
        (* Leidub tippusid, mille vahel on läbilaskevõime *)
        ResCapNodes fn f ->
        (* Täidetud on invariant h(u) <= h(v) + 1 *)
        NoSteepArc fn f l ->
        (* Iga tipp n korral, kui n kuulub aktiivsete tippude hulka, siis n kuulub ka tippude hulka*)
        (forall n, n ∈v ac = true -> n ∈v vs = true) ->
        (* Graafis on säilitatud korrektsed kõrgused *)
        ValidLabeling fn f l ->
        (* Iga tipu n korral, kui n kuulub aktiivsete tippude hulka, siis see on ekvivalentne sellega, et tipus n on ülejääk ja 
        tipp n pole sisend ega väljund*)
        (forall n, n ∈v ac = true <-> (ActiveNode fn f n /\ n<>t /\ n<>s)) ->
        (* Täidetud on eelvoo tingimused *)
        PreFlowCond fn f ->
        (* Vood ja läbilaskevõimed on mittenegatiivsed *)
        FlowMapPositiveConstraint fn f ->
        (* gpr_helper tagastab voo f', ülejäägid e' ja kõrgsued l'. Sellest järeldub, et*)
        forall f' e' l', 
        gpr_helper fn f e l ac g = (Some (f', e', l')) ->
        ExcessCacheNormal e' /\
        ExcessCached fn f' e' /\
        (* Aktiivsete tippude hulga ainsad elemendid on väljund ja sisend*)
        (forall n, ActiveNode fn f' n -> n=t \/ n=s) /\
        (* Täidetud on voo säilivuse nõue*)
        FlowConservationConstraint fn f' e' /\
        (* Sisendi ja väljundi kõrgus on funktsiooni gpr_helper lõpus sama, mis oli alguses *)
        (l[s]l)%nat = (l'[s]l)%nat /\ (l[t]l)%nat = (l'[t]l)%nat.
    Proof. 
        destruct fn as [[[[vs es] c] s] t]. induction g;
        intros f e l ac Heisn Hen Hex Hrcn Hnsa Hnvs Hvl Han Hprc Hfmpc f' l' e' H.
        +   simpl in H. inversion H.
        +   rewrite gpr_helper_fn in H. destruct_guard_in H.
        ++  destruct p. destruct_guard_in H.
        +++ cbn zeta in H. destruct_guard_in H.
        *   apply VertexSet.choiceSome in E0. destruct E0.
            destruct_guard_in H.
        **  eapply IHg in H; eauto.
        *** unfold push in E2 . destruct_guard_in E2.
        -   intros q.
            apply pair_equal_spec in E3. destruct E3. subst. clear - Hen.
            destruct (equal q v0).
        --  subst. unfold excess_update. rewrite ExcessMap.FindUpdateEq. 
            apply Qred_complete. set (q:=Qred _).  rewrite (Qred_correct). reflexivity.
        --  repeat (rewrite ExcessMap.FindUpdateNeq with (v:=v0); auto).
            destruct (equal q v).
        --- subst. unfold excess_update. rewrite ExcessMap.FindUpdateNeq; auto. 
        rewrite ExcessMap.FindUpdateEq.
            apply Qred_complete. set (q:=Qred _).  rewrite Qred_correct. reflexivity.
        --- repeat (unfold excess_update; rewrite ExcessMap.FindUpdateNeq; auto). 
        -   intros q. 
            apply pair_equal_spec in E3. destruct E3. subst. clear - Hen.
            destruct (equal q v0).
        --  subst. unfold excess_update. rewrite ExcessMap.FindUpdateEq.
            apply Qred_complete. set (q:=Qred _ ). rewrite Qred_correct. reflexivity.
        --  repeat (rewrite ExcessMap.FindUpdateNeq with (v:=v0); auto).
            destruct (equal q v).
        --- subst. repeat (rewrite ExcessMap.FindUpdateEq). unfold excess_update. 
        rewrite ExcessMap.FindUpdateNeq; auto. rewrite ExcessMap.FindUpdateEq.
            apply Qred_complete. set (q:=Qred _).  rewrite Qred_correct. reflexivity.
        --- repeat (rewrite ExcessMap.FindUpdateNeq; auto). unfold excess_update.
        rewrite ExcessMap.FindUpdateNeq; auto. rewrite ExcessMap.FindUpdateNeq; auto.
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
        *** clear H IHg. intros. destruct_guard_in H. simpl VertexSet.mem in H.
        **** destruct (equal n v0).
        ***** subst. eapply FPNinVs; eauto.
        ***** rewrite VertexSet.MemAddNeq in H; auto.
        **** destruct (equal n v0).
        ***** subst. eapply FPNinVs; eauto.
        ***** rewrite VertexSet.MemAddNeq in H; auto. subst. destruct (equal n v).
        ****** subst. rewrite VertexSet.MemRemoveEq in H. inversion H.
        ****** rewrite VertexSet.MemRemoveNeq in H; auto.
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
        ****** auto.
        ***** clear H IHg. rewrite VertexSet.MemAddNeq in H2; eauto.
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
        --  subst. unfold excess_update. rewrite ExcessMap.FindUpdateEq.
            apply Qred_complete. set (q:=Qred _ ). rewrite Qred_correct. reflexivity.
        --  repeat (rewrite ExcessMap.FindUpdateNeq with (v:=v0); auto).
            destruct (equal q v).
        --- subst. unfold excess_update. rewrite ExcessMap.FindUpdateNeq; auto.
        rewrite ExcessMap.FindUpdateEq. 
            apply Qred_complete. set (q:=Qred _). rewrite Qred_correct. reflexivity.
        --- repeat (unfold excess_update; rewrite ExcessMap.FindUpdateNeq; auto).
        -   intros q. 
            apply pair_equal_spec in E3. destruct E3. subst. clear - Hen.
            destruct (equal q v0).
        --  subst. unfold excess_update. rewrite ExcessMap.FindUpdateEq.
            apply Qred_complete. set (q:=Qred _ ). rewrite Qred_correct. reflexivity.
        --  repeat (rewrite ExcessMap.FindUpdateNeq with (v:=v0); auto).
            destruct (equal q v).
        --- subst. unfold excess_update. repeat rewrite ExcessMap.FindUpdateEq. 
        rewrite ExcessMap.FindUpdateNeq; auto. rewrite ExcessMap.FindUpdateEq.  
            apply Qred_complete. set (q:=Qred _). rewrite Qred_correct. reflexivity.
        --- repeat (unfold excess_update; rewrite ExcessMap.FindUpdateNeq; auto).
        *** destruct (equal v v0).
        -   subst. apply PushExcessCachedLoop in E2; auto.
        -   apply PushExcessCached in E2; auto.
        *** rewrite (PairFst E2).
            eapply PushResCapNodes; auto.
        *** rewrite (PairFst E2).
            eapply PushNoSteepArc; auto.
        *** intros. destruct (equal n v0).
        **** subst. auto.
        **** rewrite VertexSet.MemRemoveNeq in H4; auto. eapply Hnvs.
         destruct_guard_in H4; auto. subst.
         rewrite VertexSet.MemRemoveNeq in H4; auto.
         intro C. subst. rewrite VertexSet.MemRemoveEq in H4. inversion H4.
        *** rewrite (PairFst E2).
            eapply (PushValidLabel (vs, es, c, s, t)); eauto.
        *** intros. destruct (equal n v0).
        **** subst. rewrite VertexSet.MemRemoveEq. split; intros; [inversion H1 |].
        destruct Q.
        ***** destruct H1. destruct H1. 
            destruct (equal v v0).
        -   subst. apply PushExcessCachedLoop in E2; auto.
            specialize (E2 v0). rewrite E2 in H6. simpl Qred in *.  lra. 
        -   apply PushExcessCached in E2; auto.
            specialize (E2 v0). rewrite E2 in H6. simpl Qred in *.  lra.
        ***** simpl in H4. tauto.
        **** rewrite VertexSet.MemRemoveNeq; auto. destruct_guard; split; intros.
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
        ****** subst. rewrite VertexSet.MemRemoveEq in H4. inversion H4.
        ****** rewrite VertexSet.MemRemoveNeq in H4; auto. 
            eapply Han in H4. destruct H4. split; auto.
            rewrite (PairFst E2).
            eapply PushActiveCondition; eauto.
        ***** subst. destruct (equal n v).
        ****** subst. eapply QLt_false in E3. destruct H4, H1. 
            destruct (equal v v0).
        -   subst. apply PushExcessCachedLoop in E2; auto.
        -   apply PushExcessCached in E2; auto.
            specialize (E2 v). rewrite E2 in H5. lra.
        ****** rewrite VertexSet.MemRemoveNeq; auto. eapply Han. 
            destruct H4. split; auto.
            rewrite (PairFst E2) in H1.
            eapply PushActiveInv in P2; eauto.
        *** rewrite (PairFst E2).
            eapply (PushPreFlow (vs, es, c, s, t)); eauto.
        *** rewrite (PairFst E2).
            eapply (PushFlowMapPos (vs, es, c, s, t)); eauto.
        *** auto.
        +++ destruct_guard_in H.
        ** eapply VertexSet.choiceSome in E0; auto. destruct E0, H1.
            eapply IHg in H; eauto.
        *** split; try tauto. split; try tauto.
            destruct H, H1, H2, H3, H4.  rewrite <- H4, <- H5. subst.
            unfold relabel in E2. destruct_guard_in E2; [|inversion E2]. inv_clear E2.
            destruct (equal s v).
        **** subst. exfalso. apply Han in H0. destruct H0, H6. auto.
        **** rewrite VertexMap.FindReplaceNeq; auto. split; auto.
            destruct (equal t v). 
        ***** subst. exfalso. apply Han in H0. destruct H0. destruct H6; auto.
        ***** rewrite VertexMap.FindReplaceNeq; auto.
        *** eapply RelabelNoSteepArc; eauto.
        *** eapply (RelabelValidLabel (vs, es, c, s, t)); eauto. 
        unfold relabel in E2. destruct_guard_in E2; [| inversion E2].
        eapply RelabelValidCondition; eauto.
        **** apply Han. auto.
        ** inversion H. 
        ++  apply VertexSet.choiceNone in E0. subst. inv_clear H. 
            repeat split; try tauto.
        * intros. destruct (equal n t); auto. 
        destruct (equal n s); subst; try tauto.
        assert (n ∈v VertexSet.empty = true).
        ** eapply Han. tauto.
        ** rewrite VertexSet.MemEmpty in H0. inversion H0.
        * 
         unfold FlowConservationConstraint. intros. unfold PreFlowCond in Hprc.
        destruct Hprc. unfold NonDeficientFlowConstraint in H3.
        apply H3 in H as P; auto. clear IHg. 
        destruct (Qeq_bool (excess (vs, es, c, s, t) f' v) 0) eqn : E.
        ** eapply Qeq_bool_iff in E. rewrite <- Hex. auto.
        ** eapply Qeq_bool_neq in E. assert (v ∈v VertexSet.empty = true).
        *** eapply Han. split; auto. split; auto. lra.
        *** rewrite VertexSet.MemEmpty in H4. inversion H4.
    Qed.

    (* Kui (s,y) voog ei ole suurem d-st (0), siis tipu n ülejääk ei ole suurem kui (s,y) voog
        muuta võrdseks d-ga. *)
    Lemma NDFinitial vs es c s t d y n f:
        0 <= d ->
        n<>s ->
        excess (vs, es, c, s, t) f n <= 
            excess (vs, es, c, s, t) (EdgeMap.update (s, y) (fun x : Q => Qred (x + d)) f) n .
    Proof.
        intros Hd Hnns. unfold excess.
        set (xs := VertexSet.to_list vs). repeat rewrite Qred_correct.
        induction xs; intros.
        +   simpl. lra. 
        +   repeat rewrite map_fn. repeat rewrite QSumListFn.
            destruct (equal n y).
        -   subst. destruct (equal a s).
        *   subst. erewrite EdgeMap.FindUpdateEq. 
            erewrite EdgeMap.FindUpdateNeq;
                [|intros C; inv_clear C; contradiction].
            unfold R in *. rewrite Qred_correct. lra.
        *   repeat (erewrite EdgeMap.FindUpdateNeq;
                [|intro C; inv_clear C; auto]).
            unfold R in *. lra.
        - repeat (erewrite EdgeMap.FindUpdateNeq;
                [|intro C; inv_clear C; auto]).
            unfold R in *. lra.
    Qed.

    (* Tippu n sisenevate kaarte summa ei muutu väiksemaks, kui eelenvalt suurendada kõiki
    tipust s väljuvate kaarte voogusid d võrra. *)
    Lemma InitialUpdateBigger: forall f s v0 n d xs, d >= 0 ->
        QSumList (map (fun v1 : V =>
             EdgeMap.find 0 (EdgeMap.update (s, v0) (fun x => Qred (x + d)) f) (v1, n)) xs) >=
        QSumList (map (fun v1 : V => f[(v1, n)]f) xs).
    Proof.
        intros f s v0 n d xs H.
        induction xs; intros; [cbn; try lra|].
        destruct (Edge.equal (a,n) (s,v0)).
        +   inv_clear e.
            repeat rewrite map_fn.
            repeat rewrite QSumListFn.
            rewrite EdgeMap.FindUpdateEq.
            rewrite Qred_correct. lra.
        +   repeat rewrite map_fn.
            repeat rewrite QSumListFn.
            rewrite EdgeMap.FindUpdateNeq; auto. lra.
    Qed.

    (* Peale initsialiseerimist on aktiivsete tippude hulgas tipud, mis ei ole sisend ega väljund ja on täidetud eelvoo nõuded
     ja vood ning läbilaskevõimed on mittenegatiivsed*)
    Lemma InitialGpr fn:
        let '((vs, es),c,s,t) := fn in
        (* Iga tipp u ja v korral, kui nende vahel on serv, siis need tipud kuuluvad tippude hulka*)
        (forall u v, ((u, v) ∈e es = true) -> (u ∈v vs) = true /\ (v ∈v vs) = true) ->
        (forall u v, c u v >= 0) ->
        forall f' e' ac' ,
        (* Kui algoritmi initsialiseerimise samm, kus tehakse push samm sisendist väljuvate servade peal
        tagastab voo f' ja aktiivsed tipud ac', siis sellest järeldub all olev konjuktsioon*)
        initial_push fn = (f',e',ac') ->
        ExcessCacheNormal e' /\
        ExcessCached fn f' e' /\
        ResCapNodes fn f' /\
        (forall n, n ∈v ac' = true -> n ∈v vs = true) /\
        (forall n, n ∈v ac' = true <-> (ActiveNode fn f' n /\ n<>t /\ n<>s)) /\
        PreFlowCond fn f' /\
        FlowMapPositiveConstraint fn f'.
    Proof.
        destruct fn as [[[[vs es] c] s] t].
        intros Hvs Hc. 
        intros f' e' ac'.
        unfold initial_push.
        set (es' := EdgeSet.filter _ _).
        rewrite <- fold_left_rev_right.
        unfold initial_push_step.
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
        assert (Ds: Distinct xs). {
            apply rev_distinct. 
            apply EdgeSet.to_list_distinct.
        }
        set (F := (fun y => _)).
        intros H.
        apply (@proj2  (forall u v, ~In (u,v) xs -> f'[(u, v)]f == 0)).
        generalize dependent H.
        generalize dependent e'.
        generalize dependent ac'.
        generalize dependent f'.
        induction xs; intros f' e' ac' H.
        +   cbn in H. inv_clear H.
             repeat split; auto.
        ++  intros. rewrite EdgeMap.FindEmpty. lra.
        ++  intros v. rewrite ExcessMap.FindEmpty. apply Qred_complete. 
            rewrite Qred_correct. lra.
        ++  intros v. unfold excess.
            rewrite ExcessMap.FindEmpty. apply Qred_complete.
            generalize (VertexSet.to_list vs).
            intros l. induction l; cbn; [lra|].
            repeat rewrite EdgeMap.FindEmpty. lra.
        ++  cbn in H. destruct_guard_in H.
        +++ apply Hvs in E0. tauto.
        +++ rewrite EdgeMap.FindEmpty in H. lra.
        ++  cbn in H. destruct_guard_in H.
        +++ apply Hvs in E0. tauto.
        +++ rewrite EdgeMap.FindEmpty in H. lra.
        ++  intros. rewrite VertexSet.MemEmpty in H. inversion H.
        ++  rewrite VertexSet.MemEmpty in H. inversion H.
        ++  rewrite VertexSet.MemEmpty in H. inversion H.
        ++  rewrite VertexSet.MemEmpty in H. inversion H.
        ++  rewrite VertexSet.MemEmpty in H. inversion H.
        ++  intros [[H0 H1] [H2 H3]]. 
            unfold excess in H1.
            set (ys:=VertexSet.to_list vs) in H1. exfalso. clear -H1.
            induction ys.
        +++ cbn in H1. lra.
        +++ repeat rewrite map_fn, QSumListFn in H1.
            repeat rewrite EdgeMap.FindEmpty in H1.
            rewrite Qred_correct in H1, IHys. lra.
        ++  cbn. intros. rewrite EdgeMap.FindEmpty. apply Hc.
        ++  unfold NonDeficientFlowConstraint, excess. intros. 
            set (ys:=VertexSet.to_list vs). clear -ys .
            induction ys.
        +++ cbn. lra.
        +++ repeat rewrite map_fn, QSumListFn.
            repeat rewrite EdgeMap.FindEmpty.
            rewrite Qred_correct in IHys |- *. lra.
        ++  rewrite EdgeMap.FindEmpty. lra.
        +   simpl fold_right in H. destruct a.
            destruct (fold_right F (EdgeMap.empty 0, ExcessMap.empty 0, VertexSet.empty) xs) eqn:E. destruct p.
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
        +++ rewrite EdgeMap.FindUpdateNeq; auto.
            apply H1. intro C. apply H. right. apply C.
        ++  intros v.
            destruct (equal v0 v).
        +++ subst. rewrite ExcessMap.FindUpdateEq.
            apply Qred_complete. symmetry. apply Qred_correct.
        +++ rewrite ExcessMap.FindUpdateNeq; auto.
            destruct (equal s v).
            *   subst. rewrite ExcessMap.FindUpdateEq; auto.
                apply Qred_complete. symmetry.
                apply Qred_correct.
            *   rewrite ExcessMap.FindUpdateNeq; auto.
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
            *   rewrite EdgeMap.FindUpdateNeq in H; auto.
                apply H4 in H. cbn. tauto.
        ++  unfold res_cap in H. 
            specialize (H4 u v).
            unfold res_cap in H4.
            destruct ((u, v) ∈e es) eqn:E1.
        +++ apply Hvs in E1. tauto.
        +++ destruct (Edge.equal (s,v0) (v,u)).
            *   inv_clear e. cbn. tauto.
            *   rewrite EdgeMap.FindUpdateNeq in H; auto.
                apply H4 in H. cbn. tauto.
        ++  intros. 
            destruct (equal v0 t); cbn in H; subst; auto.
            destruct (equal v0 s); cbn in H; subst; auto.
            destruct_guard_in H; auto.
            destruct (equal n v0); cbn in H; subst; try  tauto.
            erewrite VertexSet.MemAddNeq in H; auto.
        ++  cbn.
            destruct (equal v0 t); subst.
        +++ apply H5, H.
        +++ destruct (equal v0 s); subst.
            *   apply H5, H.
            *   set (q := ExcessMap.find _ _ _) in H.
                cbn in H.
                destruct (0 <? q) eqn:E1.
            **  destruct (equal n v0); subst; auto.
                rewrite VertexSet.MemAddNeq in H; auto.
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
            *   rewrite ExcessMap.FindUpdateEq in H.
                rewrite ExcessMap.FindUpdateNeq in H; auto.
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
                assert (In s (VertexSet.to_list vs)). {
                    apply VertexSet.to_list_in. auto.
                }
                pose proof (PushExcessIn t1 (VertexSet.to_list vs) s v0 (c s v0) H0 (VertexSet.to_list_distinct _)).
                destruct H9; destruct H9; [|contradiction].
                unfold excess_loop in H10.
                unfold excess in *.
                rewrite Qred_correct in *.
                rewrite H10.
                lra.
            **  rewrite VertexSet.MemAddNeq in H; auto.
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
            *   rewrite ExcessMap.FindUpdateEq in H.
                rewrite ExcessMap.FindUpdateNeq in H; auto.
                set (q := Qred _) in H.
                simpl in H.
                destruct (0 <? q) eqn:E1;
                [destruct (equal n v0)|].
            **  subst. tauto.
            **  rewrite VertexSet.MemAddNeq in H; auto.
                apply H6 in H.
                destruct H, H, H0. tauto.
            **  apply H6 in H.
                destruct H, H, H0. tauto.
        ++  intros.
            destruct (equal v0 t); subst.
        +++ apply H6. destruct H. split; try tauto.
        +++ destruct (equal v0 s); subst.
            *   apply H6. destruct H. split; try tauto.
            *   rewrite ExcessMap.FindUpdateEq in H.
                rewrite ExcessMap.FindUpdateNeq in H; auto.
                set (q := Qred _) in H.
                simpl in H.
                destruct (0 <? q) eqn:E1;
                [destruct (equal n v0)|].
            **  subst. tauto.
            **  simpl in H. rewrite VertexSet.MemAddNeq in H; auto.
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
            *   pose proof (PushExcessCycle t1 (VertexSet.to_list vs) t (c t t) n).
                unfold excess_loop in *. rewrite H in H0. lra.
            *   assert (In t (VertexSet.to_list vs)). { 
                    apply VertexSet.to_list_in. auto.
                }
                pose proof (PushExcessOther t1 (VertexSet.to_list vs) s t n (c s t) n0 K3 K2 (VertexSet.to_list_distinct _)). 
                unfold excess_loop in H1. rewrite H1 in H0.
                lra.
        +++ destruct (equal v0 s); subst.
            *   unfold ActiveNode in K1.
                apply H6. split; try tauto.
                unfold ActiveNode.
                split; try tauto. destruct K1.
                clear -H0 K2 K3 J1 Hc. unfold excess in *.
                rewrite Qred_correct in *.
                pose proof (PushExcessCycle t1 (VertexSet.to_list vs) s (c s s) n).
                unfold excess_loop in *. rewrite H in H0. lra.
            *   rewrite ExcessMap.FindUpdateEq.
                rewrite ExcessMap.FindUpdateNeq; auto.
                destruct (0 <? Qred (t2[v0]e + c s v0)) eqn:E3.
            ** destruct (equal n v0); subst.
            *** cbn. rewrite VertexSet.MemAddEq. auto.
            *** cbn. rewrite VertexSet.MemAddNeq; auto. apply H6. split; try tauto.
                unfold ActiveNode in K1 |- *. destruct K1. split; auto.
                unfold excess in *. rewrite Qred_correct in *.
                assert (G1: s<>v0) by auto.
                assert (G2: n<>s) by auto.
                assert (G3: n<>v0) by auto.
                pose proof (PushExcessOther t1 (VertexSet.to_list vs) s v0 n (c s v0) G1 G2 G3 (VertexSet.to_list_distinct _)).                 
                unfold excess_loop in *. rewrite H8 in H0. lra.
            **  destruct (equal n v0); cbn; subst.
            *** apply H6. split; try tauto.
                unfold ActiveNode in K1 |- *. destruct K1. split; auto.
                rewrite <- H3 in E3.
                destruct (QLt_spec 0 (Qred (excess (vs, es, c, s, t) t1 v0 + c s v0))); [inversion E3|].
                exfalso.
                unfold excess in *. rewrite Qred_correct in *.
                assert (G1: s<>v0) by auto.
                assert (In s (VertexSet.to_list vs)). { 
                    apply VertexSet.to_list_in. auto.
                }
                pose proof (PushExcessIn t1 (VertexSet.to_list vs) s v0 (c s v0) G1 (VertexSet.to_list_distinct _)).
                destruct H9; destruct H9; [|contradiction].
                unfold excess_loop in *. 
                rewrite Qred_correct in *. rewrite H10 in H0.
                lra. 
            *** apply H6. split; try tauto.
                unfold ActiveNode in K1 |- *. destruct K1. split; auto.
                rewrite <- H3 in E3.
                destruct (QLt_spec 0 (Qred (excess (vs, es, c, s, t) t1 v0 + c s v0))); [inversion E3|].
                unfold excess in *. rewrite Qred_correct in *.
                assert (G1: s<>v0) by auto.
                assert (G2: n<>s) by auto.
                assert (G3: n<>v0) by auto.
                pose proof (PushExcessOther t1 (VertexSet.to_list vs) s v0 n (c s v0) G1 G2 G3 (VertexSet.to_list_distinct _)).                 
                unfold excess_loop in *. 
                rewrite Qred_correct in *. rewrite H8 in H0.
                lra. 
        ++  unfold CapacityConstraint. intros.
            destruct H7. unfold PreFlowCond in H0.
            destruct H0.
            specialize (H0 u v H).
            destruct (Edge.equal (u,v) (s,v0) ).
        +++ inv_clear e.
            rewrite EdgeMap.FindUpdateEq.
            specialize (H1 _ _ Ds1). 
            rewrite Qred_correct.
            lra.
        +++ rewrite EdgeMap.FindUpdateNeq; auto.
        ++  unfold NonDeficientFlowConstraint. intros.
            destruct H7.  destruct H7. unfold NonDeficientFlowConstraint in H9.
            specialize (H9 v H H0).
            unfold excess in *.
            destruct (equal v0 v); subst.
        +++ rewrite SumNoUpdateL; auto. 
            rewrite Qred_correct. unfold R in *.
            specialize (Hc s v).
            rewrite Qred_correct in *.
            eapply InitialUpdateBigger with (n:=v) (xs:=VertexSet.to_list vs) (s:=s) (v0:=v) (f:=t1) in Hc.
            clear -Hc H9. lra.
        +++ rewrite SumNoUpdateL; auto.
            rewrite SumNoUpdateR; auto.
        ++  unfold CapacityConstraint. intros.
            destruct (Edge.equal (s,v0) (u, v)).
            *   inv_clear e.
                rewrite EdgeMap.FindUpdateEq.
                rewrite Qred_correct.
                destruct H7, H. 
                specialize (H0 u v).
                lra.
            *   rewrite EdgeMap.FindUpdateNeq; auto.
                destruct H7, H. 
                specialize (H0 u v).
                lra.
    Qed.


    Lemma InitialPushResCap0Helper vs es c s t xs: 
    Distinct xs -> forall f' ac' e', 
    fold_right (fun x y => initial_push_step (vs,es,c,s,t) y x) (EdgeMap.empty 0, ExcessMap.empty 0, VertexSet.empty) xs = (f',e',ac') ->
    (forall v, In (s,v) xs -> f'[(s, v)]f == c s v) /\
    (forall u v, ~In (u,v) xs -> f'[(u, v)]f == 0).
    Proof.
        induction xs; intros; split; intros.
        +   inv_clear H1.
        +   cbn in H0. inv_clear H0. rewrite EdgeMap.FindEmpty. lra.
        +   simpl in H0. 
            destruct (fold_right _ _ xs) eqn:E1. destruct a, p.
            destruct H as [D1 D2].
            eapply IHxs in D2 as [C1 C2]; [|reflexivity].
            unfold initial_push_step in H0.
            repeat rewrite pair_equal_spec in H0. destruct H0, H; subst.
            destruct (Edge.equal (v0,v1) (s,v)).
        ++  inv_clear e.
            rewrite EdgeMap.FindUpdateEq, C2; auto. 
            rewrite Qred_correct. lra.
        ++  rewrite EdgeMap.FindUpdateNeq; auto.
            destruct H1.
        +++ inv_clear H. destruct n; auto.
        +++ apply C1; auto.
        +   simpl in H0. 
            destruct (fold_right _ _ xs) eqn:E1. destruct a, p.
            destruct H as [D1 D2].
            eapply IHxs in D2 as [C1 C2]; [|reflexivity].
            unfold initial_push_step in H0.
            repeat rewrite pair_equal_spec in H0. destruct H0, H; subst.
            rewrite EdgeMap.FindUpdateNeq.
        ++  apply C2. cbn in H1. tauto.
        ++  intros C. inv_clear C.  cbn in H1. tauto.
    Qed.

    (* Kui Iga serva e korral e kuulub hulka e' või e'', siis ta kuulub hulka es ja iga tipu v korral, kui puudub serv
    (s, v), siis sellel serva läbilaskevõime on 0 ning 
    iga tipu v korral, kui serv (s, v) kuulub hulka e', siis sellel serva läbilaskevõime on 0, sellest järeldub, et
    peale initsialiseerimist on kõik sisendist väljuvate servade läbilaskevõime ära kasutatud *)
    Lemma InitialPushResCap0 vs es c s t v : 
        v<>s -> forall  f' e' ac',
        initial_push (vs,es,c,s,t) = (f',e',ac') ->
        res_cap (vs,es,c,s,t) f' s v == 0.
    Proof.
        unfold initial_push.
        set (es' := EdgeSet.filter _ _).
        rewrite <- fold_left_rev_right.
        set (xs := rev _). intros.
        apply InitialPushResCap0Helper in H0.
        +   destruct H0. unfold res_cap.
            destruct ((s, v) ∈e es) eqn:E.
        ++  rewrite H0; [lra|]. unfold xs. rewrite <- in_rev.
            unfold es'. apply EdgeSet.to_list_in.
            rewrite EdgeSet.filter_in; auto. apply eqb_refl.
        ++  rewrite H1; [lra|]. intro C.
            unfold xs in C.
            rewrite <- in_rev in C.
            unfold es' in C. apply EdgeSet.to_list_in in C.
            eapply EdgeSet.in_filter in C.
            destruct C.
            destruct (equal s v); subst; try tauto.
            inv_clear H3.
        +   unfold xs. apply rev_distinct. unfold es'.
            apply EdgeSet.to_list_distinct.
    Qed.

    (* Kui tipud u ja v kuuluvad tippude hulka ning servade (u, v) läbilaskevõime on mittenegatiivne ja sisend pole väljund ning
     gpr tagastab voo f', ülejäägid e' ja kõrgused l', siis järeldub, et aktiivsed tipud on ainult sisend või väljund,
     on täidetud voo nõuded ja on säilitatud invariandid, et sisendi kõrgus on võrdne tippude arvuga ja väljundi kõrgus on 0 *)
    Lemma FlowConservationGprMain fn:
        let '((vs, es),c,s,t) := fn in
        (forall u v, ((u, v) ∈e es = true) -> (u ∈v vs) = true /\ (v ∈v vs) = true) ->
        True ->
        (forall u v, c u v >= 0) ->
        s<>t ->
        forall f' e' l', 
        gpr fn = (Some (f',e',l')) ->
        (forall n, ActiveNode fn f' n -> n=t \/ n=s) /\ 
        FlowConservationConstraint fn f' e' /\
        (VertexSet.size vs = l'[s]l)%nat /\ (O=l'[t]l)%nat.
    Proof.
        destruct fn as [[[[vs es] c] s] t]. 
        intros H H0 H1 Hst f' l' eM' H2. unfold gpr in H2.
        destruct_guard_in H2. destruct p. 
        eapply (InitialGpr (vs, es, c, s, t)) in E0 as P; eauto.
        +   destruct P, H4, H5, H6, H7, H8. 
            eapply (FlowConservationGpr (vs, es, c, s, t)) in H2; eauto.
        -   destruct H2, H10, H11, H12, H13. split; auto. split; auto.
            rewrite VertexMap.FindReplaceEq in H13.
            rewrite VertexMap.FindReplaceNeq, VertexMap.FindEmpty in H14; auto.
        -   unfold NoSteepArc. intros. destruct (equal u s).
        *   subst. rewrite VertexMap.FindReplaceEq.
            destruct (equal v s);
                [subst;rewrite VertexMap.FindReplaceEq;lia|].        
            unfold PreFlowCond in H8. 
            eapply InitialPushResCap0 with (v := v) in E0; auto.
            lra.
        *   rewrite VertexMap.FindReplaceNeq, VertexMap.FindEmpty; auto. lia.
        -   unfold ValidLabeling. intros. 
            destruct (equal u s), (equal v s).
        *   subst. lia.
        *   subst. unfold PR.E in H10. eapply EdgeSet.in_filter in H10. 
            destruct H10.
            eapply InitialPushResCap0 with (v := v) in E0; auto.
            unfold res_cap in E0. rewrite H10 in E0. 
            eapply (reflect_iff _ _ (QLt_spec _ _)) in H11. lra.
         *  subst. rewrite VertexMap.FindReplaceNeq, VertexMap.FindEmpty; auto. lia.
         *  rewrite VertexMap.FindReplaceNeq, VertexMap.FindEmpty; auto. lia.
    Qed.

End PR.

Import ListNotations.
Module Edge := Tuple (Nat) (Nat).

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
Open Scope nat.

Definition vset_list := fold_right VertexSet.add VertexSet.empty.
Definition eset_list := fold_right EdgeSet.add EdgeSet.empty.

(* Näidistranspordivõrgud*)

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
    ((vset_list [0;1;2;3;4;5],eset_list[(0,1);(0,2);(1,3);(1,4);(2,4);(3,5);(4,5)]),c,0,5).

(* Compute (PRNat.gpr FN1). *)

(* Compute (PRNat.gpr FN2).

Compute (@PRNat.excess FN1 [(0,1,10%Q)] 1).

Compute (@PRNat.excess FN2 [(0, 1, 10%Q); (0, 3, 4%Q); (3, 4, 7%Q); (
    4, 1, 0%Q); (1, 2, 10%Q); (2, 5, 7%Q); (
    4, 5, 7%Q); (2, 3, 3%Q)] 5).

Compute (@PRNat.excess FN3 [(0, 1, 4%Q); (0, 2, 2%Q); 
(2, 4, 2%Q); (4, 5, 2%Q); (1, 3, 4%Q); (3, 5, 4%Q)] 5). *)

Definition FN_excess :=
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
  ((vset_list [0;1;2;3;4;5;6], eset_list [(0,5);(1,2);(1,4);(2,3);(3,4);(3,6);(4,2);(5,1);(5,2)]), c, 0, 6).

Definition FN_rand_test :=
  let c := fun (x y : nat) =>
    match x, y with
    | 0, 1 => 8%Q
    | 0, 2 => 19%Q
    | 1, 2 => 18%Q
    | _, _ => 0%Q
    end
  in
  ((vset_list[0;1;2],eset_list[(0,1);(0,2);(1,2)]), c, 0, 2).

(* Ekstraheerimine *)

(* Lihtsamate andmetüüpide jaoks abiteegid *)
Extraction Language OCaml.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlZInt.
Require Import ExtrOcamlNatInt.

(* Ratsionaalarvud *)
Extract Inductive Q => "(int * int)" [ "" ].

(* Järjendite pikkused ja map-funktsioon. *)
Extract Constant length => "List.length".
Extract Constant map => "List.map".

Set Extraction File Comment "Extracted from the push-relabel algorithm proof in Rocq.".

(* Andmestruktuuride VertexMap, EdgeMap ja ExcessMap ekstraheerimine. *)
Extract Constant VertexMap.t "'e" => "'e VertexMap'.t".
Extract Constant VertexMap.empty => "fun _d -> VertexMap'.create 1".
Extract Constant VertexMap.find => 
    "fun d k m -> 
    try VertexMap'.find k m with Not_found -> d".
Extract Constant VertexMap.replace => "fun _d k v m -> VertexMap'.replace m k v; m".
Extract Constant VertexMap.remove => "fun d k m -> VertexMap'.replace m k d; m".
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
Extract Constant EdgeMap.remove => "fun d k m -> EdgeMap'.replace m k d; m".
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
Extract Constant ExcessMap.remove => "fun d k m -> ExcessMap'.replace m k d; m".
Extract Constant ExcessMap.update => 
    "fun d k f m -> 
        let old = try ExcessMap'.find m k with Not_found -> d
        in ExcessMap'.replace m k (f old); m".

(* Tippude hulga VertexSet ja kaarte hulga EdgeSet ekstraheerimine *)
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

Recursive Extraction PRNat.gpr.
