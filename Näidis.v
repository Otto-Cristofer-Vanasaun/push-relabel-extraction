Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Extraction.

Module Type T.
Parameter V: Type.
Parameter eq: V -> V -> bool.
End T.

Module Type SeqType (t:T) <: T.
Definition V := list t.V.
Parameter eq: V -> V -> bool.
Parameter nil: V.
Parameter cons: t.V -> V -> V.
Parameter app: V -> V -> V.
Parameter foldr: forall {B}, (t.V -> B -> B) -> B -> V -> B.
End SeqType.

Module NatT <: T.
Definition V := nat.

Fixpoint eq (x y: V): bool:=
match x, y with
| O, O => true
| S x, S y => eq x y
| _, _ => false
end.
End NatT.

Module Type PairT (A:T) (B:T) <: T.
Definition V := (A.V * B.V)%type.
Parameter eq: V -> V -> bool.
End PairT.

Module PairTI (A:T) (B:T) : PairT (A) (B).
Definition V := (A.V * B.V)%type.

Definition eq (x y: V): bool:=
match x, y with
| (x1,x2), (y1,y2) => A.eq x1 y1 && B.eq x2 y2
end.
End PairTI.

Module Algo (Tn:T) (Tp:PairT(Tn)(Tn)) (M: SeqType(Tp)).
Definition rev(xs: M.V): M.V :=
M.foldr (fun p xs => M.app xs (M.cons p M.nil)) M.nil xs.
End Algo.

Import ListNotations.
Module RocqList (t:T) <: SeqType(t).
Definition V := list t.V.
Fixpoint eq (xs ys: V) :=
match xs, ys with
| [], [] => true
| x::xs, y::ys => t.eq x y && eq xs ys
| _, _ => false
end.
Definition nil: V := [].
Definition cons (x: t.V) (xs: V) := x::xs.
Fixpoint app (xs ys:V) :=
match xs with
| [] => ys
| x::xs => x :: app xs ys
end.
Fixpoint foldr {B} (f: t.V -> B -> B) (a: B) (xs: V) :=
match xs with
| [] => a
| x::xs => f x (foldr f a xs)
end.
End RocqList.

Module Paar := PairTI(NatT)(NatT).
Module Lst : SeqType(Paar).
Module L := RocqList(Paar).
Definition V := list Paar.V.
Definition eq := L.eq .
Definition nil := L.nil.
Definition cons := L.cons.
Definition app := L.app.
Definition foldr {B}:= @L.foldr B.
End Lst.

Extract Constant Lst.nil => "[]".
(* Extract Constant Lst.cons => "(::)". *)
Extract Constant Lst.app => "(@)".
Extract Constant Lst.foldr => "fun f a xs -> List.fold_right f xs a".
Extract Constant Lst.eq => "fun xs ys -> xs = ys".
Module A := Algo(NatT)(Paar)(Lst).

Extract Inductive unit => "unit" [ "()" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive prod => "(*)" [ "(,)" ].
Extract Inductive list => "list" [ "[]" "(::)" ].

Extract Inductive nat => int [ "0" "Stdlib.Int.succ" ].

Extract Constant NatT.eq => "fun x y -> x = y".

Recursive Extraction A.rev.
