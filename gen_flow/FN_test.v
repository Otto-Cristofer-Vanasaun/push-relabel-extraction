(* Auto-generated random flow network. *)
From Coq Require Import QArith List.
Import ListNotations.
Local Open Scope Q_scope.

Definition FN_test : (list nat * list (nat * nat) * (nat -> nat -> Q) * nat * nat)%type :=
  let c := fun (x y : nat) =>
    match x, y with
    | 1, 4 => 8%Q
    | 2, 4 => 73%Q
    | 3, 1 => 16%Q
    | 3, 2 => 29%Q
    | 3, 5 => 81%Q
    | 4, 3 => 81%Q
    | _, _ => 0%Q
    end
  in
  (([0;1;2;3;4;5],[(1,4);(2,4);(3,1);(3,2);(3,5);(4,3)]), c, 0, 5).
