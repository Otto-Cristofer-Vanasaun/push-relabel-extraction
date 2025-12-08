(* Auto-generated random flow network. *)
From Coq Require Import QArith List.
Import ListNotations.
Local Open Scope Q_scope.

Definition FN_test3 : (list nat * list (nat * nat) * (nat -> nat -> Q) * nat * nat)%type :=
  let c := fun (x y : nat) =>
    match x, y with
    | 0, 3 => 20%Q
    | 1, 3 => 4%Q
    | 1, 4 => 18%Q
    | 2, 1 => 6%Q
    | 3, 2 => 9%Q
    | _, _ => 0%Q
    end
  in
  (([0;1;2;3;4],[(0,3);(1,3);(1,4);(2,1);(3,2)]), c, 0, 4).
