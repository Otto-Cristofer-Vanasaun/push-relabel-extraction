(* Auto-generated random flow network. *)
From Coq Require Import QArith List.
Import ListNotations.
Local Open Scope Q_scope.

Definition FN_test2 : (list nat * list (nat * nat) * (nat -> nat -> Q) * nat * nat)%type :=
  let c := fun (x y : nat) =>
    match x, y with
    | 0, 2 => 6%Q
    | 1, 3 => 2%Q
    | 2, 1 => 17%Q
    | 2, 3 => 16%Q
    | 3, 4 => 11%Q
    | _, _ => 0%Q
    end
  in
  (([0;1;2;3;4],[(0,2);(1,3);(2,1);(2,3);(3,4)]), c, 0, 4).
