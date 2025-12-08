(* Auto-generated random flow network. *)
From Coq Require Import QArith List.
Import ListNotations.
Local Open Scope Q_scope.

Definition FN_test : (list nat * list (nat * nat) * (nat -> nat -> Q) * nat * nat)%type :=
  let c := fun (x y : nat) =>
    match x, y with
    | 0, 2 => 17%Q
    | 0, 3 => 7%Q
    | 1, 2 => 2%Q
    | 2, 4 => 3%Q
    | 3, 1 => 14%Q
    | _, _ => 0%Q
    end
  in
  (([0;1;2;3;4],[(0,2);(0,3);(1,2);(2,4);(3,1)]), c, 0, 4).
