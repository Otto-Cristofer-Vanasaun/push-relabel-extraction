(* Auto-generated random flow network. *)
From Coq Require Import QArith List.
Import ListNotations.
Local Open Scope Q_scope.

Definition FN_spar : (list nat * list (nat * nat) * (nat -> nat -> Q) * nat * nat)%type :=
  let c := fun (x y : nat) =>
    match x, y with
    | 0, 1 => 5%Q
    | 0, 2 => 10%Q
    | 0, 3 => 2%Q
    | 1, 2 => 1%Q
    | 1, 3 => 1%Q
    | 2, 1 => 17%Q
    | 2, 3 => 3%Q
    | _, _ => 0%Q
    end
  in
  (([0;1;2;3],[(0,1);(0,2);(0,3);(1,2);(1,3);(2,1);(2,3)]), c, 0, 3).
