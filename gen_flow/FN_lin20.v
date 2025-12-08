(* Auto-generated random flow network. *)
From Coq Require Import QArith List.
Import ListNotations.
Local Open Scope Q_scope.

Definition FN_lin20 : (list nat * list (nat * nat) * (nat -> nat -> Q) * nat * nat)%type :=
  let c := fun (x y : nat) =>
    match x, y with
    | 0, 7 => 24%Q
    | 1, 10 => 21%Q
    | 2, 4 => 8%Q
    | 3, 17 => 55%Q
    | 4, 9 => 83%Q
    | 5, 14 => 14%Q
    | 6, 13 => 16%Q
    | 7, 16 => 3%Q
    | 8, 1 => 54%Q
    | 9, 11 => 53%Q
    | 10, 18 => 65%Q
    | 11, 19 => 84%Q
    | 12, 6 => 52%Q
    | 13, 2 => 28%Q
    | 14, 15 => 70%Q
    | 15, 12 => 45%Q
    | 16, 8 => 64%Q
    | 17, 5 => 61%Q
    | 18, 3 => 3%Q
    | _, _ => 0%Q
    end
  in
  (([0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15;16;17;18;19],[(0,7);(1,10);(2,4);(3,17);(4,9);(5,14);(6,13);(7,16);(8,1);(9,11);(10,18);(11,19);(12,6);(13,2);(14,15);(15,12);(16,8);(17,5);(18,3)]), c, 0, 19).
