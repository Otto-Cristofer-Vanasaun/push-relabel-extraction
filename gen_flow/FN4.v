Definition FN4 : (list nat * list (nat * nat) * (nat -> nat -> Q) * nat * nat)%type :=
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
  (([0;1;2;3;4;5;6],[(0,5);(1,2);(1,4);(2,3);(3,4);(3,6);(4,2);(5,1);(5,2)]), c, 0, 6).
