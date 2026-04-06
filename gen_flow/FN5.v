Definition FN5 : (list nat * list (nat * nat) * (nat -> nat -> Q) * nat * nat)%type :=
  let c := fun (x y : nat) =>
    match x, y with
    | 0, 1 => 8%Q
    | 0, 2 => 19%Q
    | 1, 2 => 18%Q
    | _, _ => 0%Q
    end
  in
  (([0;1;2],[(0,1);(0,2);(1,2)]), c, 0, 2).
