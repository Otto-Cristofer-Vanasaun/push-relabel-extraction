(* Erinevate ekstraheeritud arvude näited *)

(** val example_Z : int **)

(* let example_Z =
  ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1))))) *)


(** val example_Q2 : Q.t **)

(* let example_Q2 =
  (fun (n,d) -> Q.make (Z.of_int n) (Z.of_int d)) (((fun p->2*p) ((fun p->1+2*p) 1)), 1) *)


(** val example_R : PRNat.coq_R **)

(* let example_R =
  (fun (n,d) -> Q.of_ints n d) (((fun p->2*p) ((fun p->1+2*p) 1)), 1) *)


(** val example_Q2 : (int * int) **)

(* let example_Q2 =
  (fun (n,d) -> Q.of_ints n d) (((fun p->2*p) ((fun p->1+2*p) 1)), 1) *)