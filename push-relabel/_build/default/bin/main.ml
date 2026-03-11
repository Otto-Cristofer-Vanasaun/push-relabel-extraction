[@@@ocaml.warning "-27-32-34-39"]

module NatH = struct
  type t = int
  let equal = Int.equal
  let hash (n: int) = Hashtbl.hash n
end

module EdgeH = struct
  type t = int * int
  let equal (e1 : t) (e2 : t) = (e1 = e2)
  let hash (e1 : t) = Hashtbl.hash e1
end

module EdgeT = struct
  type t = int * int
  let compare (e1 : t) (e2 : t) = compare e1 e2
end

(* module VertexMap' = Map.Make(Int)
module EdgeMap' = Map.Make(EdgeT) *)
module VertexMap' = Hashtbl.Make(NatH)
module EdgeMap' = Hashtbl.Make(EdgeH)
module ExcessMap' = Hashtbl.Make(NatH)
module VertexSet' = Set.Make(Int)
(* module VertexSet' = (nt) Queue.t *)
module EdgeSet' = Set.Make(EdgeT)

(* Extracted from the push-relabel algorithm proof in Rocq. *)


type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type comparison =
| Eq
| Lt
| Gt

(** val add : int -> int -> int **)

let rec add = (+)

(** val mul : int -> int -> int **)

let rec mul = ( * )



type reflect =
| ReflectT
| ReflectF

(** val gmin : ('a1 -> 'a1 -> comparison) -> 'a1 -> 'a1 -> 'a1 **)

let gmin cmp x y =
  match cmp x y with
  | Gt -> y
  | _ -> x

module Nat =
 struct
 end

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map = List.map

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | [] -> a0
  | b :: t0 -> fold_left f t0 (f a0 b)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| [] -> a0
| b :: t0 -> f b (fold_right f a0 t0)

module Pos =
 struct
  (** val succ : int -> int **)

  let rec succ = Stdlib.Int.succ

  (** val add : int -> int -> int **)

  let rec add = (+)

  (** val add_carry : int -> int -> int **)

  and add_carry x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> (fun p->1+2*p) (add_carry p q0))
        (fun q0 -> (fun p->2*p) (add_carry p q0))
        (fun _ -> (fun p->1+2*p) (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> (fun p->2*p) (add_carry p q0))
        (fun q0 -> (fun p->1+2*p) (add p q0))
        (fun _ -> (fun p->2*p) (succ p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> (fun p->1+2*p) (succ q0))
        (fun q0 -> (fun p->2*p) (succ q0))
        (fun _ -> (fun p->1+2*p) 1)
        y)
      x

  (** val pred_double : int -> int **)

  let rec pred_double x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> (fun p->1+2*p) ((fun p->2*p) p))
      (fun p -> (fun p->1+2*p) (pred_double p))
      (fun _ -> 1)
      x

  (** val mul : int -> int -> int **)

  let rec mul = ( * )

  (** val compare_cont : comparison -> int -> int -> comparison **)

  let rec compare_cont = fun c x y -> if x=y then c else if x<y then Lt else Gt

  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt
 end

module Z =
 struct
  (** val double : int -> int **)

  let double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun p -> ((fun p->2*p) p))
      (fun p -> (~-) ((fun p->2*p) p))
      x

  (** val succ_double : int -> int **)

  let succ_double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 1)
      (fun p -> ((fun p->1+2*p) p))
      (fun p -> (~-) (Pos.pred_double p))
      x

  (** val pred_double : int -> int **)

  let pred_double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> (~-) 1)
      (fun p -> (Pos.pred_double p))
      (fun p -> (~-) ((fun p->1+2*p) p))
      x

  (** val pos_sub : int -> int -> int **)

  let rec pos_sub x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> double (pos_sub p q0))
        (fun q0 -> succ_double (pos_sub p q0))
        (fun _ -> ((fun p->2*p) p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> pred_double (pos_sub p q0))
        (fun q0 -> double (pos_sub p q0))
        (fun _ -> (Pos.pred_double p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> (~-) ((fun p->2*p) q0))
        (fun q0 -> (~-) (Pos.pred_double q0))
        (fun _ -> 0)
        y)
      x

  (** val add : int -> int -> int **)

  let add = (+)

  (** val opp : int -> int **)

  let opp = (~-)

  (** val mul : int -> int -> int **)

  let mul = ( * )

  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt
 end

(** val z_lt_dec : int -> int -> bool **)

let z_lt_dec x y =
  match Z.compare x y with
  | Lt -> true
  | _ -> false

(** val z_lt_ge_dec : int -> int -> bool **)

let z_lt_ge_dec =
  z_lt_dec

(** val z_lt_le_dec : int -> int -> bool **)

let z_lt_le_dec =
  z_lt_ge_dec

(** val qnum : (int * int) -> int **)

let qnum = function
| (qnum0, _) -> qnum0

(** val qden : (int * int) -> int **)

let qden = function
| (_, qden0) -> qden0

(** val qcompare : (int * int) -> (int * int) -> comparison **)

let qcompare p q0 =
  Z.compare (Z.mul (qnum p) (qden q0)) (Z.mul (qnum q0) (qden p))

(** val qplus : (int * int) -> (int * int) -> (int * int) **)

let qplus x y =
  ((Z.add (Z.mul (qnum x) (qden y)) (Z.mul (qnum y) (qden x))),
    (Pos.mul (qden x) (qden y)))

(** val qopp : (int * int) -> (int * int) **)

let qopp x =
  ((Z.opp (qnum x)), (qden x))

(** val qminus : (int * int) -> (int * int) -> (int * int) **)

let qminus x y =
  qplus x (qopp y)

(** val qlt_le_dec : (int * int) -> (int * int) -> bool **)

let qlt_le_dec x y =
  z_lt_le_dec (Z.mul (qnum x) (qden y)) (Z.mul (qnum y) (qden x))

(** val qmin : (int * int) -> (int * int) -> (int * int) **)

let qmin =
  gmin qcompare

module type T =
 sig
  type coq_V

  val eqb : coq_V -> coq_V -> bool

  val equal : coq_V -> coq_V -> reflect
 end

module Coq_Nat =
 struct
  type coq_V = int

  (** val eqb : int -> int -> bool **)

  let eqb =
    (=)

  (** val equal : int -> int -> reflect **)

  let rec equal n y =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> ReflectT)
        (fun _ -> ReflectF)
        y)
      (fun n0 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> ReflectF)
        (fun n1 -> equal n0 n1)
        y)
      n
 end

module Tuple =
 functor (T__36:T) ->
 functor (U:T) ->
 struct
  type coq_V = T__36.coq_V * U.coq_V

  (** val eqb : (T__36.coq_V * U.coq_V) -> (T__36.coq_V * U.coq_V) -> bool **)

  let eqb pat pat0 =
    let (a, b) = pat in let (c, d) = pat0 in (&&) (T__36.eqb a c) (U.eqb b d)

  (** val equal : coq_V -> coq_V -> reflect **)

  let equal x y =
    let (v, v0) = x in
    let (v1, v2) = y in
    let r = T__36.equal v v1 in
    (match r with
     | ReflectT -> U.equal v0 v2
     | ReflectF -> ReflectF)
 end

module PR =
 functor (T__38:T) ->
 functor (Edge:sig
  type coq_V = T__38.coq_V * T__38.coq_V

  val eqb : coq_V -> coq_V -> bool

  val equal : coq_V -> coq_V -> reflect
 end) ->
 functor (EdgeMap:sig
  type 'e t

  val empty : 'a1 -> 'a1 t

  val replace : 'a1 -> Edge.coq_V -> 'a1 -> 'a1 t -> 'a1 t

  val find : 'a1 -> 'a1 t -> Edge.coq_V -> 'a1

  val update : 'a1 -> Edge.coq_V -> ('a1 -> 'a1) -> 'a1 t -> 'a1 t
 end) ->
 functor (VertexMap:sig
  type 'e t

  val empty : 'a1 -> 'a1 t

  val replace : 'a1 -> T__38.coq_V -> 'a1 -> 'a1 t -> 'a1 t

  val find : 'a1 -> 'a1 t -> T__38.coq_V -> 'a1

  val update : 'a1 -> T__38.coq_V -> ('a1 -> 'a1) -> 'a1 t -> 'a1 t
 end) ->
 functor (ExcessMap:sig
  type 'e t

  val empty : 'a1 -> 'a1 t

  val replace : 'a1 -> T__38.coq_V -> 'a1 -> 'a1 t -> 'a1 t

  val find : 'a1 -> 'a1 t -> T__38.coq_V -> 'a1

  val update : 'a1 -> T__38.coq_V -> ('a1 -> 'a1) -> 'a1 t -> 'a1 t
 end) ->
 functor (EdgeSet:sig
  type t

  val empty : t

  val add : Edge.coq_V -> t -> t

  val remove : Edge.coq_V -> t -> t

  val mem : Edge.coq_V -> t -> bool

  val choice : t -> (Edge.coq_V * t) option

  val filter : (Edge.coq_V -> bool) -> t -> t

  val to_list : t -> Edge.coq_V list

  val find_first : (Edge.coq_V -> bool) -> t -> Edge.coq_V option

  val size : t -> int
 end) ->
 functor (VertexSet:sig
  type t

  val empty : t

  val add : T__38.coq_V -> t -> t

  val remove : T__38.coq_V -> t -> t

  val mem : T__38.coq_V -> t -> bool

  val choice : t -> (T__38.coq_V * t) option

  val filter : (T__38.coq_V -> bool) -> t -> t

  val to_list : t -> T__38.coq_V list

  val find_first : (T__38.coq_V -> bool) -> t -> T__38.coq_V option

  val size : t -> int
 end) ->
 struct
  type coq_R = (int * int)

  type coq_Graph = VertexSet.t * EdgeSet.t

  type coq_FlowNet =
    ((coq_Graph * (T__38.coq_V -> T__38.coq_V ->
    coq_R)) * T__38.coq_V) * T__38.coq_V

  (** val nodes : coq_FlowNet -> VertexSet.t **)

  let nodes = function
  | (p, _) -> let (p0, _) = p in let (g, _) = p0 in let (vs, _) = g in vs

  (** val sink : coq_FlowNet -> T__38.coq_V **)

  let sink = function
  | (_, t0) -> t0

  (** val source : coq_FlowNet -> T__38.coq_V **)

  let source = function
  | (p, _) -> let (_, s) = p in s

  (** val coq_QLe : (int * int) -> (int * int) -> bool **)

  let coq_QLe a b =
    if qlt_le_dec b a then false else true

  (** val coq_QLt : (int * int) -> (int * int) -> bool **)

  let coq_QLt a b =
    if qlt_le_dec a b then true else false

  (** val coq_QInfLt : (int * int) option -> (int * int) option -> bool **)

  let coq_QInfLt x y =
    match x with
    | Some a -> (match y with
                 | Some b -> coq_QLt a b
                 | None -> true)
    | None -> false

  (** val coq_QLt_spec : (int * int) -> (int * int) -> reflect **)

  let coq_QLt_spec x y =
    let s = qlt_le_dec x y in if s then ReflectT else ReflectF

  (** val coq_QSumList : (int * int) list -> (int * int) **)

  let coq_QSumList =
    fold_right qplus (0, 1)

  (** val excess_update :
      (int * int) ExcessMap.t -> T__38.coq_V -> (int * int) -> T__38.coq_V ->
      coq_R ExcessMap.t **)

  let excess_update e u delta v =
    let old_excess_u = ExcessMap.find (0, 1) e u in
    let old_excess_v = ExcessMap.find (0, 1) e v in
    let new_map_u = ExcessMap.replace (0, 1) u (qminus old_excess_u delta) e
    in
    ExcessMap.replace (0, 1) v (qplus old_excess_v delta) new_map_u

  (** val max_flow : coq_FlowNet -> coq_R EdgeMap.t -> coq_R **)

  let max_flow fn f =
    let (p, t0) = fn in
    let (p0, _) = p in
    let (g, _) = p0 in
    let (vs, _) = g in
    qminus
      (coq_QSumList
        (map (fun v -> EdgeMap.find (0, 1) f (v, t0)) (VertexSet.to_list vs)))
      (coq_QSumList
        (map (fun v -> EdgeMap.find (0, 1) f (t0, v)) (VertexSet.to_list vs)))

  (** val res_cap :
      coq_FlowNet -> coq_R EdgeMap.t -> T__38.coq_V -> T__38.coq_V -> coq_R **)

  let res_cap fn f u v =
    let (p, _) = fn in
    let (p0, _) = p in
    let (g, c) = p0 in
    let (_, es) = g in
    if EdgeSet.mem (u, v) es
    then qminus (c u v) (EdgeMap.find (0, 1) f (u, v))
    else EdgeMap.find (0, 1) f (v, u)

  (** val coq_E : coq_FlowNet -> coq_R EdgeMap.t -> EdgeSet.t **)

  let coq_E fn f =
    let (p, _) = fn in
    let (p0, _) = p in
    let (g, c) = p0 in
    let (_, es) = g in
    EdgeSet.filter (fun pat ->
      let (u, v) = pat in coq_QLt (EdgeMap.find (0, 1) f (u, v)) (c u v)) es

  (** val res_net : coq_FlowNet -> coq_R EdgeMap.t -> coq_FlowNet **)

  let res_net fn f =
    let (p, t0) = fn in
    let (p0, s) = p in
    let (g, _) = p0 in
    let (vs, _) = g in ((((vs, (coq_E fn f)), (res_cap fn f)), s), t0)

  (** val push :
      ((((VertexSet.t * EdgeSet.t) * (T__38.coq_V -> T__38.coq_V ->
      coq_R)) * T__38.coq_V) * T__38.coq_V) -> coq_R EdgeMap.t -> (int * int)
      ExcessMap.t -> T__38.coq_V -> T__38.coq_V -> coq_R EdgeMap.t * coq_R
      ExcessMap.t **)

  let push fn f e u v =
    let (y, _) = fn in
    let (y0, _) = y in
    let (y1, _) = y0 in
    let (_, es) = y1 in
    let excess_value = ExcessMap.find (0, 1) e u in
    let delta = qmin excess_value (res_cap fn f u v) in
    let new_excessmap = excess_update e u delta v in
    if EdgeSet.mem (u, v) es
    then ((EdgeMap.update (0, 1) (u, v) (fun x -> qplus x delta) f),
           new_excessmap)
    else ((EdgeMap.update (0, 1) (v, u) (fun x -> qminus x delta) f),
           new_excessmap)

  (** val option_min : int option -> int -> int option **)

  let option_min x y =
    match x with
    | Some a -> Some (Stdlib.min a y)
    | None -> Some y

  (** val smallest_rank :
      int VertexMap.t -> T__38.coq_V list -> T__38.coq_V option ->
      T__38.coq_V option **)

  let rec smallest_rank l xs r =
    match xs with
    | [] -> r
    | v :: xs0 ->
      (match r with
       | Some r0 ->
         if (<=) (VertexMap.find 0 l r0) (VertexMap.find 0 l v)
         then smallest_rank l xs0 (Some r0)
         else smallest_rank l xs0 (Some v)
       | None -> smallest_rank l xs0 (Some v))

  (** val relabel_find :
      coq_FlowNet -> coq_R EdgeMap.t -> int VertexMap.t -> T__38.coq_V ->
      VertexSet.t -> T__38.coq_V option **)

  let relabel_find fn f l u vs =
    let fvs = VertexSet.filter (fun v -> coq_QLt (0, 1) (res_cap fn f u v)) vs
    in
    smallest_rank l (VertexSet.to_list fvs) None

  (** val relabel :
      ((((VertexSet.t * EdgeSet.t) * (T__38.coq_V -> T__38.coq_V ->
      coq_R)) * T__38.coq_V) * T__38.coq_V) -> coq_R EdgeMap.t -> int
      VertexMap.t -> T__38.coq_V -> int VertexMap.t option **)

  let relabel fn f l u =
    let (y, _) = fn in
    let (y0, _) = y in
    let (y1, _) = y0 in
    let (vs, _) = y1 in
    (match relabel_find fn f l u vs with
     | Some n ->
       Some
         (VertexMap.replace 0 u
           (add (Stdlib.Int.succ 0) (VertexMap.find 0 l n)) l)
     | None -> None)

  (** val find_push_node :
      ((((VertexSet.t * EdgeSet.t) * (T__38.coq_V -> T__38.coq_V ->
      coq_R)) * T__38.coq_V) * T__38.coq_V) -> coq_R EdgeMap.t -> int
      VertexMap.t -> T__38.coq_V -> VertexSet.t -> T__38.coq_V option **)

  let find_push_node fn f l u vs' =
    VertexSet.find_first (fun v ->
      (&&)
        ((=) (VertexMap.find 0 l u)
          (add (Stdlib.Int.succ 0) (VertexMap.find 0 l v)))
        (coq_QLt (0, 1) (res_cap fn f u v))) vs'

  (** val has_excess_not_sink :
      coq_FlowNet -> coq_R ExcessMap.t -> T__38.coq_V -> bool **)

  let has_excess_not_sink fn e v =
    let (p, t0) = fn in
    let (_, s) = p in
    if (||) (T__38.eqb v t0) (T__38.eqb v s)
    then false
    else coq_QLt (0, 1) (ExcessMap.find (0, 1) e v)

  type coq_Tr =
  | Init of (int * int) EdgeMap.t * coq_R ExcessMap.t * int VertexMap.t
     * VertexSet.t
  | Push of T__38.coq_V * T__38.coq_V * (int * int) EdgeMap.t
     * coq_R ExcessMap.t * VertexSet.t
  | Relabel of T__38.coq_V * int * int VertexMap.t
  | OutOfGas
  | RelabelFailed

  (** val coq_Tr_rect :
      ((int * int) EdgeMap.t -> coq_R ExcessMap.t -> int VertexMap.t ->
      VertexSet.t -> 'a1) -> (T__38.coq_V -> T__38.coq_V -> (int * int)
      EdgeMap.t -> coq_R ExcessMap.t -> VertexSet.t -> 'a1) -> (T__38.coq_V
      -> int -> int VertexMap.t -> 'a1) -> 'a1 -> 'a1 -> coq_Tr -> 'a1 **)

  let coq_Tr_rect f f0 f1 f2 f3 = function
  | Init (t1, t2, t3, t4) -> f t1 t2 t3 t4
  | Push (v, v0, t1, t2, t3) -> f0 v v0 t1 t2 t3
  | Relabel (v, n, t1) -> f1 v n t1
  | OutOfGas -> f2
  | RelabelFailed -> f3

  (** val coq_Tr_rec :
      ((int * int) EdgeMap.t -> coq_R ExcessMap.t -> int VertexMap.t ->
      VertexSet.t -> 'a1) -> (T__38.coq_V -> T__38.coq_V -> (int * int)
      EdgeMap.t -> coq_R ExcessMap.t -> VertexSet.t -> 'a1) -> (T__38.coq_V
      -> int -> int VertexMap.t -> 'a1) -> 'a1 -> 'a1 -> coq_Tr -> 'a1 **)

  let coq_Tr_rec f f0 f1 f2 f3 = function
  | Init (t1, t2, t3, t4) -> f t1 t2 t3 t4
  | Push (v, v0, t1, t2, t3) -> f0 v v0 t1 t2 t3
  | Relabel (v, n, t1) -> f1 v n t1
  | OutOfGas -> f2
  | RelabelFailed -> f3

  (** val gpr_helper_trace :
      ((((VertexSet.t * EdgeSet.t) * (T__38.coq_V -> T__38.coq_V ->
      coq_R)) * T__38.coq_V) * T__38.coq_V) -> coq_R EdgeMap.t -> (int * int)
      ExcessMap.t -> int VertexMap.t -> VertexSet.t -> int -> coq_Tr list ->
      ((int * int) EdgeMap.t * int VertexMap.t) option * coq_Tr list **)

  let rec gpr_helper_trace fn f e l ac g tr =
    let (y, _) = fn in
    let (y0, _) = y in
    let (y1, _) = y0 in
    let (vs, _) = y1 in
    ((fun fO fS n -> if n=0 then fO () else fS (n-1))
       (fun _ -> (None, (OutOfGas :: tr)))
       (fun g' ->
       match VertexSet.choice ac with
       | Some p ->
         let (u, ac') = p in
         (match find_push_node fn f l u vs with
          | Some v ->
            let (f', e') = push fn f e u v in
            let ac'0 =
              if coq_QLt (0, 1) (ExcessMap.find (0, 1) e' u) then ac else ac'
            in
            if has_excess_not_sink fn e' v
            then let ac'' = VertexSet.add v ac'0 in
                 gpr_helper_trace fn f' e' l ac'' g' ((Push (u, v, f', e',
                   ac'')) :: tr)
            else let ac'' = VertexSet.remove v ac'0 in
                 gpr_helper_trace fn f' e' l ac'' g' ((Push (u, v, f', e',
                   ac'0)) :: tr)
          | None ->
            (match relabel fn f l u with
             | Some l' ->
               gpr_helper_trace fn f e l' ac g' ((Relabel (u,
                 (VertexMap.find 0 l' u), l')) :: tr)
             | None -> (None, (RelabelFailed :: tr))))
       | None -> ((Some (f, l)), tr))
       g)

  (** val initial_push :
      ((((VertexSet.t * EdgeSet.t) * (T__38.coq_V -> T__38.coq_V ->
      coq_R)) * T__38.coq_V) * T__38.coq_V) -> coq_R ExcessMap.t ->
      ((int * int) EdgeMap.t * coq_R ExcessMap.t) * VertexSet.t **)

  let initial_push fn _ =
    let (y, _) = fn in
    let (y0, s) = y in
    let (y1, c) = y0 in
    let (_, es) = y1 in
    let es' =
      EdgeSet.to_list
        (EdgeSet.filter (fun pat -> let (u, _) = pat in T__38.eqb s u) es)
    in
    fold_left (fun pat pat0 ->
      let (y2, ac) = pat in
      let (f, e) = y2 in
      let (u, v) = pat0 in
      let f' = EdgeMap.replace (0, 1) (u, v) (c u v) f in
      let e' = ExcessMap.replace (0, 1) v (c u v) e in
      let ac0 = if has_excess_not_sink fn e v then VertexSet.add v ac else ac
      in
      ((f', e'), ac0)) es' (((EdgeMap.empty (0, 1)),
      (ExcessMap.empty (0, 1))), VertexSet.empty)

  (** val gpr_trace :
      coq_FlowNet -> ((int * int) EdgeMap.t * int VertexMap.t)
      option * coq_Tr list **)

  let gpr_trace fn = match fn with
  | (p, _) ->
    let (p0, s) = p in
    let (g, _) = p0 in
    let (vs, es) = g in
    let vs_size = VertexSet.size vs in
    let labels = VertexMap.replace 0 s vs_size (VertexMap.empty 0) in
    let bound = mul (mul (EdgeSet.size es) vs_size) vs_size in
    let (p1, active) = initial_push fn (ExcessMap.empty (0, 1)) in
    let (f, e) = p1 in
    gpr_helper_trace fn f e labels active bound ((Init (f, e, labels,
      active)) :: [])
 end

module Edge = Tuple(Coq_Nat)(Coq_Nat)

module EdgeMap =
 struct
  type 'e t = 'e EdgeMap'.t

  (** val empty : 'a1 -> 'a1 t **)

  let empty = fun _d -> EdgeMap'.create 1

  (** val remove : 'a1 -> Edge.coq_V -> 'a1 t -> 'a1 t **)

  let rec remove d v = function
  | [] -> []
  | p :: xs0 ->
    let (u, y) = p in
    if Edge.eqb v u then remove d v xs0 else (u, y) :: (remove d v xs0)

  (** val replace :
      'a1 -> Edge.coq_V -> 'a1 -> 'a1 t -> (Edge.coq_V * 'a1) list **)

  let rec replace = fun _d k v m -> EdgeMap'.replace m k v; m

  (** val update :
      'a1 -> Edge.coq_V -> ('a1 -> 'a1) -> 'a1 t -> (Edge.coq_V * 'a1) list **)

  let rec update = fun d k f m -> 
        let old = try EdgeMap'.find m k with Not_found -> d
        in EdgeMap'.replace m k (f old); m

  (** val find : 'a1 -> 'a1 t -> Edge.coq_V -> 'a1 **)

  let rec find = fun d k m -> 
    try EdgeMap'.find k m with Not_found -> d

  (** val coq_FindEmpty : __ **)

  let coq_FindEmpty =
    __

  (** val coq_FindUpdateEq : __ **)

  let coq_FindUpdateEq =
    __

  (** val coq_FindUpdateNeq : __ **)

  let coq_FindUpdateNeq =
    __

  (** val coq_FindReplaceEq : __ **)

  let coq_FindReplaceEq =
    __

  (** val coq_FindReplaceNeq : __ **)

  let coq_FindReplaceNeq =
    __
 end

module VertexMap =
 struct
  type 'e t = 'e VertexMap'.t

  (** val empty : 'a1 -> 'a1 t **)

  let empty = fun _d -> VertexMap'.create 1

  (** val remove : 'a1 -> Coq_Nat.coq_V -> 'a1 t -> 'a1 t **)

  let rec remove d v = function
  | [] -> []
  | p :: xs0 ->
    let (u, y) = p in
    if Coq_Nat.eqb v u then remove d v xs0 else (u, y) :: (remove d v xs0)

  (** val replace :
      'a1 -> Coq_Nat.coq_V -> 'a1 -> 'a1 t -> (Coq_Nat.coq_V * 'a1) list **)

  let rec replace = fun _d k v m -> VertexMap'.replace m k v; m

  (** val update :
      'a1 -> Coq_Nat.coq_V -> ('a1 -> 'a1) -> 'a1 t -> (Coq_Nat.coq_V * 'a1)
      list **)

  let rec update = fun d k f m -> 
        let old = try VertexMap'.find m k with Not_found -> d
        in VertexMap'.replace m k (f old); m

  (** val find : 'a1 -> 'a1 t -> Coq_Nat.coq_V -> 'a1 **)

  let rec find = fun d k m -> 
    try VertexMap'.find k m with Not_found -> d

  (** val coq_FindEmpty : __ **)

  let coq_FindEmpty =
    __

  (** val coq_FindUpdateEq : __ **)

  let coq_FindUpdateEq =
    __

  (** val coq_FindUpdateNeq : __ **)

  let coq_FindUpdateNeq =
    __

  (** val coq_FindReplaceEq : __ **)

  let coq_FindReplaceEq =
    __

  (** val coq_FindReplaceNeq : __ **)

  let coq_FindReplaceNeq =
    __
 end

module ExcessMap =
 struct
  type 'e t = 'e ExcessMap'.t

  (** val empty : 'a1 -> 'a1 t **)

  let empty = fun _d -> ExcessMap'.create 1

  (** val remove : 'a1 -> Coq_Nat.coq_V -> 'a1 t -> 'a1 t **)

  let rec remove d v = function
  | [] -> []
  | p :: xs0 ->
    let (u, y) = p in
    if Coq_Nat.eqb v u then remove d v xs0 else (u, y) :: (remove d v xs0)

  (** val replace :
      'a1 -> Coq_Nat.coq_V -> 'a1 -> 'a1 t -> (Coq_Nat.coq_V * 'a1) list **)

  let rec replace = fun _d k v m -> ExcessMap'.replace m k v; m

  (** val update :
      'a1 -> Coq_Nat.coq_V -> ('a1 -> 'a1) -> 'a1 t -> (Coq_Nat.coq_V * 'a1)
      list **)

  let rec update = fun d k f m -> 
        let old = try ExcessMap'.find m k with Not_found -> d
        in ExcessMap'.replace m k (f old); m

  (** val find : 'a1 -> 'a1 t -> Coq_Nat.coq_V -> 'a1 **)

  let rec find = fun d k m -> 
    try ExcessMap'.find k m with Not_found -> d

  (** val coq_FindEmpty : __ **)

  let coq_FindEmpty =
    __

  (** val coq_FindUpdateEq : __ **)

  let coq_FindUpdateEq =
    __

  (** val coq_FindUpdateNeq : __ **)

  let coq_FindUpdateNeq =
    __

  (** val coq_FindReplaceEq : __ **)

  let coq_FindReplaceEq =
    __

  (** val coq_FindReplaceNeq : __ **)

  let coq_FindReplaceNeq =
    __
 end

module EdgeSet =
 struct
  type t = EdgeSet'.t

  (** val empty : t **)

  let empty = EdgeSet'.empty

  (** val remove : Edge.coq_V -> Edge.coq_V list -> Edge.coq_V list **)

  let rec remove = EdgeSet'.remove

  (** val add : Edge.coq_V -> Edge.coq_V list -> Edge.coq_V list **)

  let add = EdgeSet'.add

  (** val to_list : t -> Edge.coq_V list **)

  let rec to_list = EdgeSet'.elements

  (** val mem : Edge.coq_V -> Edge.coq_V list -> bool **)

  let rec mem = EdgeSet'.mem

  (** val find_first :
      (Edge.coq_V -> bool) -> Edge.coq_V list -> Edge.coq_V option **)

  let rec find_first = EdgeSet'.find_first_opt

  (** val size : t -> int **)

  let size = EdgeSet'.cardinal

  (** val find_first_specSome : __ **)

  let find_first_specSome =
    __

  (** val find_first_specNone : __ **)

  let find_first_specNone =
    __

  (** val to_list_distinct : __ **)

  let to_list_distinct =
    __

  (** val to_list_in : __ **)

  let to_list_in =
    __

  (** val coq_MemEmpty : __ **)

  let coq_MemEmpty =
    __

  (** val coq_MemAddEq : __ **)

  let coq_MemAddEq =
    __

  (** val coq_MemRemoveEq : __ **)

  let coq_MemRemoveEq =
    __

  (** val coq_MemRemoveNeq : __ **)

  let coq_MemRemoveNeq =
    __

  (** val coq_MemAddNeq : __ **)

  let coq_MemAddNeq =
    __

  (** val choice : Edge.coq_V list -> (Edge.coq_V * t) option **)

  let choice = fun xs -> 
    match EdgeSet'.choose_opt xs with
    | None -> None
    | Some x -> Some (x, EdgeSet'.remove x xs)

  (** val choiceNone : __ **)

  let choiceNone =
    __

  (** val filter : (Edge.coq_V -> bool) -> t -> Edge.coq_V list **)

  let rec filter = EdgeSet'.filter

  (** val in_filter : __ **)

  let in_filter =
    __

  (** val filter_in : __ **)

  let filter_in =
    __

  (** val choiceSome : __ **)

  let choiceSome =
    __
 end

module VertexSet =
 struct
  type t = VertexSet'.t

  (** val empty : t **)

  let empty = VertexSet'.empty

  (** val remove :
      Coq_Nat.coq_V -> Coq_Nat.coq_V list -> Coq_Nat.coq_V list **)

  let rec remove = VertexSet'.remove

  (** val add : Coq_Nat.coq_V -> Coq_Nat.coq_V list -> Coq_Nat.coq_V list **)

  let add = VertexSet'.add

  (** val to_list : t -> Coq_Nat.coq_V list **)

  let rec to_list = VertexSet'.elements

  (** val mem : Coq_Nat.coq_V -> Coq_Nat.coq_V list -> bool **)

  let rec mem = VertexSet'.mem

  (** val find_first :
      (Coq_Nat.coq_V -> bool) -> Coq_Nat.coq_V list -> Coq_Nat.coq_V option **)

  let rec find_first = fun p xs -> Seq.find p (VertexSet'.to_seq xs)

  (** val size : t -> int **)

  let size = VertexSet'.cardinal

  (** val find_first_specSome : __ **)

  let find_first_specSome =
    __

  (** val find_first_specNone : __ **)

  let find_first_specNone =
    __

  (** val to_list_distinct : __ **)

  let to_list_distinct =
    __

  (** val to_list_in : __ **)

  let to_list_in =
    __

  (** val coq_MemEmpty : __ **)

  let coq_MemEmpty =
    __

  (** val coq_MemAddEq : __ **)

  let coq_MemAddEq =
    __

  (** val coq_MemRemoveEq : __ **)

  let coq_MemRemoveEq =
    __

  (** val coq_MemRemoveNeq : __ **)

  let coq_MemRemoveNeq =
    __

  (** val coq_MemAddNeq : __ **)

  let coq_MemAddNeq =
    __

  (** val choice : Coq_Nat.coq_V list -> (Coq_Nat.coq_V * t) option **)

  let choice = fun xs -> 
    match VertexSet'.choose_opt xs with
    | None -> None
    | Some x -> Some (x, VertexSet'.remove x xs)

  (** val choiceNone : __ **)

  let choiceNone =
    __

  (** val filter : (Coq_Nat.coq_V -> bool) -> t -> Coq_Nat.coq_V list **)

  let rec filter = VertexSet'.filter

  (** val in_filter : __ **)

  let in_filter =
    __

  (** val filter_in : __ **)

  let filter_in =
    __

  (** val choiceSome : __ **)

  let choiceSome =
    __
 end

module PRNat =
 PR(Coq_Nat)(Edge)(EdgeMap)(VertexMap)(ExcessMap)(EdgeSet)(VertexSet)

let fN1 =
  let c = fun (_n : int) (_m: int) -> ((10, 1):PRNat.coq_R) in
  (((((VertexSet'.of_list [0; 1]), EdgeSet'.of_list((0, 1) :: [])),
  c), 0), 1)

let fN2 =
  let c = fun x y ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> (0, 1))
        (fun n ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> (15, 1))
          (fun n0 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> (0, 1))
            (fun n1 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> (4, 1))
              (fun _ -> (0, 1))
              n1)
            n0)
          n)
        y)
      (fun n ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> (0, 1))
          (fun n0 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> (0, 1))
            (fun n1 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> (12, 1))
              (fun _ -> (0, 1))
              n1)
            n0)
          y)
        (fun n0 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> (0, 1))
            (fun n1 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> (0, 1))
              (fun n2 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ -> (0, 1))
                (fun n3 ->
                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ -> (3, 1))
                  (fun n4 ->
                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                    (fun _ -> (0, 1))
                    (fun n5 ->
                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                      (fun _ -> (7, 1))
                      (fun _ -> (0, 1))
                      n5)
                    n4)
                  n3)
                n2)
              n1)
            y)
          (fun n1 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> (0, 1))
              (fun n2 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ -> (0, 1))
                (fun n3 ->
                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ -> (0, 1))
                  (fun n4 ->
                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                    (fun _ -> (0, 1))
                    (fun n5 ->
                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                      (fun _ -> (10, 1))
                      (fun _ -> (0, 1))
                      n5)
                    n4)
                  n3)
                n2)
              y)
            (fun n2 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ -> (0, 1))
                (fun n3 ->
                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ -> (5, 1))
                  (fun n4 ->
                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                    (fun _ -> (0, 1))
                    (fun n5 ->
                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                      (fun _ -> (0, 1))
                      (fun n6 ->
                      (fun fO fS n -> if n=0 then fO () else fS (n-1))
                        (fun _ -> (0, 1))
                        (fun n7 ->
                        (fun fO fS n -> if n=0 then fO () else fS (n-1))
                          (fun _ -> (10, 1))
                          (fun _ -> (0, 1))
                          n7)
                        n6)
                      n5)
                    n4)
                  n3)
                y)
              (fun _ -> (0, 1))
              n2)
            n1)
          n0)
        n)
      x
  in
  ((((VertexSet'.of_list(0 :: (1 :: (2 :: (3 :: (4 :: (5 :: [])))))),
   EdgeSet'.of_list((0, 1) :: ((0, 3) :: ((1, 2) :: (2, 3) :: ((2, 5) :: ((3, 4) :: ((4, 1) :: ((4, 5) :: [])))))))),
    c), 0), 5)

let fN3 =
  let c = fun x y ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> (0, 1))
        (fun n ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> (((fun p->2*p) ((fun p->2*p) 1)), 1))
          (fun n0 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> (((fun p->2*p) 1), 1))
            (fun _ -> (0, 1))
            n0)
          n)
        y)
      (fun n ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> (0, 1))
          (fun n0 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> (0, 1))
            (fun n1 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> (0, 1))
              (fun n2 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ -> (((fun p->2*p) ((fun p->2*p) 1)), 1))
                (fun _ -> (0, 1))
                n2)
              n1)
            n0)
          y)
        (fun n0 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> (0, 1))
            (fun n1 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> (0, 1))
              (fun n2 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ -> (0, 1))
                (fun n3 ->
                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ -> (0, 1))
                  (fun n4 ->
                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                    (fun _ -> (((fun p->2*p) 1), 1))
                    (fun _ -> (0, 1))
                    n4)
                  n3)
                n2)
              n1)
            y)
          (fun n1 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> (0, 1))
              (fun n2 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ -> (0, 1))
                (fun n3 ->
                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ -> (0, 1))
                  (fun n4 ->
                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                    (fun _ -> (0, 1))
                    (fun n5 ->
                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                      (fun _ -> (0, 1))
                      (fun n6 ->
                      (fun fO fS n -> if n=0 then fO () else fS (n-1))
                        (fun _ -> (((fun p->2*p) ((fun p->2*p) 1)),
                        1))
                        (fun _ -> (0, 1))
                        n6)
                      n5)
                    n4)
                  n3)
                n2)
              y)
            (fun n2 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ -> (0, 1))
                (fun n3 ->
                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ -> (0, 1))
                  (fun n4 ->
                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                    (fun _ -> (0, 1))
                    (fun n5 ->
                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                      (fun _ -> (0, 1))
                      (fun n6 ->
                      (fun fO fS n -> if n=0 then fO () else fS (n-1))
                        (fun _ -> (0, 1))
                        (fun n7 ->
                        (fun fO fS n -> if n=0 then fO () else fS (n-1))
                          (fun _ -> (((fun p->2*p) 1), 1))
                          (fun _ -> (0, 1))
                          n7)
                        n6)
                      n5)
                    n4)
                  n3)
                y)
              (fun _ -> (0, 1))
              n2)
            n1)
          n0)
        n)
      x
  in
  ((((VertexSet'.of_list(0 :: ((Stdlib.Int.succ 0) :: ((Stdlib.Int.succ (Stdlib.Int.succ
  0)) :: ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
  0))) :: ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
  (Stdlib.Int.succ 0)))) :: ((Stdlib.Int.succ (Stdlib.Int.succ
  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))) :: [])))))), EdgeSet'.of_list((0,
  (Stdlib.Int.succ 0)) :: ((0, (Stdlib.Int.succ (Stdlib.Int.succ
  0))) :: (((Stdlib.Int.succ 0), (Stdlib.Int.succ (Stdlib.Int.succ
  (Stdlib.Int.succ 0)))) :: (((Stdlib.Int.succ 0), (Stdlib.Int.succ
  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
  0))))) :: (((Stdlib.Int.succ (Stdlib.Int.succ 0)), (Stdlib.Int.succ
  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
  0))))) :: (((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))),
  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
  (Stdlib.Int.succ 0)))))) :: (((Stdlib.Int.succ (Stdlib.Int.succ
  (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Stdlib.Int.succ (Stdlib.Int.succ
  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))) :: [])))))))),
  c), 0), (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
  (Stdlib.Int.succ 0))))))


let fN_excess =
  let c = fun x y ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> (0, 1))
        (fun n ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> (0, 1))
          (fun n0 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> (0, 1))
            (fun n1 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> (0, 1))
              (fun n2 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ -> (0, 1))
                (fun n3 ->
                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ -> (((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p)
                  ((fun p->2*p) 1)))), 1))
                  (fun _ -> (0, 1))
                  n3)
                n2)
              n1)
            n0)
          n)
        y)
      (fun n ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> (0, 1))
          (fun n0 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> (0, 1))
            (fun n1 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> (((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p)
              ((fun p->2*p) 1)))), 1))
              (fun n2 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ -> (0, 1))
                (fun n3 ->
                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ -> (((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p)
                  1))), 1))
                  (fun _ -> (0, 1))
                  n3)
                n2)
              n1)
            n0)
          y)
        (fun n0 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> (0, 1))
            (fun n1 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> (0, 1))
              (fun n2 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ -> (0, 1))
                (fun n3 ->
                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ -> (((fun p->2*p) 1), 1))
                  (fun _ -> (0, 1))
                  n3)
                n2)
              n1)
            y)
          (fun n1 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> (0, 1))
              (fun n2 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ -> (0, 1))
                (fun n3 ->
                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ -> (0, 1))
                  (fun n4 ->
                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                    (fun _ -> (0, 1))
                    (fun n5 ->
                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                      (fun _ -> (((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
                      1))), 1))
                      (fun n6 ->
                      (fun fO fS n -> if n=0 then fO () else fS (n-1))
                        (fun _ -> (0, 1))
                        (fun n7 ->
                        (fun fO fS n -> if n=0 then fO () else fS (n-1))
                          (fun _ -> (((fun p->2*p) 1), 1))
                          (fun _ -> (0, 1))
                          n7)
                        n6)
                      n5)
                    n4)
                  n3)
                n2)
              y)
            (fun n2 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ -> (0, 1))
                (fun n3 ->
                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ -> (0, 1))
                  (fun n4 ->
                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                    (fun _ -> (((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
                    ((fun p->2*p) 1)))), 1))
                    (fun _ -> (0, 1))
                    n4)
                  n3)
                y)
              (fun n3 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ ->
                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ -> (0, 1))
                  (fun n4 ->
                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                    (fun _ -> (((fun p->1+2*p) ((fun p->2*p) 1)),
                    1))
                    (fun n5 ->
                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                      (fun _ -> (((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
                      1))), 1))
                      (fun _ -> (0, 1))
                      n5)
                    n4)
                  y)
                (fun _ -> (0, 1))
                n3)
              n2)
            n1)
          n0)
        n)
      x
  in
  ((((VertexSet'.of_list(0 :: ((Stdlib.Int.succ 0) :: ((Stdlib.Int.succ (Stdlib.Int.succ
  0)) :: ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
  0))) :: ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
  (Stdlib.Int.succ 0)))) :: ((Stdlib.Int.succ (Stdlib.Int.succ
  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
  0))))) :: ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))) :: []))))))),
  EdgeSet'.of_list((0, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
  (Stdlib.Int.succ 0)))))) :: (((Stdlib.Int.succ 0), (Stdlib.Int.succ
  (Stdlib.Int.succ 0))) :: (((Stdlib.Int.succ 0), (Stdlib.Int.succ
  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
  0))))) :: (((Stdlib.Int.succ (Stdlib.Int.succ 0)), (Stdlib.Int.succ
  (Stdlib.Int.succ (Stdlib.Int.succ 0)))) :: (((Stdlib.Int.succ
  (Stdlib.Int.succ (Stdlib.Int.succ 0))), (Stdlib.Int.succ (Stdlib.Int.succ
  (Stdlib.Int.succ (Stdlib.Int.succ 0))))) :: (((Stdlib.Int.succ
  (Stdlib.Int.succ (Stdlib.Int.succ 0))), (Stdlib.Int.succ (Stdlib.Int.succ
  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
  0))))))) :: (((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
  (Stdlib.Int.succ 0)))), (Stdlib.Int.succ (Stdlib.Int.succ
  0))) :: (((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
  (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (Stdlib.Int.succ
  0)) :: (((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
  (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (Stdlib.Int.succ (Stdlib.Int.succ
  0))) :: [])))))))))), c), 0), (Stdlib.Int.succ (Stdlib.Int.succ
  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))

(** val fN_rand_test :
    (((int list * (int * int) list) * (int -> int ->
    (int * int))) * int) * int **)

let fN_rand_test =
  let c = fun x y ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> (0, 1))
        (fun n ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> (((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))),
          1))
          (fun n0 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> (((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p)
            ((fun p->2*p) 1)))), 1))
            (fun _ -> (0, 1))
            n0)
          n)
        y)
      (fun n ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> (0, 1))
          (fun n0 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> (0, 1))
            (fun n1 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> (((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
              ((fun p->2*p) 1)))), 1))
              (fun _ -> (0, 1))
              n1)
            n0)
          y)
        (fun _ -> (0, 1))
        n)
      x
  in
  ((((VertexSet'.of_list(0 :: ((Stdlib.Int.succ 0) :: ((Stdlib.Int.succ (Stdlib.Int.succ
  0)) :: []))), EdgeSet'.of_list((0, (Stdlib.Int.succ 0)) :: ((0, (Stdlib.Int.succ
  (Stdlib.Int.succ 0))) :: (((Stdlib.Int.succ 0), (Stdlib.Int.succ
  (Stdlib.Int.succ 0))) :: [])))), c), 0), (Stdlib.Int.succ (Stdlib.Int.succ
  0)))
(* Listidel põhineva implementatsiooni vastuste testimine
    (PRNat.excess fN2 [((0, 1), (15,1)); ((0, 3), (4,1));
      ((1, 2), (12,1));
      ((2, 3), (3,1));
      ((2, 5), (7,1));
      ((3, 4), (10,1));
      ((4, 1), (5,1));
      ((4, 5), (10,1))] 5)
      *)

(* Mappidel põhineva implementatsiooni vastuste testimine
  (PRNat.excess fN2 EdgeMap'.(empty |> add (0,1) (15,1) |> add (0,3) (4,1) |> add (1,2) (12,1)
    |> add (2,3) (3,1) |> add (2,5) (7,1) |> add (3,4) (10,1) |> add (4,1) (5,1) |> add (4,5) (10,1)) 5)
 *)

 (* Paisktabelitel põhineva implementatsiooni vastuste testimine
  (PRNat.excess fN2 
     (let t = EdgeMap'.create 10 in
     EdgeMap'.replace t (0,1) (10,1);
     EdgeMap'.replace t (0,3) (4,1);
     EdgeMap'.replace t (1,2) (10,1);
     EdgeMap'.replace t (2,3) (3,1);
     EdgeMap'.replace t (2,5) (7,1);
     EdgeMap'.replace t (3,4) (10,1);
     EdgeMap'.replace t (4,1) (0,1);
     EdgeMap'.replace t (4,5) (7,1); t) 5)
 *)

let time f x = 
    let t = Sys.time() in
    let fx = f x in
    Printf.printf "Ajakulu: %fms, " ((Sys.time() -. t) *. 1000.0);
  fx

(* PR ajakulu mõõtmine *)
let () =
    let _ = time PRNat.gpr_trace fN2 in
  ()

(* PR tulemuse väljaprintimine *)
(* let () =
    let (a,b) =
    (PRNat.max_flow fN3
    (let t = EdgeMap'.create 10 in 
     EdgeMap'.replace t (4, 5) (2, 1);
     EdgeMap'.replace t (3, 5) (4, 1);
     EdgeMap'.replace t (0, 1) (4, 1);
     EdgeMap'.replace t (2, 4) (2, 1);
     EdgeMap'.replace t (1, 3) (4, 1);
     EdgeMap'.replace t (0, 2) (2, 1); t))
     in
     Printf.printf "maksimaalne voog: %s\n" (Q.to_string (Q.of_ints a b)) *)


open Format 
let pp_edge fmt (a, b) = fprintf fmt "(%d, %d)" a b
let pp_Q fmt (a, b) = fprintf fmt "(%d, %d)" a b
let pp_edge_map key value fmt edgemap = 
  EdgeMap'.iter (fun k v -> 
    fprintf fmt "\n     EdgeMap'.replace t %a %a;" key k value v) edgemap
let pp_v fmt a = fprintf fmt "%d" a
let pp_excess_map key value fmt excessmap = 
  ExcessMap'.iter (fun k v -> 
    fprintf fmt "\n vertice: %a, excess: %a;" key k value v) excessmap

let pp_vert_map key value fmt verticemap = 
  VertexMap'.iter (fun k v -> 
    fprintf fmt "\n vertice: %a, label: %a;" key k value v) verticemap
let pp_list pp_elem fmt lst =
  fprintf fmt "%a"
    (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt "; ") pp_elem)
    lst

let pp_vert_set pp_elem fmt verticeset =
  VertexSet'.iter (fun elem ->
    fprintf fmt "%a " pp_elem elem) verticeset

(* Prindime ainult ühe korra lõppseisu *)
let pp_coq_Tr fmt = function
| PRNat.Init (_, _, _, verticeset) -> 
  (* fprintf fmt "init " *)
  fprintf fmt "init \nactive: [%a] " (pp_vert_set pp_v) verticeset
| PRNat.Push (u, v, edgemap, excessmap, verticeset) -> 
    (* fprintf fmt "push %a %a [%a] " pp_v u pp_v v (pp_vert_set pp_v) verticeset *)
    fprintf fmt "(let t = EdgeMap'.create 10 in %a t))\n" (pp_edge_map pp_edge pp_Q) edgemap
    (* fprintf fmt "(let t = EdgeMap'.create 10 in %a t))\n Excess: %a\n"
     (pp_edge_map pp_edge pp_Q) edgemap (pp_excess_map pp_v pp_Q) excessmap *)
| PRNat.Relabel (u, l, verticemap) -> 
  fprintf fmt "relabel %a %a " pp_v u pp_print_int l
  (* fprintf fmt "relabel %a %a %a" pp_v u pp_print_int l (pp_vert_map pp_v pp_print_int) verticemap *)
| PRNat.OutOfGas -> fprintf fmt "outofgas"
| PRNat.RelabelFailed -> fprintf fmt "relabelfailed"
(* | _ -> fprintf fmt "" *)

(* Kaarte kaalud algoritmi lõpus *)
let () =
  let gpr = PRNat.gpr_trace fN2 in
  Format.printf "%a" (pp_coq_Tr) (List.hd (snd gpr));

(* et Hashtbl initsialiseerida
  module NatH = struct
    type t = int
    let equal = Int.equal
    let hash = Hashtbl.hash
  end

  module EdgeH = struct
    type t = int * int
    let equal = (=)
    let hash = Hashtbl.hash
  end

  module VertexMap' = Hashtbl.Make(NatH)
  module EdgeMap' = Hashtbl.Make(EdgeH)

*)


