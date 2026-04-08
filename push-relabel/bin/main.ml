[@@@ocaml.warning "-32-34-39"] (* Eirame hoiatusi kasutamata muutujate kohta *)

(* Paisktabelite jaoks tarvilikud naturaalarvude ja kaarte definitsioonid *)
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

(* Vajalikud definitsioonid, mida vastavad struktuurid ekstraheeritud algoritmist kasutada saavad. *)
module VertexMap' = Hashtbl.Make(NatH)
module EdgeMap' = Hashtbl.Make(EdgeH)
module ExcessMap' = Hashtbl.Make(NatH)
module VertexSet' = Set.Make(Int)
module EdgeSet' = Set.Make(EdgeT)

(* Extracted from the push-relabel algorithm proof in Rocq. *)


type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

type comparison =
| Eq
| Lt
| Gt

module Coq__1 = struct
 (** val add : int -> int -> int **)

 let rec add = (+)
end
include Coq__1

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
  type mask =
  | IsNul
  | IsPos of int
  | IsNeg
 end

module Coq_Pos =
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

  type mask = Pos.mask =
  | IsNul
  | IsPos of int
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos 1
  | IsPos p -> IsPos ((fun p->1+2*p) p)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p -> IsPos ((fun p->2*p) p)
  | x0 -> x0

  (** val double_pred_mask : int -> mask **)

  let double_pred_mask x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> IsPos ((fun p->2*p) ((fun p->2*p) p)))
      (fun p -> IsPos ((fun p->2*p) (pred_double p)))
      (fun _ -> IsNul)
      x

  (** val sub_mask : int -> int -> mask **)

  let rec sub_mask x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> double_mask (sub_mask p q0))
        (fun q0 -> succ_double_mask (sub_mask p q0))
        (fun _ -> IsPos ((fun p->2*p) p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> succ_double_mask (sub_mask_carry p q0))
        (fun q0 -> double_mask (sub_mask p q0))
        (fun _ -> IsPos (pred_double p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> IsNeg)
        (fun _ -> IsNeg)
        (fun _ -> IsNul)
        y)
      x

  (** val sub_mask_carry : int -> int -> mask **)

  and sub_mask_carry x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> succ_double_mask (sub_mask_carry p q0))
        (fun q0 -> double_mask (sub_mask p q0))
        (fun _ -> IsPos (pred_double p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> double_mask (sub_mask_carry p q0))
        (fun q0 -> succ_double_mask (sub_mask_carry p q0))
        (fun _ -> double_pred_mask p)
        y)
      (fun _ -> IsNeg)
      x

  (** val sub : int -> int -> int **)

  let sub = fun n m -> Stdlib.max 1 (n-m)

  (** val mul : int -> int -> int **)

  let rec mul = ( * )

  (** val size_nat : int -> int **)

  let rec size_nat p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> Stdlib.Int.succ (size_nat p0))
      (fun p0 -> Stdlib.Int.succ (size_nat p0))
      (fun _ -> Stdlib.Int.succ 0)
      p

  (** val compare_cont : comparison -> int -> int -> comparison **)

  let rec compare_cont = fun c x y -> if x=y then c else if x<y then Lt else Gt

  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt

  (** val ggcdn : int -> int -> int -> int * (int * int) **)

  let rec ggcdn n a b =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> (1, (a, b)))
      (fun n0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun a' ->
        (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
          (fun b' ->
          match compare a' b' with
          | Eq -> (a, (1, 1))
          | Lt ->
            let (g, p) = ggcdn n0 (sub b' a') a in
            let (ba, aa) = p in (g, (aa, (add aa ((fun p->2*p) ba))))
          | Gt ->
            let (g, p) = ggcdn n0 (sub a' b') b in
            let (ab, bb) = p in (g, ((add bb ((fun p->2*p) ab)), bb)))
          (fun b0 ->
          let (g, p) = ggcdn n0 a b0 in
          let (aa, bb) = p in (g, (aa, ((fun p->2*p) bb))))
          (fun _ -> (1, (a, 1)))
          b)
        (fun a0 ->
        (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
          (fun _ ->
          let (g, p) = ggcdn n0 a0 b in
          let (aa, bb) = p in (g, (((fun p->2*p) aa), bb)))
          (fun b0 ->
          let (g, p) = ggcdn n0 a0 b0 in (((fun p->2*p) g), p))
          (fun _ -> (1, (a, 1)))
          b)
        (fun _ -> (1, (1, b)))
        a)
      n

  (** val ggcd : int -> int -> int * (int * int) **)

  let ggcd a b =
    ggcdn (Coq__1.add (size_nat a) (size_nat b)) a b
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
      (fun p -> (~-) (Coq_Pos.pred_double p))
      x

  (** val pred_double : int -> int **)

  let pred_double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> (~-) 1)
      (fun p -> (Coq_Pos.pred_double p))
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
        (fun _ -> (Coq_Pos.pred_double p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> (~-) ((fun p->2*p) q0))
        (fun q0 -> (~-) (Coq_Pos.pred_double q0))
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

  (** val sgn : int -> int **)

  let sgn z0 =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun _ -> 1)
      (fun _ -> (~-) 1)
      z0

  (** val abs : int -> int **)

  let abs = Stdlib.Int.abs

  (** val to_pos : int -> int **)

  let to_pos z0 =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 1)
      (fun p -> p)
      (fun _ -> 1)
      z0

  (** val ggcd : int -> int -> int * (int * int) **)

  let ggcd a b =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> ((abs b), (0, (sgn b))))
      (fun a0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> ((abs a), ((sgn a), 0)))
        (fun b0 ->
        let (g, p) = Coq_Pos.ggcd a0 b0 in let (aa, bb) = p in (g, (aa, bb)))
        (fun b0 ->
        let (g, p) = Coq_Pos.ggcd a0 b0 in
        let (aa, bb) = p in (g, (aa, ((~-) bb))))
        b)
      (fun a0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> ((abs a), ((sgn a), 0)))
        (fun b0 ->
        let (g, p) = Coq_Pos.ggcd a0 b0 in
        let (aa, bb) = p in (g, (((~-) aa), bb)))
        (fun b0 ->
        let (g, p) = Coq_Pos.ggcd a0 b0 in
        let (aa, bb) = p in (g, (((~-) aa), ((~-) bb))))
        b)
      a
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
    (Coq_Pos.mul (qden x) (qden y)))

(** val qopp : (int * int) -> (int * int) **)

let qopp x =
  ((Z.opp (qnum x)), (qden x))

(** val qminus : (int * int) -> (int * int) -> (int * int) **)

let qminus x y =
  qplus x (qopp y)

(** val qlt_le_dec : (int * int) -> (int * int) -> bool **)

let qlt_le_dec x y =
  z_lt_le_dec (Z.mul (qnum x) (qden y)) (Z.mul (qnum y) (qden x))

(** val qred : (int * int) -> (int * int) **)

let qred = function
| (q1, q2) -> let (r1, r2) = snd (Z.ggcd q1 q2) in (r1, (Z.to_pos r2))

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
 functor (T__6:T) ->
 functor (U:T) ->
 struct
  type coq_V = T__6.coq_V * U.coq_V

  (** val eqb : (T__6.coq_V * U.coq_V) -> (T__6.coq_V * U.coq_V) -> bool **)

  let eqb pat pat0 =
    let (a, b) = pat in let (c, d) = pat0 in (&&) (T__6.eqb a c) (U.eqb b d)

  (** val equal : coq_V -> coq_V -> reflect **)

  let equal x y =
    let (v, v0) = x in
    let (v1, v2) = y in
    let r = T__6.equal v v1 in
    (match r with
     | ReflectT -> U.equal v0 v2
     | ReflectF -> ReflectF)
 end

module PR =
 functor (T__8:T) ->
 functor (Edge:sig
  type coq_V = T__8.coq_V * T__8.coq_V

  val eqb : coq_V -> coq_V -> bool

  val equal : coq_V -> coq_V -> reflect
 end) ->
 functor (EdgeMap:sig
  type 'e t

  val empty : 'a1 -> 'a1 t

  val replace : 'a1 -> Edge.coq_V -> 'a1 -> 'a1 t -> 'a1 t

  val find : 'a1 -> 'a1 t -> Edge.coq_V -> 'a1

  val update : 'a1 -> Edge.coq_V -> ('a1 -> 'a1) -> 'a1 t -> 'a1 t

  val remove : 'a1 -> Edge.coq_V -> 'a1 t -> 'a1 t
 end) ->
 functor (VertexMap:sig
  type 'e t

  val empty : 'a1 -> 'a1 t

  val replace : 'a1 -> T__8.coq_V -> 'a1 -> 'a1 t -> 'a1 t

  val find : 'a1 -> 'a1 t -> T__8.coq_V -> 'a1

  val update : 'a1 -> T__8.coq_V -> ('a1 -> 'a1) -> 'a1 t -> 'a1 t

  val remove : 'a1 -> T__8.coq_V -> 'a1 t -> 'a1 t
 end) ->
 functor (ExcessMap:sig
  type 'e t

  val empty : 'a1 -> 'a1 t

  val replace : 'a1 -> T__8.coq_V -> 'a1 -> 'a1 t -> 'a1 t

  val find : 'a1 -> 'a1 t -> T__8.coq_V -> 'a1

  val update : 'a1 -> T__8.coq_V -> ('a1 -> 'a1) -> 'a1 t -> 'a1 t

  val remove : 'a1 -> T__8.coq_V -> 'a1 t -> 'a1 t
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

  val add : T__8.coq_V -> t -> t

  val remove : T__8.coq_V -> t -> t

  val mem : T__8.coq_V -> t -> bool

  val choice : t -> (T__8.coq_V * t) option

  val filter : (T__8.coq_V -> bool) -> t -> t

  val to_list : t -> T__8.coq_V list

  val find_first : (T__8.coq_V -> bool) -> t -> T__8.coq_V option

  val size : t -> int
 end) ->
 struct
  type coq_R = (int * int)

  type coq_Graph = VertexSet.t * EdgeSet.t

  type coq_FlowNet =
    ((coq_Graph * (T__8.coq_V -> T__8.coq_V ->
    coq_R)) * T__8.coq_V) * T__8.coq_V

  (** val nodes : coq_FlowNet -> VertexSet.t **)

  let nodes = function
  | (p, _) -> let (p0, _) = p in let (g, _) = p0 in let (vs, _) = g in vs

  (** val sink : coq_FlowNet -> T__8.coq_V **)

  let sink = function
  | (_, t0) -> t0

  (** val source : coq_FlowNet -> T__8.coq_V **)

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

  (** val excess : coq_FlowNet -> coq_R EdgeMap.t -> T__8.coq_V -> coq_R **)

  let excess fn f u =
    let (p, _) = fn in
    let (p0, _) = p in
    let (g, _) = p0 in
    let (vs, _) = g in
    qred
      (qminus
        (coq_QSumList
          (map (fun v -> EdgeMap.find (0, 1) f (v, u)) (VertexSet.to_list vs)))
        (coq_QSumList
          (map (fun v -> EdgeMap.find (0, 1) f (u, v)) (VertexSet.to_list vs))))

  (** val excess_update :
      coq_R ExcessMap.t -> T__8.coq_V -> (int * int) -> T__8.coq_V -> coq_R
      ExcessMap.t **)

  let excess_update e u delta v =
    let new_map_u =
      ExcessMap.update (0, 1) u (fun x -> qred (qminus x delta)) e
    in
    ExcessMap.update (0, 1) v (fun x -> qred (qplus x delta)) new_map_u

  (** val res_cap :
      coq_FlowNet -> coq_R EdgeMap.t -> T__8.coq_V -> T__8.coq_V -> coq_R **)

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
      ((((VertexSet.t * EdgeSet.t) * (T__8.coq_V -> T__8.coq_V ->
      coq_R)) * T__8.coq_V) * T__8.coq_V) -> coq_R EdgeMap.t -> (int * int)
      ExcessMap.t -> T__8.coq_V -> T__8.coq_V -> coq_R EdgeMap.t * coq_R
      ExcessMap.t **)

  let push fn f e u v =
    let (y, _) = fn in
    let (y0, _) = y in
    let (y1, _) = y0 in
    let (_, es) = y1 in
    let delta = qmin (ExcessMap.find (0, 1) e u) (res_cap fn f u v) in
    let new_excessmap = excess_update e u delta v in
    if EdgeSet.mem (u, v) es
    then ((EdgeMap.update (0, 1) (u, v) (fun x -> qred (qplus x delta)) f),
           new_excessmap)
    else ((EdgeMap.update (0, 1) (v, u) (fun x -> qred (qminus x delta)) f),
           new_excessmap)

  (** val smallest_rank :
      int VertexMap.t -> T__8.coq_V list -> T__8.coq_V option -> T__8.coq_V
      option **)

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
      coq_FlowNet -> coq_R EdgeMap.t -> int VertexMap.t -> T__8.coq_V ->
      VertexSet.t -> T__8.coq_V option **)

  let relabel_find fn f l u vs =
    let fvs = VertexSet.filter (fun v -> coq_QLt (0, 1) (res_cap fn f u v)) vs
    in
    smallest_rank l (VertexSet.to_list fvs) None

  (** val relabel :
      ((((VertexSet.t * EdgeSet.t) * (T__8.coq_V -> T__8.coq_V ->
      coq_R)) * T__8.coq_V) * T__8.coq_V) -> coq_R EdgeMap.t -> int
      VertexMap.t -> T__8.coq_V -> int VertexMap.t option **)

  let relabel fn f l u =
    let (y, _) = fn in
    let (y0, _) = y in
    let (y1, _) = y0 in
    let (vs, _) = y1 in
    (match relabel_find fn f l u vs with
     | Some v ->
       Some
         (VertexMap.replace 0 u
           (add (Stdlib.Int.succ 0) (VertexMap.find 0 l v)) l)
     | None -> None)

  (** val find_push_node :
      ((((VertexSet.t * EdgeSet.t) * (T__8.coq_V -> T__8.coq_V ->
      coq_R)) * T__8.coq_V) * T__8.coq_V) -> coq_R EdgeMap.t -> int
      VertexMap.t -> T__8.coq_V -> VertexSet.t -> T__8.coq_V option **)

  let find_push_node fn f l u vs' =
    VertexSet.find_first (fun v ->
      (&&)
        ((=) (VertexMap.find 0 l u)
          (add (Stdlib.Int.succ 0) (VertexMap.find 0 l v)))
        (coq_QLt (0, 1) (res_cap fn f u v))) vs'

  (** val has_excess_not_sink :
      coq_FlowNet -> coq_R ExcessMap.t -> T__8.coq_V -> bool **)

  let has_excess_not_sink fn e v =
    let (p, t0) = fn in
    let (_, s) = p in
    if (||) (T__8.eqb v t0) (T__8.eqb v s)
    then false
    else coq_QLt (0, 1) (ExcessMap.find (0, 1) e v)

  (** val gpr_helper :
      ((((VertexSet.t * EdgeSet.t) * (T__8.coq_V -> T__8.coq_V ->
      coq_R)) * T__8.coq_V) * T__8.coq_V) -> coq_R EdgeMap.t -> (int * int)
      ExcessMap.t -> int VertexMap.t -> VertexSet.t -> int -> ((coq_R
      EdgeMap.t * coq_R ExcessMap.t) * int VertexMap.t) option **)

  let rec gpr_helper fn f e l ac g =
    let (y, _) = fn in
    let (y0, _) = y in
    let (y1, _) = y0 in
    let (vs, _) = y1 in
    ((fun fO fS n -> if n=0 then fO () else fS (n-1))
       (fun _ -> None)
       (fun g' ->
       match VertexSet.choice ac with
       | Some p ->
         let (u, ac') = p in
         (match find_push_node fn f l u vs with
          | Some v ->
            let (f', e') = push fn f e u v in
            let ac'0 =
              if coq_QLt (0, 1) (ExcessMap.find (qred (0, 1)) e' u)
              then ac
              else ac'
            in
            if has_excess_not_sink fn e' v
            then let ac'' = VertexSet.add v ac'0 in
                 gpr_helper fn f' e' l ac'' g'
            else let ac'' = VertexSet.remove v ac'0 in
                 gpr_helper fn f' e' l ac'' g'
          | None ->
            (match relabel fn f l u with
             | Some l' -> gpr_helper fn f e l' ac g'
             | None -> None))
       | None -> Some ((f, e), l))
       g)

  (** val initial_push_step :
      ((((VertexSet.t * EdgeSet.t) * (T__8.coq_V -> T__8.coq_V ->
      (int * int))) * T__8.coq_V) * T__8.coq_V) -> ((coq_R
      EdgeMap.t * (int * int) ExcessMap.t) * VertexSet.t) ->
      (T__8.coq_V * T__8.coq_V) -> (coq_R EdgeMap.t * (int * int)
      ExcessMap.t) * VertexSet.t **)

  let initial_push_step fn pat pat0 =
    let (y, ac) = pat in
    let (f, e) = y in
    let (u, v) = pat0 in
    let (y0, _) = fn in
    let (y1, _) = y0 in
    let (_, c) = y1 in
    let f' = EdgeMap.update (0, 1) (u, v) (fun x -> qred (qplus x (c u v))) f
    in
    let e' =
      ExcessMap.update (0, 1) v (fun x -> qred (qplus x (c u v)))
        (ExcessMap.update (0, 1) u (fun x -> qred (qminus x (c u v))) e)
    in
    let ac' = if has_excess_not_sink fn e' v then VertexSet.add v ac else ac
    in
    ((f', e'), ac')

  (** val initial_push :
      ((((VertexSet.t * EdgeSet.t) * (T__8.coq_V -> T__8.coq_V ->
      (int * int))) * T__8.coq_V) * T__8.coq_V) -> (coq_R EdgeMap.t * coq_R
      ExcessMap.t) * VertexSet.t **)

  let initial_push fn = match fn with
  | (y, _) ->
    let (y0, s) = y in
    let (y1, _) = y0 in
    let (_, es) = y1 in
    let es' =
      EdgeSet.to_list
        (EdgeSet.filter (fun pat -> let (u, _) = pat in T__8.eqb s u) es)
    in
    let start_st = (((EdgeMap.empty (0, 1)), (ExcessMap.empty (0, 1))),
      VertexSet.empty)
    in
    fold_left (initial_push_step fn) es' start_st

  (** val gpr :
      coq_FlowNet -> ((coq_R EdgeMap.t * coq_R ExcessMap.t) * int
      VertexMap.t) option **)

  let gpr fn = match fn with
  | (p, _) ->
    let (p0, s) = p in
    let (g, _) = p0 in
    let (vs, es) = g in
    let vs_size = VertexSet.size vs in
    let labels = VertexMap.replace 0 s vs_size (VertexMap.empty 0) in
    let bound = mul (mul (EdgeSet.size es) vs_size) vs_size in
    let (p1, active) = initial_push fn in
    let (f, e) = p1 in gpr_helper fn f e labels active bound

  (** val excess_loop :
      (int * int) EdgeMap.t -> T__8.coq_V -> T__8.coq_V list -> (int * int) **)

  let excess_loop f u xs =
    qminus (coq_QSumList (map (fun v -> EdgeMap.find (0, 1) f (v, u)) xs))
      (coq_QSumList (map (fun v -> EdgeMap.find (0, 1) f (u, v)) xs))

  type coq_Tr =
  | Init of coq_R EdgeMap.t * coq_R ExcessMap.t * int VertexMap.t
     * VertexSet.t
  | Push of T__8.coq_V * T__8.coq_V * coq_R EdgeMap.t * coq_R ExcessMap.t
     * VertexSet.t
  | Relabel of T__8.coq_V * int * int VertexMap.t
  | OutOfGas
  | RelabelFailed

  (** val coq_Tr_rect :
      (coq_R EdgeMap.t -> coq_R ExcessMap.t -> int VertexMap.t -> VertexSet.t
      -> 'a1) -> (T__8.coq_V -> T__8.coq_V -> coq_R EdgeMap.t -> coq_R
      ExcessMap.t -> VertexSet.t -> 'a1) -> (T__8.coq_V -> int -> int
      VertexMap.t -> 'a1) -> 'a1 -> 'a1 -> coq_Tr -> 'a1 **)

  let coq_Tr_rect f f0 f1 f2 f3 = function
  | Init (t1, t2, t3, t4) -> f t1 t2 t3 t4
  | Push (v, v0, t1, t2, t3) -> f0 v v0 t1 t2 t3
  | Relabel (v, n, t1) -> f1 v n t1
  | OutOfGas -> f2
  | RelabelFailed -> f3

  (** val coq_Tr_rec :
      (coq_R EdgeMap.t -> coq_R ExcessMap.t -> int VertexMap.t -> VertexSet.t
      -> 'a1) -> (T__8.coq_V -> T__8.coq_V -> coq_R EdgeMap.t -> coq_R
      ExcessMap.t -> VertexSet.t -> 'a1) -> (T__8.coq_V -> int -> int
      VertexMap.t -> 'a1) -> 'a1 -> 'a1 -> coq_Tr -> 'a1 **)

  let coq_Tr_rec f f0 f1 f2 f3 = function
  | Init (t1, t2, t3, t4) -> f t1 t2 t3 t4
  | Push (v, v0, t1, t2, t3) -> f0 v v0 t1 t2 t3
  | Relabel (v, n, t1) -> f1 v n t1
  | OutOfGas -> f2
  | RelabelFailed -> f3

  (** val gpr_helper_trace :
      ((((VertexSet.t * EdgeSet.t) * (T__8.coq_V -> T__8.coq_V ->
      coq_R)) * T__8.coq_V) * T__8.coq_V) -> coq_R EdgeMap.t -> (int * int)
      ExcessMap.t -> int VertexMap.t -> VertexSet.t -> int -> coq_Tr list ->
      ((coq_R EdgeMap.t * coq_R ExcessMap.t) * int VertexMap.t)
      option * coq_Tr list **)

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
              if coq_QLt (0, 1) (ExcessMap.find (qred (0, 1)) e' u)
              then ac
              else ac'
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
       | None -> ((Some ((f, e), l)), tr))
       g)

  (** val gpr_trace :
      coq_FlowNet -> ((coq_R EdgeMap.t * coq_R ExcessMap.t) * int
      VertexMap.t) option * coq_Tr list **)

  let gpr_trace fn = match fn with
  | (p, _) ->
    let (p0, s) = p in
    let (g, _) = p0 in
    let (vs, es) = g in
    let vs_size = VertexSet.size vs in
    let labels = VertexMap.replace 0 s vs_size (VertexMap.empty 0) in
    let bound = mul (mul (EdgeSet.size es) vs_size) vs_size in
    let (p1, active) = initial_push fn in
    let (f, e) = p1 in
    gpr_helper_trace fn f e labels active bound ((Init (f, e, labels,
      active)) :: [])
 end

module Edge = Tuple(Coq_Nat)(Coq_Nat)

module EdgeMap =
 struct
  type 'e t = 'e EdgeMap'.t

  type eq_nat = __

  type eq_rat = __

  (** val empty : 'a1 -> 'a1 t **)

  let empty = fun _d -> EdgeMap'.create 1

  (** val remove : 'a1 -> Edge.coq_V -> 'a1 t -> 'a1 t **)

  let rec remove = fun d k m -> EdgeMap'.replace m k d; m

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

  type eq_nat = __

  type eq_rat = __

  (** val empty : 'a1 -> 'a1 t **)

  let empty = fun _d -> VertexMap'.create 1

  (** val remove : 'a1 -> Coq_Nat.coq_V -> 'a1 t -> 'a1 t **)

  let rec remove = fun d k m -> VertexMap'.replace m k d; m

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

  type eq_nat = __

  type eq_rat = __

  (** val empty : 'a1 -> 'a1 t **)

  let empty = fun _d -> ExcessMap'.create 1

  (** val remove : 'a1 -> Coq_Nat.coq_V -> 'a1 t -> 'a1 t **)

  let rec remove = fun d k m -> ExcessMap'.replace m k d; m

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


(* Näidisvõrgud *)
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

let fN4 =
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

let fN5 =
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

(* PR tulemuse väljaprintimine *)

open Format 
let pp_edge fmt (a, b) = fprintf fmt "(%d, %d)" a b
let pp_Q fmt (a, b) = fprintf fmt "(%d, %d)" a b
let pp_edge_map key value fmt edgemap = 
  EdgeMap'.iter (fun k v -> 
    fprintf fmt "Edge: %a, flow: %a\n" key k value v) edgemap
let pp_v fmt a = fprintf fmt "%d" a
let pp_excess_map key value fmt excessmap = 
  ExcessMap'.iter (fun k v -> 
    fprintf fmt "Vertex: %a, excess: %a\n" key k value v) excessmap

let pp_vert_map key value fmt verticemap = 
  VertexMap'.iter (fun k v -> 
    fprintf fmt "Vertex: %a, label: %a\n" key k value v) verticemap

let pp_triple fmt ((edgemap, excessmap), vertexmap) =
  fprintf fmt "%a\n%a\n%a" 
  (pp_edge_map pp_edge pp_Q) edgemap
  (pp_vert_map pp_v pp_print_int) vertexmap
  (pp_excess_map pp_v pp_Q) excessmap

let pp_formatter fmt = function
| x -> fprintf fmt "%a\n" (pp_print_option pp_triple) x

(* Kaarte vood, tippude kõrgused ja ülejäägid algoritmi lõpus *)
let () =
  let gpr = PRNat.gpr fN2 in
  Format.printf "%a" (pp_formatter) gpr;

Format.close_box ()

(* PR ajakulu mõõtmine *)
let time f x = 
    let t = Sys.time() in
    let fx = f x in
    Printf.printf "Ajakulu: %fms\n" ((Sys.time() -. t) *. 1000.0);
  fx


  
let () =
    let _ = time PRNat.gpr fN2 in
  ()