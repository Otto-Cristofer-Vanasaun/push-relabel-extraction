[@@@ocaml.warning "-32-34-39"]

(** val length : 'a1 list -> int **)

let rec length = function
| [] -> 0
| _ :: l' -> Stdlib.Int.succ (length l')

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

let rec map f = function
| [] -> []
| a :: t0 -> (f a) :: (map f t0)

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

module Map =
 functor (T__1:T) ->
 struct
  type 'e t = (T__1.coq_V * 'e) list

  (** val empty : 'a1 -> 'a1 t **)

  let empty _ =
    []

  (** val remove : 'a1 -> T__1.coq_V -> 'a1 t -> 'a1 t **)

  let rec remove d v = function
  | [] -> []
  | p :: xs0 ->
    let (u, y) = p in
    if T__1.eqb v u then remove d v xs0 else (u, y) :: (remove d v xs0)

  (** val replace :
      'a1 -> T__1.coq_V -> 'a1 -> 'a1 t -> (T__1.coq_V * 'a1) list **)

  let rec replace d v x = function
  | [] -> (v, x) :: []
  | p :: xs0 ->
    let (u, y) = p in
    if T__1.eqb v u
    then (u, x) :: (remove d v xs0)
    else (u, y) :: (replace d v x xs0)

  (** val update :
      'a1 -> T__1.coq_V -> ('a1 -> 'a1) -> 'a1 t -> (T__1.coq_V * 'a1) list **)

  let rec update d v f = function
  | [] -> (v, (f d)) :: []
  | p :: xs0 ->
    let (u, y) = p in
    if T__1.eqb v u
    then (u, (f y)) :: (remove d v xs0)
    else (u, y) :: (update d v f xs0)

  (** val find : 'a1 -> 'a1 t -> T__1.coq_V -> 'a1 **)

  let rec find d xs v =
    match xs with
    | [] -> d
    | p :: xs0 -> let (u, y) = p in if T__1.eqb v u then y else find d xs0 v
 end

module MkSet =
 functor (T__3:T) ->
 struct
  type t = T__3.coq_V list

  (** val empty : t **)

  let empty =
    []

  (** val remove : T__3.coq_V -> T__3.coq_V list -> T__3.coq_V list **)

  let rec remove v = function
  | [] -> []
  | v' :: s0 -> if T__3.eqb v v' then remove v s0 else v' :: (remove v s0)

  (** val add : T__3.coq_V -> T__3.coq_V list -> T__3.coq_V list **)

  let add v s =
    v :: (remove v s)

  (** val mem : T__3.coq_V -> T__3.coq_V list -> bool **)

  let rec mem v = function
  | [] -> false
  | v' :: s0 -> if T__3.eqb v v' then true else mem v s0

  (** val choice : T__3.coq_V list -> (T__3.coq_V * t) option **)

  let choice = function
  | [] -> None
  | v :: s0 -> Some (v, s0)

  (** val filter : (T__3.coq_V -> bool) -> t -> T__3.coq_V list **)

  let rec filter p = function
  | [] -> []
  | v :: s -> if p v then v :: (filter p s) else filter p s

  (** val fold_left : ('a1 -> T__3.coq_V -> 'a1) -> t -> 'a1 -> 'a1 **)

  let fold_left =
    fold_left
 end

module Tuple =
 functor (T__4:T) ->
 functor (U:T) ->
 struct
  type coq_V = T__4.coq_V * U.coq_V

  (** val eqb : (T__4.coq_V * U.coq_V) -> (T__4.coq_V * U.coq_V) -> bool **)

  let eqb pat pat0 =
    let (a, b) = pat in let (c, d) = pat0 in (&&) (T__4.eqb a c) (U.eqb b d)

  (** val equal : coq_V -> coq_V -> reflect **)

  let equal x y =
    let (v, v0) = x in
    let (v1, v2) = y in
    let r = T__4.equal v v1 in
    (match r with
     | ReflectT -> U.equal v0 v2
     | ReflectF -> ReflectF)
 end

module PR =
 functor (T__6:T) ->
 struct
  type coq_R = (int * int)

  module Edge = Tuple(T__6)(T__6)

  module EMap = Map(Edge)

  module VSet = MkSet(T__6)

  module ESet = MkSet(Edge)

  type coq_Graph = VSet.t * ESet.t

  type coq_FlowNet =
    ((coq_Graph * (T__6.coq_V -> T__6.coq_V ->
    coq_R)) * T__6.coq_V) * T__6.coq_V

  (** val nodes : coq_FlowNet -> VSet.t **)

  let nodes = function
  | (p, _) -> let (p0, _) = p in let (g, _) = p0 in let (vs, _) = g in vs

  (** val sink : coq_FlowNet -> T__6.coq_V **)

  let sink = function
  | (_, t0) -> t0

  (** val source : coq_FlowNet -> T__6.coq_V **)

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

  (** val excess : coq_FlowNet -> coq_R EMap.t -> T__6.coq_V -> coq_R **)

  let excess fn f u =
    let (p, _) = fn in
    let (p0, _) = p in
    let (g, _) = p0 in
    let (vs, _) = g in
    qminus (coq_QSumList (map (fun v -> EMap.find (0, 1) f (v, u)) vs))
      (coq_QSumList (map (fun v -> EMap.find (0, 1) f (u, v)) vs))

  (** val res_cap :
      coq_FlowNet -> coq_R EMap.t -> T__6.coq_V -> T__6.coq_V -> coq_R **)

  let res_cap fn f u v =
    let (p, _) = fn in
    let (p0, _) = p in
    let (g, c) = p0 in
    let (_, es) = g in
    if ESet.mem (u, v) es
    then qminus (c u v) (EMap.find (0, 1) f (u, v))
    else EMap.find (0, 1) f (v, u)

  (** val coq_E : coq_FlowNet -> coq_R EMap.t -> Edge.coq_V list **)

  let coq_E fn f =
    let (p, _) = fn in
    let (p0, _) = p in
    let (g, c) = p0 in
    let (_, es) = g in
    ESet.filter (fun pat ->
      let (u, v) = pat in coq_QLt (EMap.find (0, 1) f (u, v)) (c u v)) es

  (** val res_net : coq_FlowNet -> coq_R EMap.t -> coq_FlowNet **)

  let res_net fn f =
    let (p, t0) = fn in
    let (p0, s) = p in
    let (g, _) = p0 in
    let (vs, _) = g in ((((vs, (coq_E fn f)), (res_cap fn f)), s), t0)

  module NMap = Map(T__6)

  (** val push :
      ((((VSet.t * ESet.t) * (T__6.coq_V -> T__6.coq_V ->
      coq_R)) * T__6.coq_V) * T__6.coq_V) -> coq_R EMap.t -> T__6.coq_V ->
      T__6.coq_V -> coq_R EMap.t **)

  let push fn f u v =
    let (y, _) = fn in
    let (y0, _) = y in
    let (y1, _) = y0 in
    let (_, es) = y1 in
    let delta = qmin (excess fn f u) (res_cap fn f u v) in
    if ESet.mem (u, v) es
    then EMap.update (0, 1) (u, v) (fun x -> qplus x delta) f
    else EMap.update (0, 1) (v, u) (fun x -> qminus x delta) f

  (** val option_min : int option -> int -> int option **)

  let option_min x y =
    match x with
    | Some a -> Some (Stdlib.min a y)
    | None -> Some y

  (** val relabel_find :
      coq_FlowNet -> coq_R EMap.t -> int NMap.t -> T__6.coq_V -> VSet.t ->
      T__6.coq_V option **)

  let relabel_find fn f l u vs =
    let fvs = VSet.filter (fun v -> coq_QLt (0, 1) (res_cap fn f u v)) vs in
    VSet.fold_left (fun r v ->
      match r with
      | Some r0 ->
        if (<=) (NMap.find 0 l r0) (NMap.find 0 l v) then Some r0 else Some v
      | None -> Some v) fvs None

  (** val relabel :
      ((((VSet.t * ESet.t) * (T__6.coq_V -> T__6.coq_V ->
      coq_R)) * T__6.coq_V) * T__6.coq_V) -> coq_R EMap.t -> int NMap.t ->
      T__6.coq_V -> int NMap.t option **)

  let relabel fn f l u =
    let (y, _) = fn in
    let (y0, _) = y in
    let (y1, _) = y0 in
    let (vs, _) = y1 in
    (match relabel_find fn f l u vs with
     | Some n ->
       Some (NMap.replace 0 u (add (Stdlib.Int.succ 0) (NMap.find 0 l n)) l)
     | None -> None)

  (** val find_push_node :
      ((((VSet.t * ESet.t) * (T__6.coq_V -> T__6.coq_V ->
      coq_R)) * T__6.coq_V) * T__6.coq_V) -> coq_R EMap.t -> int NMap.t ->
      T__6.coq_V -> T__6.coq_V list -> T__6.coq_V option **)

  let rec find_push_node fn f l u = function
  | [] -> None
  | v :: vs'0 ->
    if (&&)
         ((=) (NMap.find 0 l u) (add (Stdlib.Int.succ 0) (NMap.find 0 l v)))
         (coq_QLt (0, 1) (res_cap fn f u v))
    then Some v
    else find_push_node fn f l u vs'0

  (** val has_excess_not_sink :
      ((((VSet.t * ESet.t) * (T__6.coq_V -> T__6.coq_V ->
      coq_R)) * T__6.coq_V) * T__6.coq_V) -> coq_R EMap.t -> T__6.coq_V ->
      bool **)

  let has_excess_not_sink fn f v =
    let (y, t0) = fn in
    let (_, s) = y in
    if (||) (T__6.eqb v t0) (T__6.eqb v s)
    then false
    else coq_QLt (0, 1) (excess fn f v)

  type coq_Tr =
  | Init of (int * int) * (int * int) EMap.t * int NMap.t * VSet.t
  | Push of (int * int) * T__6.coq_V * T__6.coq_V * (int * int) EMap.t
     * VSet.t
  | Relabel of T__6.coq_V * int * int NMap.t
  | OutOfGas
  | RelabelFailed

  (** val coq_Tr_rect :
      ((int * int) -> (int * int) EMap.t -> int NMap.t -> VSet.t -> 'a1) ->
      ((int * int) -> T__6.coq_V -> T__6.coq_V -> (int * int) EMap.t ->
      VSet.t -> 'a1) -> (T__6.coq_V -> int -> int NMap.t -> 'a1) -> 'a1 ->
      'a1 -> coq_Tr -> 'a1 **)

  let coq_Tr_rect f f0 f1 f2 f3 = function
  | Init (d, t1, t2, t3) -> f d t1 t2 t3
  | Push (d, v, v0, t1, t2) -> f0 d v v0 t1 t2
  | Relabel (v, n, t1) -> f1 v n t1
  | OutOfGas -> f2
  | RelabelFailed -> f3

  (** val coq_Tr_rec :
      ((int * int) -> (int * int) EMap.t -> int NMap.t -> VSet.t -> 'a1) ->
      ((int * int) -> T__6.coq_V -> T__6.coq_V -> (int * int) EMap.t ->
      VSet.t -> 'a1) -> (T__6.coq_V -> int -> int NMap.t -> 'a1) -> 'a1 ->
      'a1 -> coq_Tr -> 'a1 **)

  let coq_Tr_rec f f0 f1 f2 f3 = function
  | Init (d, t1, t2, t3) -> f d t1 t2 t3
  | Push (d, v, v0, t1, t2) -> f0 d v v0 t1 t2
  | Relabel (v, n, t1) -> f1 v n t1
  | OutOfGas -> f2
  | RelabelFailed -> f3

  (** val gpr_helper_trace :
      ((((VSet.t * ESet.t) * (T__6.coq_V -> T__6.coq_V ->
      coq_R)) * T__6.coq_V) * T__6.coq_V) -> coq_R EMap.t -> int NMap.t ->
      T__6.coq_V list -> int -> coq_Tr list -> ((int * int) EMap.t * int
      NMap.t) option * coq_Tr list **)

  let rec gpr_helper_trace fn f l ac g tr =
    let (y, _) = fn in
    let (y0, _) = y in
    let (y1, _) = y0 in
    let (vs, _) = y1 in
    ((fun fO fS n -> if n=0 then fO () else fS (n-1))
       (fun _ -> (None, (OutOfGas :: tr)))
       (fun g' ->
       match VSet.choice ac with
       | Some p ->
         let (u, ac') = p in
         (match find_push_node fn f l u vs with
          | Some v ->
            let f' = push fn f u v in
            let ac'0 = if coq_QLt (0, 1) (excess fn f' u) then ac else ac' in
            if has_excess_not_sink fn f' v
            then let ac'' = VSet.add v ac'0 in
                 gpr_helper_trace fn f' l ac'' g' ((Push ((0, 1), u, v, f',
                   ac'')) :: tr)
            else let ac'' = VSet.remove v ac'0 in
                 gpr_helper_trace fn f' l ac'' g' ((Push ((0, 1), u, v, f',
                   ac'0)) :: tr)
          | None ->
            (match relabel fn f l u with
             | Some l' ->
               gpr_helper_trace fn f l' ac g' ((Relabel (u,
                 (NMap.find 0 l' u), l')) :: tr)
             | None -> (None, (RelabelFailed :: tr))))
       | None -> ((Some (f, l)), tr))
       g)

  (** val initial_push :
      ((((VSet.t * ESet.t) * (T__6.coq_V -> T__6.coq_V ->
      (int * int))) * T__6.coq_V) * T__6.coq_V) -> (int * int) EMap.t ->
      T__6.coq_V list -> (T__6.coq_V * T__6.coq_V) list -> (int * int)
      EMap.t * T__6.coq_V list **)

  let rec initial_push fn f ac es =
    let (y, _) = fn in
    let (y0, s) = y in
    let (_, c) = y0 in
    (match es with
     | [] -> (f, ac)
     | y1 :: es0 ->
       let (u, v) = y1 in
       if T__6.eqb s u
       then let f' = EMap.replace (0, 1) (u, v) (c u v) f in
            let ac0 =
              if has_excess_not_sink fn f' v then VSet.add v ac else ac
            in
            initial_push fn f' ac0 es0
       else initial_push fn f ac es0)

  (** val gpr_trace :
      coq_FlowNet -> ((int * int) EMap.t * int NMap.t) option * coq_Tr list **)

  let gpr_trace fn = match fn with
  | (p, _) ->
    let (p0, s) = p in
    let (g, _) = p0 in
    let (vs, es) = g in
    let labels = NMap.replace 0 s (length vs) (NMap.empty 0) in
    let bound = mul (mul (length es) (length vs)) (length vs) in
    let (f, active) = initial_push fn (EMap.empty (0, 1)) [] es in
    gpr_helper_trace fn f labels active bound ((Init ((0, 1), f, labels,
      active)) :: [])
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

module PRNat = PR(Coq_Nat)

(** val fN2 : PRNat.coq_FlowNet **)

let fN2 =
  let c = fun x y ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> (0, 1))
        (fun n ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> (((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1))),
          1))
          (fun n0 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> (0, 1))
            (fun n1 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> (((fun p->2*p) ((fun p->2*p) 1)), 1))
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
              (fun _ -> (((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1))),
              1))
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
                  (fun _ -> (((fun p->1+2*p) 1), 1))
                  (fun n4 ->
                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                    (fun _ -> (0, 1))
                    (fun n5 ->
                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                      (fun _ -> (((fun p->1+2*p) ((fun p->1+2*p) 1)),
                      1))
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
                      (fun _ -> (((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
                      1))), 1))
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
                  (fun _ -> (((fun p->1+2*p) ((fun p->2*p) 1)), 1))
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
                          (fun _ -> (((fun p->2*p) ((fun p->1+2*p)
                          ((fun p->2*p) 1))), 1))
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
  (((((0 :: ((Stdlib.Int.succ 0) :: ((Stdlib.Int.succ (Stdlib.Int.succ
  0)) :: ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
  0))) :: ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
  (Stdlib.Int.succ 0)))) :: ((Stdlib.Int.succ (Stdlib.Int.succ
  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))) :: [])))))), ((0,
  (Stdlib.Int.succ 0)) :: ((0, (Stdlib.Int.succ (Stdlib.Int.succ
  (Stdlib.Int.succ 0)))) :: (((Stdlib.Int.succ 0), (Stdlib.Int.succ
  (Stdlib.Int.succ 0))) :: (((Stdlib.Int.succ (Stdlib.Int.succ 0)),
  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
  0)))) :: (((Stdlib.Int.succ (Stdlib.Int.succ 0)), (Stdlib.Int.succ
  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
  0)))))) :: (((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))),
  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
  0))))) :: (((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
  (Stdlib.Int.succ 0)))), (Stdlib.Int.succ 0)) :: (((Stdlib.Int.succ
  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Stdlib.Int.succ
  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
  0)))))) :: []))))))))), c), 0), (Stdlib.Int.succ (Stdlib.Int.succ
  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
(* 
(** val fN1 : PRNat.coq_FlowNet **)
let fN1 =
  let c = fun _ _ -> { qnum = (Zpos (XO (XI (XO XH)))); qden = XH } in
  Pair ((Pair ((Pair ((Pair ((Cons (O, (Cons ((S O), Nil)))), (Cons ((Pair
  (O, (S O))), Nil)))), c)), O)), (S O)) *)



  
let time f x = 
    let t = Sys.time() in
    let fx = f x in
    Printf.printf "Ajakulu: %fms\n" ((Sys.time() -. t) *. 1000.0);
  fx

let () =
    (* let list1 : (PRNat.Edge.coq_V, PRNat.coq_R) prod list = 
      (Cons (Pair ((Pair (O, (S O))), { qnum = (Zpos (XO (XI (XO XH)))); qden = XH }),Nil)) in
    let _ = time PRNat.excess fN1 list1 (S O) in  *)
     (* Teistega excessi testida on keeruline, sest seda listi peaks manuaalselt koostama. Tuleme hiljem selle juurde tagasi.*)
    let _ = time PRNat.gpr_trace fN2 in
  ()
