module IArray : sig
  val length' : 'a array -> Z.t
  val sub' : 'a array * Z.t -> 'a
end = struct

let length' xs = Z.of_int (Array.length xs);;

let sub' (xs, i) = Array.get xs (Z.to_int i);;

end

module VYDRA : sig
  type nat
  val integer_of_nat : nat -> Z.t
  type 'a set
  val nat_of_integer : Z.t -> nat
  type 'a i
  type ('a, 'b) regex = Lookahead of ('a, 'b) formula |
    Symbol of ('a, 'b) formula | Plus of ('a, 'b) regex * ('a, 'b) regex |
    Times of ('a, 'b) regex * ('a, 'b) regex | Star of ('a, 'b) regex
  and ('a, 'b) formula = Bool of bool | Atom of 'a | Neg of ('a, 'b) formula |
    Bin of (bool -> bool -> bool) * ('a, 'b) formula * ('a, 'b) formula |
    Prev of 'b i * ('a, 'b) formula | Next of 'b i * ('a, 'b) formula |
    Since of ('a, 'b) formula * 'b i * ('a, 'b) formula |
    Until of ('a, 'b) formula * 'b i * ('a, 'b) formula |
    MatchP of 'b i * ('a, 'b) regex | MatchF of 'b i * ('a, 'b) regex
  type enat = Enat of nat | Infinity_enat
  type ('a, 'b, 'c) vydra_aux
  type ('a, 'b) regexa = Test of ('a, 'b) formulaa | Wild |
    Plusa of ('a, 'b) regexa * ('a, 'b) regexa |
    Timesa of ('a, 'b) regexa * ('a, 'b) regexa | Stara of ('a, 'b) regexa
  and ('a, 'b) formulaa = Boola of bool | Atoma of 'a |
    Nega of ('a, 'b) formulaa |
    Bina of (bool -> bool -> bool) * ('a, 'b) formulaa * ('a, 'b) formulaa |
    Preva of 'b i * ('a, 'b) formulaa | Nexta of 'b i * ('a, 'b) formulaa |
    Sincea of ('a, 'b) formulaa * 'b i * ('a, 'b) formulaa |
    Untila of ('a, 'b) formulaa * 'b i * ('a, 'b) formulaa |
    MatchPa of 'b i * ('a, 'b) regexa | MatchFa of 'b i * ('a, 'b) regexa
  val mk_db : string list -> string set
  val wf_fmla_enat : (string, enat) formula -> bool
  val interval_enat : enat -> enat -> bool -> bool -> enat i
  val mdl2mdl_enat : (string, enat) formula -> (string, enat) formulaa
  val progress_enat : (string, enat) formula -> enat list -> nat
  val rep_interval_enat : enat i -> enat * (enat * (bool * bool))
  val run_vydra_string_enat :
    ('a -> ('a * (enat * string set)) option) ->
      nat * (string, enat, 'a) vydra_aux ->
        ((nat * (string, enat, 'a) vydra_aux) * (enat * bool)) option
  val init_vydra_string_enat :
    'a -> ('a -> ('a * (enat * string set)) option) ->
            (string, enat) formula -> nat * (string, enat, 'a) vydra_aux
  val bounded_future_fmla_enat : (string, enat) formula -> bool
end = struct

type 'a countable = unit;;

type 'a finite = {countable_finite : 'a countable};;

type 'a enum =
  {finite_enum : 'a finite; enum : 'a list; enum_all : ('a -> bool) -> bool;
    enum_ex : ('a -> bool) -> bool};;
let enum _A = _A.enum;;
let enum_all _A = _A.enum_all;;
let enum_ex _A = _A.enum_ex;;

type 'a equal = {equal : 'a -> 'a -> bool};;
let equal _A = _A.equal;;

let rec eq _A a b = equal _A a b;;

let rec equal_funa _A _B f g = enum_all _A (fun x -> eq _B (f x) (g x));;

let rec equal_fun _A _B = ({equal = equal_funa _A _B} : ('a -> 'b) equal);;

type nat = Nat of Z.t;;

let rec integer_of_nat (Nat x) = x;;

let rec equal_nata m n = Z.equal (integer_of_nat m) (integer_of_nat n);;

let equal_nat = ({equal = equal_nata} : nat equal);;

type 'a ord = {less_eq : 'a -> 'a -> bool; less : 'a -> 'a -> bool};;
let less_eq _A = _A.less_eq;;
let less _A = _A.less;;

let rec min _A a b = (if less_eq _A a b then a else b);;

let rec less_eq_nat m n = Z.leq (integer_of_nat m) (integer_of_nat n);;

let rec less_nat m n = Z.lt (integer_of_nat m) (integer_of_nat n);;

let ord_nat = ({less_eq = less_eq_nat; less = less_nat} : nat ord);;

let rec inf_nata x = min ord_nat x;;

type 'a inf = {inf : 'a -> 'a -> 'a};;
let inf _A = _A.inf;;

let inf_nat = ({inf = inf_nata} : nat inf);;

let rec max _A a b = (if less_eq _A a b then b else a);;

let rec sup_nata x = max ord_nat x;;

type 'a sup = {sup : 'a -> 'a -> 'a};;
let sup _A = _A.sup;;

let sup_nat = ({sup = sup_nata} : nat sup);;

type 'a preorder = {ord_preorder : 'a ord};;

type 'a order = {preorder_order : 'a preorder};;

let preorder_nat = ({ord_preorder = ord_nat} : nat preorder);;

let order_nat = ({preorder_order = preorder_nat} : nat order);;

type 'a semilattice_sup =
  {sup_semilattice_sup : 'a sup; order_semilattice_sup : 'a order};;

type 'a semilattice_inf =
  {inf_semilattice_inf : 'a inf; order_semilattice_inf : 'a order};;

type 'a lattice =
  {semilattice_inf_lattice : 'a semilattice_inf;
    semilattice_sup_lattice : 'a semilattice_sup};;

let semilattice_sup_nat =
  ({sup_semilattice_sup = sup_nat; order_semilattice_sup = order_nat} :
    nat semilattice_sup);;

let semilattice_inf_nat =
  ({inf_semilattice_inf = inf_nat; order_semilattice_inf = order_nat} :
    nat semilattice_inf);;

let lattice_nat =
  ({semilattice_inf_lattice = semilattice_inf_nat;
     semilattice_sup_lattice = semilattice_sup_nat}
    : nat lattice);;

let ceq_nata : (nat -> nat -> bool) option = Some equal_nata;;

type 'a ceq = {ceq : ('a -> 'a -> bool) option};;
let ceq _A = _A.ceq;;

let ceq_nat = ({ceq = ceq_nata} : nat ceq);;

type ('a, 'b) phantom = Phantom of 'b;;

type set_impla = Set_Choose | Set_Collect | Set_DList | Set_RBT | Set_Monada;;

let set_impl_nata : (nat, set_impla) phantom = Phantom Set_RBT;;

type 'a set_impl = {set_impl : ('a, set_impla) phantom};;
let set_impl _A = _A.set_impl;;

let set_impl_nat = ({set_impl = set_impl_nata} : nat set_impl);;

type 'a linorder = {order_linorder : 'a order};;

let linorder_nat = ({order_linorder = order_nat} : nat linorder);;

let cEnum_nat :
  (nat list * (((nat -> bool) -> bool) * ((nat -> bool) -> bool))) option
  = None;;

type 'a cenum =
  {cEnum :
     ('a list * ((('a -> bool) -> bool) * (('a -> bool) -> bool))) option};;
let cEnum _A = _A.cEnum;;

let cenum_nat = ({cEnum = cEnum_nat} : nat cenum);;

let finite_UNIV_nata : (nat, bool) phantom = Phantom false;;

type 'a finite_UNIV = {finite_UNIV : ('a, bool) phantom};;
let finite_UNIV _A = _A.finite_UNIV;;

let finite_UNIV_nat = ({finite_UNIV = finite_UNIV_nata} : nat finite_UNIV);;

type ordera = Eq | Lt | Gt;;

let rec comparator_of (_A1, _A2)
  x y = (if less _A2.order_linorder.preorder_order.ord_preorder x y then Lt
          else (if eq _A1 x y then Eq else Gt));;

let rec compare_nat x = comparator_of (equal_nat, linorder_nat) x;;

let ccompare_nata : (nat -> nat -> ordera) option = Some compare_nat;;

type 'a ccompare = {ccompare : ('a -> 'a -> ordera) option};;
let ccompare _A = _A.ccompare;;

let ccompare_nat = ({ccompare = ccompare_nata} : nat ccompare);;

let ord_integer = ({less_eq = Z.leq; less = Z.lt} : Z.t ord);;

let rec minus_nat
  m n = Nat (max ord_integer Z.zero
              (Z.sub (integer_of_nat m) (integer_of_nat n)));;

let zero_nat : nat = Nat Z.zero;;

type num = One | Bit0 of num | Bit1 of num;;

let one_nat : nat = Nat (Z.of_int 1);;

let rec proper_interval_nat
  no x1 = match no, x1 with no, None -> true
    | None, Some x -> less_nat zero_nat x
    | Some x, Some y -> less_nat one_nat (minus_nat y x);;

let rec cproper_interval_nata x = proper_interval_nat x;;

type 'a cproper_interval =
  {ccompare_cproper_interval : 'a ccompare;
    cproper_interval : 'a option -> 'a option -> bool};;
let cproper_interval _A = _A.cproper_interval;;

let cproper_interval_nat =
  ({ccompare_cproper_interval = ccompare_nat;
     cproper_interval = cproper_interval_nata}
    : nat cproper_interval);;

let rec equal_order x0 x1 = match x0, x1 with Lt, Gt -> false
                      | Gt, Lt -> false
                      | Eq, Gt -> false
                      | Gt, Eq -> false
                      | Eq, Lt -> false
                      | Lt, Eq -> false
                      | Gt, Gt -> true
                      | Lt, Lt -> true
                      | Eq, Eq -> true;;

type ('a, 'b) generator = Generator of (('b -> bool) * ('b -> 'a * 'b));;

let rec generator (Generator x) = x;;

let rec fst (x1, x2) = x1;;

let rec has_next g = fst (generator g);;

let rec snd (x1, x2) = x2;;

let rec next g = snd (generator g);;

let rec sorted_list_subset_fusion
  less eq g1 g2 s1 s2 =
    (if has_next g1 s1
      then (let (x, s1a) = next g1 s1 in
             has_next g2 s2 &&
               (let (y, s2a) = next g2 s2 in
                 (if eq x y then sorted_list_subset_fusion less eq g1 g2 s1a s2a
                   else less y x &&
                          sorted_list_subset_fusion less eq g1 g2 s1 s2a)))
      else true);;

let rec list_all_fusion
  g p s =
    (if has_next g s
      then (let (x, sa) = next g s in p x && list_all_fusion g p sa)
      else true);;

type color = R | B;;

type ('a, 'b) rbt = Empty |
  Branch of color * ('a, 'b) rbt * 'a * 'b * ('a, 'b) rbt;;

let rec rbt_keys_next
  = function ((k, t) :: kts, Empty) -> (k, (kts, t))
    | (kts, Branch (c, l, k, v, r)) -> rbt_keys_next ((k, r) :: kts, l);;

let rec rbt_has_next = function ([], Empty) -> false
                       | (vb :: vc, va) -> true
                       | (v, Branch (vb, vc, vd, ve, vf)) -> true;;

let rbt_keys_generator :
  ('a, (('a * ('a, 'b) rbt) list * ('a, 'b) rbt)) generator
  = Generator (rbt_has_next, rbt_keys_next);;

let rec lt_of_comp
  acomp x y = (match acomp x y with Eq -> false | Lt -> true | Gt -> false);;

type ('b, 'a) mapping_rbt = Mapping_RBTa of ('b, 'a) rbt;;

type 'a set_dlist = Abs_dlist of 'a list;;

type 'a set = Collect_set of ('a -> bool) | DList_set of 'a set_dlist |
  RBT_set of ('a, unit) mapping_rbt | Set_Monad of 'a list |
  Complement of 'a set;;

let rec list_of_dlist _A (Abs_dlist x) = x;;

let rec list_all p x1 = match p, x1 with p, [] -> true
                   | p, x :: xs -> p x && list_all p xs;;

let rec dlist_all _A x xc = list_all x (list_of_dlist _A xc);;

let rec impl_ofa _B (Mapping_RBTa x) = x;;

let rec rbt_init x = ([], x);;

let rec init _A xa = rbt_init (impl_ofa _A xa);;

let rec filter
  p x1 = match p, x1 with p, [] -> []
    | p, x :: xs -> (if p x then x :: filter p xs else filter p xs);;

let rec collect _A
  p = (match cEnum _A with None -> Collect_set p
        | Some (enum, _) -> Set_Monad (filter p enum));;

let rec list_member
  equal x1 y = match equal, x1, y with
    equal, x :: xs, y -> equal x y || list_member equal xs y
    | equal, [], y -> false;;

let rec the (Some x2) = x2;;

let rec memberc _A xa = list_member (the (ceq _A)) (list_of_dlist _A xa);;

let rec equal_option _A x0 x1 = match x0, x1 with None, Some x2 -> false
                          | Some x2, None -> false
                          | Some x2, Some y2 -> eq _A x2 y2
                          | None, None -> true;;

let rec rbt_comp_lookup
  c x1 k = match c, x1, k with c, Empty, k -> None
    | c, Branch (uu, l, x, y, r), k ->
        (match c k x with Eq -> Some y | Lt -> rbt_comp_lookup c l k
          | Gt -> rbt_comp_lookup c r k);;

let rec lookupb _A xa = rbt_comp_lookup (the (ccompare _A)) (impl_ofa _A xa);;

let rec equal_unita u v = true;;

let equal_unit = ({equal = equal_unita} : unit equal);;

let rec memberb _A t x = equal_option equal_unit (lookupb _A t x) (Some ());;

let rec member (_A1, _A2)
  x xa1 = match x, xa1 with
    x, Set_Monad xs ->
      (match ceq _A1
        with None ->
          failwith "member Set_Monad: ceq = None"
            (fun _ -> member (_A1, _A2) x (Set_Monad xs))
        | Some eq -> list_member eq xs x)
    | xa, Complement x -> not (member (_A1, _A2) xa x)
    | x, RBT_set rbt -> memberb _A2 rbt x
    | x, DList_set dxs -> memberc _A1 dxs x
    | x, Collect_set a -> a x;;

let rec less_eq_set (_A1, _A2, _A3)
  x0 c = match x0, c with
    RBT_set rbt1, RBT_set rbt2 ->
      (match ccompare _A3
        with None ->
          failwith "subset RBT_set RBT_set: ccompare = None"
            (fun _ -> less_eq_set (_A1, _A2, _A3) (RBT_set rbt1) (RBT_set rbt2))
        | Some c ->
          (match ceq _A2
            with None ->
              sorted_list_subset_fusion (lt_of_comp c)
                (fun x y -> equal_order (c x y) Eq) rbt_keys_generator
                rbt_keys_generator (init _A3 rbt1) (init _A3 rbt2)
            | Some eq ->
              sorted_list_subset_fusion (lt_of_comp c) eq rbt_keys_generator
                rbt_keys_generator (init _A3 rbt1) (init _A3 rbt2)))
    | Complement a1, Complement a2 -> less_eq_set (_A1, _A2, _A3) a2 a1
    | Collect_set p, Complement a ->
        less_eq_set (_A1, _A2, _A3) a (collect _A1 (fun x -> not (p x)))
    | Set_Monad xs, c -> list_all (fun x -> member (_A2, _A3) x c) xs
    | DList_set dxs, c ->
        (match ceq _A2
          with None ->
            failwith "subset DList_set1: ceq = None"
              (fun _ -> less_eq_set (_A1, _A2, _A3) (DList_set dxs) c)
          | Some _ -> dlist_all _A2 (fun x -> member (_A2, _A3) x c) dxs)
    | RBT_set rbt, b ->
        (match ccompare _A3
          with None ->
            failwith "subset RBT_set1: ccompare = None"
              (fun _ -> less_eq_set (_A1, _A2, _A3) (RBT_set rbt) b)
          | Some _ ->
            list_all_fusion rbt_keys_generator (fun x -> member (_A2, _A3) x b)
              (init _A3 rbt));;

let rec equal_seta (_A1, _A2, _A3, _A4)
  a b = less_eq_set (_A1, _A2, _A3) a b && less_eq_set (_A1, _A2, _A3) b a;;

let rec equal_set (_A1, _A2, _A3, _A4) =
  ({equal = equal_seta (_A1, _A2, _A3, _A4)} : 'a set equal);;

let rec uminus_set = function Complement b -> b
                     | Collect_set p -> Collect_set (fun x -> not (p x))
                     | a -> Complement a;;

let rec balance
  x0 s t x3 = match x0, s, t, x3 with
    Branch (R, a, w, x, b), s, t, Branch (R, c, y, z, d) ->
      Branch (R, Branch (B, a, w, x, b), s, t, Branch (B, c, y, z, d))
    | Branch (R, Branch (R, a, w, x, b), s, t, c), y, z, Empty ->
        Branch (R, Branch (B, a, w, x, b), s, t, Branch (B, c, y, z, Empty))
    | Branch (R, Branch (R, a, w, x, b), s, t, c), y, z,
        Branch (B, va, vb, vc, vd)
        -> Branch
             (R, Branch (B, a, w, x, b), s, t,
               Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
    | Branch (R, Empty, w, x, Branch (R, b, s, t, c)), y, z, Empty ->
        Branch (R, Branch (B, Empty, w, x, b), s, t, Branch (B, c, y, z, Empty))
    | Branch (R, Branch (B, va, vb, vc, vd), w, x, Branch (R, b, s, t, c)), y,
        z, Empty
        -> Branch
             (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
               Branch (B, c, y, z, Empty))
    | Branch (R, Empty, w, x, Branch (R, b, s, t, c)), y, z,
        Branch (B, va, vb, vc, vd)
        -> Branch
             (R, Branch (B, Empty, w, x, b), s, t,
               Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
    | Branch (R, Branch (B, ve, vf, vg, vh), w, x, Branch (R, b, s, t, c)), y,
        z, Branch (B, va, vb, vc, vd)
        -> Branch
             (R, Branch (B, Branch (B, ve, vf, vg, vh), w, x, b), s, t,
               Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
    | Empty, w, x, Branch (R, b, s, t, Branch (R, c, y, z, d)) ->
        Branch (R, Branch (B, Empty, w, x, b), s, t, Branch (B, c, y, z, d))
    | Branch (B, va, vb, vc, vd), w, x,
        Branch (R, b, s, t, Branch (R, c, y, z, d))
        -> Branch
             (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
               Branch (B, c, y, z, d))
    | Empty, w, x, Branch (R, Branch (R, b, s, t, c), y, z, Empty) ->
        Branch (R, Branch (B, Empty, w, x, b), s, t, Branch (B, c, y, z, Empty))
    | Empty, w, x,
        Branch (R, Branch (R, b, s, t, c), y, z, Branch (B, va, vb, vc, vd))
        -> Branch
             (R, Branch (B, Empty, w, x, b), s, t,
               Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
    | Branch (B, va, vb, vc, vd), w, x,
        Branch (R, Branch (R, b, s, t, c), y, z, Empty)
        -> Branch
             (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
               Branch (B, c, y, z, Empty))
    | Branch (B, va, vb, vc, vd), w, x,
        Branch (R, Branch (R, b, s, t, c), y, z, Branch (B, ve, vf, vg, vh))
        -> Branch
             (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
               Branch (B, c, y, z, Branch (B, ve, vf, vg, vh)))
    | Empty, s, t, Empty -> Branch (B, Empty, s, t, Empty)
    | Empty, s, t, Branch (B, va, vb, vc, vd) ->
        Branch (B, Empty, s, t, Branch (B, va, vb, vc, vd))
    | Empty, s, t, Branch (v, Empty, vb, vc, Empty) ->
        Branch (B, Empty, s, t, Branch (v, Empty, vb, vc, Empty))
    | Empty, s, t, Branch (v, Branch (B, ve, vf, vg, vh), vb, vc, Empty) ->
        Branch
          (B, Empty, s, t,
            Branch (v, Branch (B, ve, vf, vg, vh), vb, vc, Empty))
    | Empty, s, t, Branch (v, Empty, vb, vc, Branch (B, vf, vg, vh, vi)) ->
        Branch
          (B, Empty, s, t,
            Branch (v, Empty, vb, vc, Branch (B, vf, vg, vh, vi)))
    | Empty, s, t,
        Branch
          (v, Branch (B, ve, vj, vk, vl), vb, vc, Branch (B, vf, vg, vh, vi))
        -> Branch
             (B, Empty, s, t,
               Branch
                 (v, Branch (B, ve, vj, vk, vl), vb, vc,
                   Branch (B, vf, vg, vh, vi)))
    | Branch (B, va, vb, vc, vd), s, t, Empty ->
        Branch (B, Branch (B, va, vb, vc, vd), s, t, Empty)
    | Branch (B, va, vb, vc, vd), s, t, Branch (B, ve, vf, vg, vh) ->
        Branch (B, Branch (B, va, vb, vc, vd), s, t, Branch (B, ve, vf, vg, vh))
    | Branch (B, va, vb, vc, vd), s, t, Branch (v, Empty, vf, vg, Empty) ->
        Branch
          (B, Branch (B, va, vb, vc, vd), s, t,
            Branch (v, Empty, vf, vg, Empty))
    | Branch (B, va, vb, vc, vd), s, t,
        Branch (v, Branch (B, vi, vj, vk, vl), vf, vg, Empty)
        -> Branch
             (B, Branch (B, va, vb, vc, vd), s, t,
               Branch (v, Branch (B, vi, vj, vk, vl), vf, vg, Empty))
    | Branch (B, va, vb, vc, vd), s, t,
        Branch (v, Empty, vf, vg, Branch (B, vj, vk, vl, vm))
        -> Branch
             (B, Branch (B, va, vb, vc, vd), s, t,
               Branch (v, Empty, vf, vg, Branch (B, vj, vk, vl, vm)))
    | Branch (B, va, vb, vc, vd), s, t,
        Branch
          (v, Branch (B, vi, vn, vo, vp), vf, vg, Branch (B, vj, vk, vl, vm))
        -> Branch
             (B, Branch (B, va, vb, vc, vd), s, t,
               Branch
                 (v, Branch (B, vi, vn, vo, vp), vf, vg,
                   Branch (B, vj, vk, vl, vm)))
    | Branch (v, Empty, vb, vc, Empty), s, t, Empty ->
        Branch (B, Branch (v, Empty, vb, vc, Empty), s, t, Empty)
    | Branch (v, Empty, vb, vc, Branch (B, ve, vf, vg, vh)), s, t, Empty ->
        Branch
          (B, Branch (v, Empty, vb, vc, Branch (B, ve, vf, vg, vh)), s, t,
            Empty)
    | Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Empty), s, t, Empty ->
        Branch
          (B, Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Empty), s, t,
            Empty)
    | Branch
        (v, Branch (B, vf, vg, vh, vi), vb, vc, Branch (B, ve, vj, vk, vl)),
        s, t, Empty
        -> Branch
             (B, Branch
                   (v, Branch (B, vf, vg, vh, vi), vb, vc,
                     Branch (B, ve, vj, vk, vl)),
               s, t, Empty)
    | Branch (v, Empty, vf, vg, Empty), s, t, Branch (B, va, vb, vc, vd) ->
        Branch
          (B, Branch (v, Empty, vf, vg, Empty), s, t,
            Branch (B, va, vb, vc, vd))
    | Branch (v, Empty, vf, vg, Branch (B, vi, vj, vk, vl)), s, t,
        Branch (B, va, vb, vc, vd)
        -> Branch
             (B, Branch (v, Empty, vf, vg, Branch (B, vi, vj, vk, vl)), s, t,
               Branch (B, va, vb, vc, vd))
    | Branch (v, Branch (B, vj, vk, vl, vm), vf, vg, Empty), s, t,
        Branch (B, va, vb, vc, vd)
        -> Branch
             (B, Branch (v, Branch (B, vj, vk, vl, vm), vf, vg, Empty), s, t,
               Branch (B, va, vb, vc, vd))
    | Branch
        (v, Branch (B, vj, vk, vl, vm), vf, vg, Branch (B, vi, vn, vo, vp)),
        s, t, Branch (B, va, vb, vc, vd)
        -> Branch
             (B, Branch
                   (v, Branch (B, vj, vk, vl, vm), vf, vg,
                     Branch (B, vi, vn, vo, vp)),
               s, t, Branch (B, va, vb, vc, vd));;

let rec rbt_comp_ins
  c f k v x4 = match c, f, k, v, x4 with
    c, f, k, v, Empty -> Branch (R, Empty, k, v, Empty)
    | c, f, k, v, Branch (B, l, x, y, r) ->
        (match c k x with Eq -> Branch (B, l, x, f k y v, r)
          | Lt -> balance (rbt_comp_ins c f k v l) x y r
          | Gt -> balance l x y (rbt_comp_ins c f k v r))
    | c, f, k, v, Branch (R, l, x, y, r) ->
        (match c k x with Eq -> Branch (R, l, x, f k y v, r)
          | Lt -> Branch (R, rbt_comp_ins c f k v l, x, y, r)
          | Gt -> Branch (R, l, x, y, rbt_comp_ins c f k v r));;

let rec paint c x1 = match c, x1 with c, Empty -> Empty
                | c, Branch (uu, l, k, v, r) -> Branch (c, l, k, v, r);;

let rec rbt_comp_insert_with_key c f k v t = paint B (rbt_comp_ins c f k v t);;

let rec rbt_comp_insert c = rbt_comp_insert_with_key c (fun _ _ nv -> nv);;

let rec insertb _A
  xc xd xe =
    Mapping_RBTa (rbt_comp_insert (the (ccompare _A)) xc xd (impl_ofa _A xe));;

let rec rbt_baliR
  t1 ab bb x3 = match t1, ab, bb, x3 with
    t1, ab, bb, Branch (R, t2, aa, ba, Branch (R, t3, a, b, t4)) ->
      Branch (R, Branch (B, t1, ab, bb, t2), aa, ba, Branch (B, t3, a, b, t4))
    | t1, ab, bb, Branch (R, Branch (R, t2, aa, ba, t3), a, b, Empty) ->
        Branch
          (R, Branch (B, t1, ab, bb, t2), aa, ba, Branch (B, t3, a, b, Empty))
    | t1, ab, bb,
        Branch (R, Branch (R, t2, aa, ba, t3), a, b, Branch (B, va, vb, vc, vd))
        -> Branch
             (R, Branch (B, t1, ab, bb, t2), aa, ba,
               Branch (B, t3, a, b, Branch (B, va, vb, vc, vd)))
    | t1, a, b, Empty -> Branch (B, t1, a, b, Empty)
    | t1, a, b, Branch (B, va, vb, vc, vd) ->
        Branch (B, t1, a, b, Branch (B, va, vb, vc, vd))
    | t1, a, b, Branch (v, Empty, vb, vc, Empty) ->
        Branch (B, t1, a, b, Branch (v, Empty, vb, vc, Empty))
    | t1, a, b, Branch (v, Branch (B, ve, vf, vg, vh), vb, vc, Empty) ->
        Branch
          (B, t1, a, b, Branch (v, Branch (B, ve, vf, vg, vh), vb, vc, Empty))
    | t1, a, b, Branch (v, Empty, vb, vc, Branch (B, vf, vg, vh, vi)) ->
        Branch
          (B, t1, a, b, Branch (v, Empty, vb, vc, Branch (B, vf, vg, vh, vi)))
    | t1, a, b,
        Branch
          (v, Branch (B, ve, vj, vk, vl), vb, vc, Branch (B, vf, vg, vh, vi))
        -> Branch
             (B, t1, a, b,
               Branch
                 (v, Branch (B, ve, vj, vk, vl), vb, vc,
                   Branch (B, vf, vg, vh, vi)));;

let rec equal_color x0 x1 = match x0, x1 with R, B -> false
                      | B, R -> false
                      | B, B -> true
                      | R, R -> true;;

let rec plus_nat m n = Nat (Z.add (integer_of_nat m) (integer_of_nat n));;

let rec suc n = plus_nat n one_nat;;

let rec bheight
  = function Empty -> zero_nat
    | Branch (c, lt, k, v, rt) ->
        (if equal_color c B then suc (bheight lt) else bheight lt);;

let rec rbt_joinR
  l a b r =
    (if less_eq_nat (bheight l) (bheight r) then Branch (R, l, a, b, r)
      else (match l
             with Branch (R, la, ab, ba, ra) ->
               Branch (R, la, ab, ba, rbt_joinR ra a b r)
             | Branch (B, la, ab, ba, ra) ->
               rbt_baliR la ab ba (rbt_joinR ra a b r)));;

let rec rbt_baliL
  x0 a b t4 = match x0, a, b, t4 with
    Branch (R, Branch (R, t1, ab, bb, t2), aa, ba, t3), a, b, t4 ->
      Branch (R, Branch (B, t1, ab, bb, t2), aa, ba, Branch (B, t3, a, b, t4))
    | Branch (R, Empty, ab, bb, Branch (R, t2, aa, ba, t3)), a, b, t4 ->
        Branch
          (R, Branch (B, Empty, ab, bb, t2), aa, ba, Branch (B, t3, a, b, t4))
    | Branch
        (R, Branch (B, va, vb, vc, vd), ab, bb, Branch (R, t2, aa, ba, t3)),
        a, b, t4
        -> Branch
             (R, Branch (B, Branch (B, va, vb, vc, vd), ab, bb, t2), aa, ba,
               Branch (B, t3, a, b, t4))
    | Empty, a, b, t2 -> Branch (B, Empty, a, b, t2)
    | Branch (B, va, vb, vc, vd), a, b, t2 ->
        Branch (B, Branch (B, va, vb, vc, vd), a, b, t2)
    | Branch (v, Empty, vb, vc, Empty), a, b, t2 ->
        Branch (B, Branch (v, Empty, vb, vc, Empty), a, b, t2)
    | Branch (v, Empty, vb, vc, Branch (B, ve, vf, vg, vh)), a, b, t2 ->
        Branch
          (B, Branch (v, Empty, vb, vc, Branch (B, ve, vf, vg, vh)), a, b, t2)
    | Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Empty), a, b, t2 ->
        Branch
          (B, Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Empty), a, b, t2)
    | Branch
        (v, Branch (B, vf, vg, vh, vi), vb, vc, Branch (B, ve, vj, vk, vl)),
        a, b, t2
        -> Branch
             (B, Branch
                   (v, Branch (B, vf, vg, vh, vi), vb, vc,
                     Branch (B, ve, vj, vk, vl)),
               a, b, t2);;

let rec rbt_joinL
  l a b r =
    (if less_eq_nat (bheight r) (bheight l) then Branch (R, l, a, b, r)
      else (match r
             with Branch (R, la, ab, ba, ra) ->
               Branch (R, rbt_joinL l a b la, ab, ba, ra)
             | Branch (B, la, ab, ba, ra) ->
               rbt_baliL (rbt_joinL l a b la) ab ba ra));;

let rec rbt_join
  l a b r =
    (let bhl = bheight l in
     let bhr = bheight r in
      (if less_nat bhr bhl then paint B (rbt_joinR l a b r)
        else (if less_nat bhl bhr then paint B (rbt_joinL l a b r)
               else Branch (B, l, a, b, r))));;

let rec rbt_split_comp
  c x1 k = match c, x1, k with c, Empty, k -> (Empty, (None, Empty))
    | c, Branch (uu, l, a, b, r), x ->
        (match c x a with Eq -> (l, (Some b, r))
          | Lt ->
            (let (l1, (beta, l2)) = rbt_split_comp c l x in
              (l1, (beta, rbt_join l2 a b r)))
          | Gt ->
            (let (r1, (beta, r2)) = rbt_split_comp c r x in
              (rbt_join l a b r1, (beta, r2))));;

let rec nat_of_integer k = Nat (max ord_integer Z.zero k);;

let rec folda
  f xa1 x = match f, xa1, x with
    f, Branch (c, lt, k, v, rt), x -> folda f rt (f k v (folda f lt x))
    | f, Empty, x -> x;;

let rec rbt_comp_union_swap_rec
  c f gamma t1 t2 =
    (let bh1 = bheight t1 in
     let bh2 = bheight t2 in
     let (gammaa, (t2a, (bh2a, (t1a, _)))) =
       (if less_nat bh1 bh2 then (not gamma, (t1, (bh1, (t2, bh2))))
         else (gamma, (t2, (bh2, (t1, bh1)))))
       in
     let fa = (if gammaa then (fun k v va -> f k va v) else f) in
      (if less_nat bh2a (nat_of_integer (Z.of_int 4))
        then folda (rbt_comp_insert_with_key c fa) t2a t1a
        else (match t1a with Empty -> t2a
               | Branch (_, l1, a, b, r1) ->
                 (let (l2, (beta, r2)) = rbt_split_comp c t2a a in
                   rbt_join (rbt_comp_union_swap_rec c f gammaa l1 l2) a
                     (match beta with None -> b | Some ca -> fa a b ca)
                     (rbt_comp_union_swap_rec c f gammaa r1 r2)))));;

let rec rbt_comp_union_with_key
  c f t1 t2 = paint B (rbt_comp_union_swap_rec c f false t1 t2);;

let rec join _A
  xc xd xe =
    Mapping_RBTa
      (rbt_comp_union_with_key (the (ccompare _A)) xc (impl_ofa _A xd)
        (impl_ofa _A xe));;

let rec list_insert
  equal x xs = (if list_member equal xs x then xs else x :: xs);;

let rec inserta _A
  xb xc = Abs_dlist (list_insert (the (ceq _A)) xb (list_of_dlist _A xc));;

let rec fold f x1 s = match f, x1, s with f, x :: xs, s -> fold f xs (f x s)
               | f, [], s -> s;;

let rec foldc _A x xc = fold x (list_of_dlist _A xc);;

let rec union _A = foldc _A (inserta _A);;

let rec id x = (fun xa -> xa) x;;

let rec is_none = function Some x -> false
                  | None -> true;;

let rec inter_list _A
  xb xc =
    Mapping_RBTa
      (fold (fun k -> rbt_comp_insert (the (ccompare _A)) k ())
        (filter
          (fun x ->
            not (is_none
                  (rbt_comp_lookup (the (ccompare _A)) (impl_ofa _A xb) x)))
          xc)
        Empty);;

let rec gen_length n x1 = match n, x1 with n, x :: xs -> gen_length (suc n) xs
                     | n, [] -> n;;

let rec size_list x = gen_length zero_nat x;;

let rec apfst f (x, y) = (f x, y);;

let rec map_prod f g (a, b) = (f a, g b);;

let rec divmod_nat
  m n = (let k = integer_of_nat m in
         let l = integer_of_nat n in
          map_prod nat_of_integer nat_of_integer
            (if Z.equal k Z.zero then (Z.zero, Z.zero)
              else (if Z.equal l Z.zero then (Z.zero, k)
                     else (fun k l -> if Z.equal Z.zero l then (Z.zero, l) else
                            Z.div_rem (Z.abs k) (Z.abs l))
                            k l)));;

let rec rbtreeify_g
  n kvs =
    (if equal_nata n zero_nat || equal_nata n one_nat then (Empty, kvs)
      else (let (na, r) = divmod_nat n (nat_of_integer (Z.of_int 2)) in
             (if equal_nata r zero_nat
               then (let (t1, (k, v) :: kvsa) = rbtreeify_g na kvs in
                      apfst (fun a -> Branch (B, t1, k, v, a))
                        (rbtreeify_g na kvsa))
               else (let (t1, (k, v) :: kvsa) = rbtreeify_f na kvs in
                      apfst (fun a -> Branch (B, t1, k, v, a))
                        (rbtreeify_g na kvsa)))))
and rbtreeify_f
  n kvs =
    (if equal_nata n zero_nat then (Empty, kvs)
      else (if equal_nata n one_nat
             then (let (k, v) :: kvsa = kvs in
                    (Branch (R, Empty, k, v, Empty), kvsa))
             else (let (na, r) = divmod_nat n (nat_of_integer (Z.of_int 2)) in
                    (if equal_nata r zero_nat
                      then (let (t1, (k, v) :: kvsa) = rbtreeify_f na kvs in
                             apfst (fun a -> Branch (B, t1, k, v, a))
                               (rbtreeify_g na kvsa))
                      else (let (t1, (k, v) :: kvsa) = rbtreeify_f na kvs in
                             apfst (fun a -> Branch (B, t1, k, v, a))
                               (rbtreeify_f na kvsa))))));;

let rec rbtreeify kvs = fst (rbtreeify_g (suc (size_list kvs)) kvs);;

let rec gen_entries
  kvts x1 = match kvts, x1 with
    kvts, Branch (c, l, k, v, r) -> gen_entries (((k, v), r) :: kvts) l
    | (kv, t) :: kvts, Empty -> kv :: gen_entries kvts t
    | [], Empty -> [];;

let rec entries x = gen_entries [] x;;

let rec filterb _A
  xb xc = Mapping_RBTa (rbtreeify (filter xb (entries (impl_ofa _A xc))));;

let rec map_filter
  f x1 = match f, x1 with f, [] -> []
    | f, x :: xs ->
        (match f x with None -> map_filter f xs
          | Some y -> y :: map_filter f xs);;

let rec map_filter_comp_inter
  c f t1 t2 =
    map_filter
      (fun (k, v) ->
        (match rbt_comp_lookup c t1 k with None -> None
          | Some va -> Some (k, f k va v)))
      (entries t2);;

let rec is_rbt_empty
  t = (match t with Empty -> true | Branch (_, _, _, _, _) -> false);;

let rec rbt_split_min
  = function Empty -> failwith "undefined"
    | Branch (uu, l, a, b, r) ->
        (if is_rbt_empty l then (a, (b, r))
          else (let (aa, (ba, la)) = rbt_split_min l in
                 (aa, (ba, rbt_join la a b r))));;

let rec rbt_join2
  l r = (if is_rbt_empty r then l
          else (let a = rbt_split_min r in
                let (aa, b) = a in
                let (ba, c) = b in
                 rbt_join l aa ba c));;

let rec rbt_comp_inter_swap_rec
  c f gamma t1 t2 =
    (let bh1 = bheight t1 in
     let bh2 = bheight t2 in
     let (gammaa, (t2a, (bh2a, (t1a, _)))) =
       (if less_nat bh1 bh2 then (not gamma, (t1, (bh1, (t2, bh2))))
         else (gamma, (t2, (bh2, (t1, bh1)))))
       in
     let fa = (if gammaa then (fun k v va -> f k va v) else f) in
      (if less_nat bh2a (nat_of_integer (Z.of_int 4))
        then rbtreeify (map_filter_comp_inter c fa t1a t2a)
        else (match t1a with Empty -> Empty
               | Branch (_, l1, a, b, r1) ->
                 (let (l2, (beta, r2)) = rbt_split_comp c t2a a in
                  let l = rbt_comp_inter_swap_rec c f gammaa l1 l2 in
                  let r = rbt_comp_inter_swap_rec c f gammaa r1 r2 in
                   (match beta with None -> rbt_join2 l r
                     | Some ba -> rbt_join l a (fa a b ba) r)))));;

let rec rbt_comp_inter_with_key
  c f t1 t2 = paint B (rbt_comp_inter_swap_rec c f false t1 t2);;

let rec meet _A
  xc xd xe =
    Mapping_RBTa
      (rbt_comp_inter_with_key (the (ccompare _A)) xc (impl_ofa _A xd)
        (impl_ofa _A xe));;

let rec filtera _A xb xc = Abs_dlist (filter xb (list_of_dlist _A xc));;

let rec comp f g = (fun x -> f (g x));;

let rec inf_seta (_A1, _A2)
  g ga = match g, ga with
    RBT_set rbt1, Set_Monad xs ->
      (match ccompare _A2
        with None ->
          failwith "inter RBT_set Set_Monad: ccompare = None"
            (fun _ -> inf_seta (_A1, _A2) (RBT_set rbt1) (Set_Monad xs))
        | Some _ -> RBT_set (inter_list _A2 rbt1 xs))
    | RBT_set rbt, DList_set dxs ->
        (match ccompare _A2
          with None ->
            failwith "inter RBT_set DList_set: ccompare = None"
              (fun _ -> inf_seta (_A1, _A2) (RBT_set rbt) (DList_set dxs))
          | Some _ ->
            (match ceq _A1
              with None ->
                failwith "inter RBT_set DList_set: ceq = None"
                  (fun _ -> inf_seta (_A1, _A2) (RBT_set rbt) (DList_set dxs))
              | Some _ -> RBT_set (inter_list _A2 rbt (list_of_dlist _A1 dxs))))
    | RBT_set rbt1, RBT_set rbt2 ->
        (match ccompare _A2
          with None ->
            failwith "inter RBT_set RBT_set: ccompare = None"
              (fun _ -> inf_seta (_A1, _A2) (RBT_set rbt1) (RBT_set rbt2))
          | Some _ -> RBT_set (meet _A2 (fun _ _ -> id) rbt1 rbt2))
    | DList_set dxs1, Set_Monad xs ->
        (match ceq _A1
          with None ->
            failwith "inter DList_set Set_Monad: ceq = None"
              (fun _ -> inf_seta (_A1, _A2) (DList_set dxs1) (Set_Monad xs))
          | Some eq -> DList_set (filtera _A1 (list_member eq xs) dxs1))
    | DList_set dxs1, DList_set dxs2 ->
        (match ceq _A1
          with None ->
            failwith "inter DList_set DList_set: ceq = None"
              (fun _ -> inf_seta (_A1, _A2) (DList_set dxs1) (DList_set dxs2))
          | Some _ -> DList_set (filtera _A1 (memberc _A1 dxs2) dxs1))
    | DList_set dxs, RBT_set rbt ->
        (match ccompare _A2
          with None ->
            failwith "inter DList_set RBT_set: ccompare = None"
              (fun _ -> inf_seta (_A1, _A2) (DList_set dxs) (RBT_set rbt))
          | Some _ ->
            (match ceq _A1
              with None ->
                failwith "inter DList_set RBT_set: ceq = None"
                  (fun _ -> inf_seta (_A1, _A2) (DList_set dxs) (RBT_set rbt))
              | Some _ -> RBT_set (inter_list _A2 rbt (list_of_dlist _A1 dxs))))
    | Set_Monad xs1, Set_Monad xs2 ->
        (match ceq _A1
          with None ->
            failwith "inter Set_Monad Set_Monad: ceq = None"
              (fun _ -> inf_seta (_A1, _A2) (Set_Monad xs1) (Set_Monad xs2))
          | Some eq -> Set_Monad (filter (list_member eq xs2) xs1))
    | Set_Monad xs, DList_set dxs2 ->
        (match ceq _A1
          with None ->
            failwith "inter Set_Monad DList_set: ceq = None"
              (fun _ -> inf_seta (_A1, _A2) (Set_Monad xs) (DList_set dxs2))
          | Some eq -> DList_set (filtera _A1 (list_member eq xs) dxs2))
    | Set_Monad xs, RBT_set rbt1 ->
        (match ccompare _A2
          with None ->
            failwith "inter Set_Monad RBT_set: ccompare = None"
              (fun _ -> inf_seta (_A1, _A2) (RBT_set rbt1) (Set_Monad xs))
          | Some _ -> RBT_set (inter_list _A2 rbt1 xs))
    | Complement ba, Complement b -> Complement (sup_seta (_A1, _A2) ba b)
    | g, RBT_set rbt2 ->
        (match ccompare _A2
          with None ->
            failwith "inter RBT_set2: ccompare = None"
              (fun _ -> inf_seta (_A1, _A2) g (RBT_set rbt2))
          | Some _ ->
            RBT_set
              (filterb _A2 (comp (fun x -> member (_A1, _A2) x g) fst) rbt2))
    | RBT_set rbt1, g ->
        (match ccompare _A2
          with None ->
            failwith "inter RBT_set1: ccompare = None"
              (fun _ -> inf_seta (_A1, _A2) (RBT_set rbt1) g)
          | Some _ ->
            RBT_set
              (filterb _A2 (comp (fun x -> member (_A1, _A2) x g) fst) rbt1))
    | h, DList_set dxs2 ->
        (match ceq _A1
          with None ->
            failwith "inter DList_set2: ceq = None"
              (fun _ -> inf_seta (_A1, _A2) h (DList_set dxs2))
          | Some _ ->
            DList_set (filtera _A1 (fun x -> member (_A1, _A2) x h) dxs2))
    | DList_set dxs1, h ->
        (match ceq _A1
          with None ->
            failwith "inter DList_set1: ceq = None"
              (fun _ -> inf_seta (_A1, _A2) (DList_set dxs1) h)
          | Some _ ->
            DList_set (filtera _A1 (fun x -> member (_A1, _A2) x h) dxs1))
    | i, Set_Monad xs -> Set_Monad (filter (fun x -> member (_A1, _A2) x i) xs)
    | Set_Monad xs, i -> Set_Monad (filter (fun x -> member (_A1, _A2) x i) xs)
    | j, Collect_set a -> Collect_set (fun x -> a x && member (_A1, _A2) x j)
    | Collect_set a, j -> Collect_set (fun x -> a x && member (_A1, _A2) x j)
and sup_seta (_A1, _A2)
  ba b = match ba, b with
    ba, Complement b -> Complement (inf_seta (_A1, _A2) (uminus_set ba) b)
    | Complement ba, b -> Complement (inf_seta (_A1, _A2) ba (uminus_set b))
    | b, Collect_set a -> Collect_set (fun x -> a x || member (_A1, _A2) x b)
    | Collect_set a, b -> Collect_set (fun x -> a x || member (_A1, _A2) x b)
    | Set_Monad xs, Set_Monad ys -> Set_Monad (xs @ ys)
    | DList_set dxs1, Set_Monad ws ->
        (match ceq _A1
          with None ->
            failwith "union DList_set Set_Monad: ceq = None"
              (fun _ -> sup_seta (_A1, _A2) (DList_set dxs1) (Set_Monad ws))
          | Some _ -> DList_set (fold (inserta _A1) ws dxs1))
    | Set_Monad ws, DList_set dxs2 ->
        (match ceq _A1
          with None ->
            failwith "union Set_Monad DList_set: ceq = None"
              (fun _ -> sup_seta (_A1, _A2) (Set_Monad ws) (DList_set dxs2))
          | Some _ -> DList_set (fold (inserta _A1) ws dxs2))
    | RBT_set rbt1, Set_Monad zs ->
        (match ccompare _A2
          with None ->
            failwith "union RBT_set Set_Monad: ccompare = None"
              (fun _ -> sup_seta (_A1, _A2) (RBT_set rbt1) (Set_Monad zs))
          | Some _ -> RBT_set (fold (fun k -> insertb _A2 k ()) zs rbt1))
    | Set_Monad zs, RBT_set rbt2 ->
        (match ccompare _A2
          with None ->
            failwith "union Set_Monad RBT_set: ccompare = None"
              (fun _ -> sup_seta (_A1, _A2) (Set_Monad zs) (RBT_set rbt2))
          | Some _ -> RBT_set (fold (fun k -> insertb _A2 k ()) zs rbt2))
    | DList_set dxs1, DList_set dxs2 ->
        (match ceq _A1
          with None ->
            failwith "union DList_set DList_set: ceq = None"
              (fun _ -> sup_seta (_A1, _A2) (DList_set dxs1) (DList_set dxs2))
          | Some _ -> DList_set (union _A1 dxs1 dxs2))
    | DList_set dxs, RBT_set rbt ->
        (match ccompare _A2
          with None ->
            failwith "union DList_set RBT_set: ccompare = None"
              (fun _ -> sup_seta (_A1, _A2) (RBT_set rbt) (DList_set dxs))
          | Some _ ->
            (match ceq _A1
              with None ->
                failwith "union DList_set RBT_set: ceq = None"
                  (fun _ -> sup_seta (_A1, _A2) (RBT_set rbt) (DList_set dxs))
              | Some _ ->
                RBT_set (foldc _A1 (fun k -> insertb _A2 k ()) dxs rbt)))
    | RBT_set rbt, DList_set dxs ->
        (match ccompare _A2
          with None ->
            failwith "union RBT_set DList_set: ccompare = None"
              (fun _ -> sup_seta (_A1, _A2) (RBT_set rbt) (DList_set dxs))
          | Some _ ->
            (match ceq _A1
              with None ->
                failwith "union RBT_set DList_set: ceq = None"
                  (fun _ -> sup_seta (_A1, _A2) (RBT_set rbt) (DList_set dxs))
              | Some _ ->
                RBT_set (foldc _A1 (fun k -> insertb _A2 k ()) dxs rbt)))
    | RBT_set rbt1, RBT_set rbt2 ->
        (match ccompare _A2
          with None ->
            failwith "union RBT_set RBT_set: ccompare = None"
              (fun _ -> sup_seta (_A1, _A2) (RBT_set rbt1) (RBT_set rbt2))
          | Some _ -> RBT_set (join _A2 (fun _ _ -> id) rbt1 rbt2));;

let rec inf_set (_A1, _A2) = ({inf = inf_seta (_A1, _A2)} : 'a set inf);;

let rec sup_set (_A1, _A2) = ({sup = sup_seta (_A1, _A2)} : 'a set sup);;

let rec less_set (_A1, _A2, _A3)
  a b = less_eq_set (_A1, _A2, _A3) a b &&
          not (less_eq_set (_A1, _A2, _A3) b a);;

let rec ord_set (_A1, _A2, _A3) =
  ({less_eq = less_eq_set (_A1, _A2, _A3); less = less_set (_A1, _A2, _A3)} :
    'a set ord);;

let rec preorder_set (_A1, _A2, _A3) =
  ({ord_preorder = (ord_set (_A1, _A2, _A3))} : 'a set preorder);;

let rec order_set (_A1, _A2, _A3) =
  ({preorder_order = (preorder_set (_A1, _A2, _A3))} : 'a set order);;

let rec semilattice_sup_set (_A1, _A2, _A3) =
  ({sup_semilattice_sup = (sup_set (_A2, _A3));
     order_semilattice_sup = (order_set (_A1, _A2, _A3))}
    : 'a set semilattice_sup);;

let rec semilattice_inf_set (_A1, _A2, _A3) =
  ({inf_semilattice_inf = (inf_set (_A2, _A3));
     order_semilattice_inf = (order_set (_A1, _A2, _A3))}
    : 'a set semilattice_inf);;

let rec lattice_set (_A1, _A2, _A3) =
  ({semilattice_inf_lattice = (semilattice_inf_set (_A1, _A2, _A3));
     semilattice_sup_lattice = (semilattice_sup_set (_A1, _A2, _A3))}
    : 'a set lattice);;

let rec list_all2_fusion
  p g1 g2 s1 s2 =
    (if has_next g1 s1
      then has_next g2 s2 &&
             (let (x, s1a) = next g1 s1 in
              let (y, s2a) = next g2 s2 in
               p x y && list_all2_fusion p g1 g2 s1a s2a)
      else not (has_next g2 s2));;

let rec set_eq (_A1, _A2, _A3)
  a b = match a, b with
    RBT_set rbt1, RBT_set rbt2 ->
      (match ccompare _A3
        with None ->
          failwith "set_eq RBT_set RBT_set: ccompare = None"
            (fun _ -> set_eq (_A1, _A2, _A3) (RBT_set rbt1) (RBT_set rbt2))
        | Some c ->
          (match ceq _A2
            with None ->
              list_all2_fusion (fun x y -> equal_order (c x y) Eq)
                rbt_keys_generator rbt_keys_generator (init _A3 rbt1)
                (init _A3 rbt2)
            | Some eq ->
              list_all2_fusion eq rbt_keys_generator rbt_keys_generator
                (init _A3 rbt1) (init _A3 rbt2)))
    | Complement a, Complement b -> set_eq (_A1, _A2, _A3) a b
    | a, b ->
        less_eq_set (_A1, _A2, _A3) a b && less_eq_set (_A1, _A2, _A3) b a;;

let rec ceq_seta (_A1, _A2, _A3)
  = (match ceq _A2 with None -> None
      | Some _ -> Some (set_eq (_A1, _A2, _A3)));;

let rec ceq_set (_A1, _A2, _A3) =
  ({ceq = ceq_seta (_A1, _A2, _A3)} : 'a set ceq);;

let set_impl_seta : ('a set, set_impla) phantom = Phantom Set_Choose;;

let set_impl_set = ({set_impl = set_impl_seta} : 'a set set_impl);;

let rec of_phantom (Phantom x) = x;;

let rec finite_UNIV_seta _A = Phantom (of_phantom (finite_UNIV _A));;

let rec finite_UNIV_set _A =
  ({finite_UNIV = finite_UNIV_seta _A} : 'a set finite_UNIV);;

let rec set_less_eq_aux_Compl_fusion
  less proper_interval g1 g2 ao s1 s2 =
    (if has_next g1 s1
      then (if has_next g2 s2
             then (let (x, s1a) = next g1 s1 in
                   let (y, s2a) = next g2 s2 in
                    (if less x y
                      then proper_interval ao (Some x) ||
                             set_less_eq_aux_Compl_fusion less proper_interval
                               g1 g2 (Some x) s1a s2
                      else (if less y x
                             then proper_interval ao (Some y) ||
                                    set_less_eq_aux_Compl_fusion less
                                      proper_interval g1 g2 (Some y) s1 s2a
                             else proper_interval ao (Some y))))
             else true)
      else true);;

let rec compl_set_less_eq_aux_fusion
  less proper_interval g1 g2 ao s1 s2 =
    (if has_next g1 s1
      then (let (x, s1a) = next g1 s1 in
             (if has_next g2 s2
               then (let (y, s2a) = next g2 s2 in
                      (if less x y
                        then not (proper_interval ao (Some x)) &&
                               compl_set_less_eq_aux_fusion less proper_interval
                                 g1 g2 (Some x) s1a s2
                        else (if less y x
                               then not (proper_interval ao (Some y)) &&
                                      compl_set_less_eq_aux_fusion less
proper_interval g1 g2 (Some y) s1 s2a
                               else not (proper_interval ao (Some y)))))
               else not (proper_interval ao (Some x)) &&
                      compl_set_less_eq_aux_fusion less proper_interval g1 g2
                        (Some x) s1a s2))
      else (if has_next g2 s2
             then (let (y, s2a) = next g2 s2 in
                    not (proper_interval ao (Some y)) &&
                      compl_set_less_eq_aux_fusion less proper_interval g1 g2
                        (Some y) s1 s2a)
             else not (proper_interval ao None)));;

let rec set_less_eq_aux_Compl
  less proper_interval ao xs ys = match less, proper_interval, ao, xs, ys with
    less, proper_interval, ao, x :: xs, y :: ys ->
      (if less x y
        then proper_interval ao (Some x) ||
               set_less_eq_aux_Compl less proper_interval (Some x) xs (y :: ys)
        else (if less y x
               then proper_interval ao (Some y) ||
                      set_less_eq_aux_Compl less proper_interval (Some y)
                        (x :: xs) ys
               else proper_interval ao (Some y)))
    | less, proper_interval, ao, xs, [] -> true
    | less, proper_interval, ao, [], ys -> true;;

let rec compl_set_less_eq_aux
  less proper_interval ao x3 x4 = match less, proper_interval, ao, x3, x4 with
    less, proper_interval, ao, x :: xs, y :: ys ->
      (if less x y
        then not (proper_interval ao (Some x)) &&
               compl_set_less_eq_aux less proper_interval (Some x) xs (y :: ys)
        else (if less y x
               then not (proper_interval ao (Some y)) &&
                      compl_set_less_eq_aux less proper_interval (Some y)
                        (x :: xs) ys
               else not (proper_interval ao (Some y))))
    | less, proper_interval, ao, x :: xs, [] ->
        not (proper_interval ao (Some x)) &&
          compl_set_less_eq_aux less proper_interval (Some x) xs []
    | less, proper_interval, ao, [], y :: ys ->
        not (proper_interval ao (Some y)) &&
          compl_set_less_eq_aux less proper_interval (Some y) [] ys
    | less, proper_interval, ao, [], [] -> not (proper_interval ao None);;

let rec lexord_eq_fusion
  less g1 g2 s1 s2 =
    (if has_next g1 s1
      then has_next g2 s2 &&
             (let (x, s1a) = next g1 s1 in
              let (y, s2a) = next g2 s2 in
               less x y ||
                 not (less y x) && lexord_eq_fusion less g1 g2 s1a s2a)
      else true);;

let rec remdups_sorted
  less x1 = match less, x1 with
    less, x :: y :: xs ->
      (if less x y then x :: remdups_sorted less (y :: xs)
        else remdups_sorted less (y :: xs))
    | less, [x] -> [x]
    | less, [] -> [];;

let rec quicksort_acc
  less ac x2 = match less, ac, x2 with
    less, ac, x :: v :: va -> quicksort_part less ac x [] [] [] (v :: va)
    | less, ac, [x] -> x :: ac
    | less, ac, [] -> ac
and quicksort_part
  less ac x lts eqs gts xa6 = match less, ac, x, lts, eqs, gts, xa6 with
    less, ac, x, lts, eqs, gts, z :: zs ->
      (if less x z then quicksort_part less ac x lts eqs (z :: gts) zs
        else (if less z x then quicksort_part less ac x (z :: lts) eqs gts zs
               else quicksort_part less ac x lts (z :: eqs) gts zs))
    | less, ac, x, lts, eqs, gts, [] ->
        quicksort_acc less (eqs @ x :: quicksort_acc less ac gts) lts;;

let rec quicksort less = quicksort_acc less [];;

let rec gen_keys
  kts x1 = match kts, x1 with
    kts, Branch (c, l, k, v, r) -> gen_keys ((k, r) :: kts) l
    | (k, t) :: kts, Empty -> k :: gen_keys kts t
    | [], Empty -> [];;

let rec keys x = gen_keys [] x;;

let rec keysa _A xa = keys (impl_ofa _A xa);;

let rec csorted_list_of_set (_A1, _A2)
  = function
    Set_Monad xs ->
      (match ccompare _A2
        with None ->
          failwith "csorted_list_of_set Set_Monad: ccompare = None"
            (fun _ -> csorted_list_of_set (_A1, _A2) (Set_Monad xs))
        | Some c -> remdups_sorted (lt_of_comp c) (quicksort (lt_of_comp c) xs))
    | DList_set dxs ->
        (match ceq _A1
          with None ->
            failwith "csorted_list_of_set DList_set: ceq = None"
              (fun _ -> csorted_list_of_set (_A1, _A2) (DList_set dxs))
          | Some _ ->
            (match ccompare _A2
              with None ->
                failwith "csorted_list_of_set DList_set: ccompare = None"
                  (fun _ -> csorted_list_of_set (_A1, _A2) (DList_set dxs))
              | Some c -> quicksort (lt_of_comp c) (list_of_dlist _A1 dxs)))
    | RBT_set rbt ->
        (match ccompare _A2
          with None ->
            failwith "csorted_list_of_set RBT_set: ccompare = None"
              (fun _ -> csorted_list_of_set (_A1, _A2) (RBT_set rbt))
          | Some _ -> keysa _A2 rbt);;

let rec emptyc _A = Mapping_RBTa Empty;;

let rec emptyb _A = Abs_dlist [];;

let rec set_empty_choose (_A1, _A2)
  = (match ccompare _A2
      with None ->
        (match ceq _A1 with None -> Set_Monad []
          | Some _ -> DList_set (emptyb _A1))
      | Some _ -> RBT_set (emptyc _A2));;

let rec set_empty (_A1, _A2)
  = function Set_Choose -> set_empty_choose (_A1, _A2)
    | Set_Monada -> Set_Monad []
    | Set_RBT -> RBT_set (emptyc _A2)
    | Set_DList -> DList_set (emptyb _A1)
    | Set_Collect -> Collect_set (fun _ -> false);;

let rec bot_set (_A1, _A2, _A3)
  = set_empty (_A1, _A2) (of_phantom (set_impl _A3));;

let rec top_set (_A1, _A2, _A3) = uminus_set (bot_set (_A1, _A2, _A3));;

let rec le_of_comp
  acomp x y = (match acomp x y with Eq -> true | Lt -> true | Gt -> false);;

let rec null = function [] -> true
               | x :: xs -> false;;

let rec lexordp_eq
  less xs ys = match less, xs, ys with
    less, x :: xs, y :: ys ->
      less x y || not (less y x) && lexordp_eq less xs ys
    | less, x :: xs, [] -> false
    | less, xs, [] -> null xs
    | less, [], ys -> true;;

let rec finite (_A1, _A2, _A3)
  = function
    Collect_set p ->
      of_phantom (finite_UNIV _A1) ||
        failwith "finite Collect_set"
          (fun _ -> finite (_A1, _A2, _A3) (Collect_set p))
    | Set_Monad xs -> true
    | Complement a ->
        (if of_phantom (finite_UNIV _A1) then true
          else (if finite (_A1, _A2, _A3) a then false
                 else failwith "finite Complement: infinite set"
                        (fun _ -> finite (_A1, _A2, _A3) (Complement a))))
    | RBT_set rbt ->
        (match ccompare _A3
          with None ->
            failwith "finite RBT_set: ccompare = None"
              (fun _ -> finite (_A1, _A2, _A3) (RBT_set rbt))
          | Some _ -> true)
    | DList_set dxs ->
        (match ceq _A2
          with None ->
            failwith "finite DList_set: ceq = None"
              (fun _ -> finite (_A1, _A2, _A3) (DList_set dxs))
          | Some _ -> true);;

let rec set_less_aux_Compl_fusion
  less proper_interval g1 g2 ao s1 s2 =
    (if has_next g1 s1
      then (let (x, s1a) = next g1 s1 in
             (if has_next g2 s2
               then (let (y, s2a) = next g2 s2 in
                      (if less x y
                        then proper_interval ao (Some x) ||
                               set_less_aux_Compl_fusion less proper_interval g1
                                 g2 (Some x) s1a s2
                        else (if less y x
                               then proper_interval ao (Some y) ||
                                      set_less_aux_Compl_fusion less
proper_interval g1 g2 (Some y) s1 s2a
                               else proper_interval ao (Some y))))
               else proper_interval ao (Some x) ||
                      set_less_aux_Compl_fusion less proper_interval g1 g2
                        (Some x) s1a s2))
      else (if has_next g2 s2
             then (let (y, s2a) = next g2 s2 in
                    proper_interval ao (Some y) ||
                      set_less_aux_Compl_fusion less proper_interval g1 g2
                        (Some y) s1 s2a)
             else proper_interval ao None));;

let rec compl_set_less_aux_fusion
  less proper_interval g1 g2 ao s1 s2 =
    has_next g1 s1 &&
      (has_next g2 s2 &&
        (let (x, s1a) = next g1 s1 in
         let (y, s2a) = next g2 s2 in
          (if less x y
            then not (proper_interval ao (Some x)) &&
                   compl_set_less_aux_fusion less proper_interval g1 g2 (Some x)
                     s1a s2
            else (if less y x
                   then not (proper_interval ao (Some y)) &&
                          compl_set_less_aux_fusion less proper_interval g1 g2
                            (Some y) s1 s2a
                   else not (proper_interval ao (Some y))))));;

let rec set_less_aux_Compl
  less proper_interval ao x3 x4 = match less, proper_interval, ao, x3, x4 with
    less, proper_interval, ao, x :: xs, y :: ys ->
      (if less x y
        then proper_interval ao (Some x) ||
               set_less_aux_Compl less proper_interval (Some x) xs (y :: ys)
        else (if less y x
               then proper_interval ao (Some y) ||
                      set_less_aux_Compl less proper_interval (Some y) (x :: xs)
                        ys
               else proper_interval ao (Some y)))
    | less, proper_interval, ao, x :: xs, [] ->
        proper_interval ao (Some x) ||
          set_less_aux_Compl less proper_interval (Some x) xs []
    | less, proper_interval, ao, [], y :: ys ->
        proper_interval ao (Some y) ||
          set_less_aux_Compl less proper_interval (Some y) [] ys
    | less, proper_interval, ao, [], [] -> proper_interval ao None;;

let rec compl_set_less_aux
  less proper_interval ao xs ys = match less, proper_interval, ao, xs, ys with
    less, proper_interval, ao, x :: xs, y :: ys ->
      (if less x y
        then not (proper_interval ao (Some x)) &&
               compl_set_less_aux less proper_interval (Some x) xs (y :: ys)
        else (if less y x
               then not (proper_interval ao (Some y)) &&
                      compl_set_less_aux less proper_interval (Some y) (x :: xs)
                        ys
               else not (proper_interval ao (Some y))))
    | less, proper_interval, ao, xs, [] -> false
    | less, proper_interval, ao, [], ys -> false;;

let rec lexord_fusion
  less g1 g2 s1 s2 =
    (if has_next g1 s1
      then (if has_next g2 s2
             then (let (x, s1a) = next g1 s1 in
                   let (y, s2a) = next g2 s2 in
                    less x y ||
                      not (less y x) && lexord_fusion less g1 g2 s1a s2a)
             else false)
      else has_next g2 s2);;

let rec lexordp
  less xs ys = match less, xs, ys with
    less, x :: xs, y :: ys -> less x y || not (less y x) && lexordp less xs ys
    | less, xs, [] -> false
    | less, [], ys -> not (null ys);;

let rec comp_of_ords
  le lt x y = (if lt x y then Lt else (if le x y then Eq else Gt));;

let rec ccompare_seta (_A1, _A2, _A3, _A4)
  = (match ccompare _A3.ccompare_cproper_interval with None -> None
      | Some _ ->
        Some (comp_of_ords (cless_eq_set (_A1, _A2, _A3, _A4))
               (cless_set (_A1, _A2, _A3, _A4))))
and cless_set (_A1, _A2, _A3, _A4)
  a b = match a, b with
    Complement (RBT_set rbt1), RBT_set rbt2 ->
      (match ccompare _A3.ccompare_cproper_interval
        with None ->
          failwith "cless_set (Complement RBT_set) RBT_set: ccompare = None"
            (fun _ ->
              cless_set (_A1, _A2, _A3, _A4) (Complement (RBT_set rbt1))
                (RBT_set rbt2))
        | Some c ->
          finite (_A1, _A2, _A3.ccompare_cproper_interval)
            (top_set (_A2, _A3.ccompare_cproper_interval, _A4)) &&
            compl_set_less_aux_fusion (lt_of_comp c) (cproper_interval _A3)
              rbt_keys_generator rbt_keys_generator None
              (init _A3.ccompare_cproper_interval rbt1)
              (init _A3.ccompare_cproper_interval rbt2))
    | RBT_set rbt1, Complement (RBT_set rbt2) ->
        (match ccompare _A3.ccompare_cproper_interval
          with None ->
            failwith "cless_set RBT_set (Complement RBT_set): ccompare = None"
              (fun _ ->
                cless_set (_A1, _A2, _A3, _A4) (RBT_set rbt1)
                  (Complement (RBT_set rbt2)))
          | Some c ->
            (if finite (_A1, _A2, _A3.ccompare_cproper_interval)
                  (top_set (_A2, _A3.ccompare_cproper_interval, _A4))
              then set_less_aux_Compl_fusion (lt_of_comp c)
                     (cproper_interval _A3) rbt_keys_generator
                     rbt_keys_generator None
                     (init _A3.ccompare_cproper_interval rbt1)
                     (init _A3.ccompare_cproper_interval rbt2)
              else true))
    | RBT_set rbta, RBT_set rbt ->
        (match ccompare _A3.ccompare_cproper_interval
          with None ->
            failwith "cless_set RBT_set RBT_set: ccompare = None"
              (fun _ ->
                cless_set (_A1, _A2, _A3, _A4) (RBT_set rbta) (RBT_set rbt))
          | Some c ->
            lexord_fusion (fun x y -> lt_of_comp c y x) rbt_keys_generator
              rbt_keys_generator (init _A3.ccompare_cproper_interval rbta)
              (init _A3.ccompare_cproper_interval rbt))
    | Complement a, Complement b ->
        (match ccompare _A3.ccompare_cproper_interval
          with None ->
            failwith "cless_set Complement Complement: ccompare = None"
              (fun _ ->
                cless_set (_A1, _A2, _A3, _A4) (Complement a) (Complement b))
          | Some _ -> lt_of_comp (the (ccompare_seta (_A1, _A2, _A3, _A4))) b a)
    | Complement a, b ->
        (match ccompare _A3.ccompare_cproper_interval
          with None ->
            failwith "cless_set Complement1: ccompare = None"
              (fun _ -> cless_set (_A1, _A2, _A3, _A4) (Complement a) b)
          | Some c ->
            (if finite (_A1, _A2, _A3.ccompare_cproper_interval) a &&
                  finite (_A1, _A2, _A3.ccompare_cproper_interval) b
              then finite (_A1, _A2, _A3.ccompare_cproper_interval)
                     (top_set (_A2, _A3.ccompare_cproper_interval, _A4)) &&
                     compl_set_less_aux (lt_of_comp c) (cproper_interval _A3)
                       None
                       (csorted_list_of_set (_A2, _A3.ccompare_cproper_interval)
                         a)
                       (csorted_list_of_set (_A2, _A3.ccompare_cproper_interval)
                         b)
              else failwith "cless_set Complement1: infinite set"
                     (fun _ ->
                       cless_set (_A1, _A2, _A3, _A4) (Complement a) b)))
    | a, Complement b ->
        (match ccompare _A3.ccompare_cproper_interval
          with None ->
            failwith "cless_set Complement2: ccompare = None"
              (fun _ -> cless_set (_A1, _A2, _A3, _A4) a (Complement b))
          | Some c ->
            (if finite (_A1, _A2, _A3.ccompare_cproper_interval) a &&
                  finite (_A1, _A2, _A3.ccompare_cproper_interval) b
              then (if finite (_A1, _A2, _A3.ccompare_cproper_interval)
                         (top_set (_A2, _A3.ccompare_cproper_interval, _A4))
                     then set_less_aux_Compl (lt_of_comp c)
                            (cproper_interval _A3) None
                            (csorted_list_of_set
                              (_A2, _A3.ccompare_cproper_interval) a)
                            (csorted_list_of_set
                              (_A2, _A3.ccompare_cproper_interval) b)
                     else true)
              else failwith "cless_set Complement2: infinite set"
                     (fun _ ->
                       cless_set (_A1, _A2, _A3, _A4) a (Complement b))))
    | a, b ->
        (match ccompare _A3.ccompare_cproper_interval
          with None ->
            failwith "cless_set: ccompare = None"
              (fun _ -> cless_set (_A1, _A2, _A3, _A4) a b)
          | Some c ->
            (if finite (_A1, _A2, _A3.ccompare_cproper_interval) a &&
                  finite (_A1, _A2, _A3.ccompare_cproper_interval) b
              then lexordp (fun x y -> lt_of_comp c y x)
                     (csorted_list_of_set (_A2, _A3.ccompare_cproper_interval)
                       a)
                     (csorted_list_of_set (_A2, _A3.ccompare_cproper_interval)
                       b)
              else failwith "cless_set: infinite set"
                     (fun _ -> cless_set (_A1, _A2, _A3, _A4) a b)))
and cless_eq_set (_A1, _A2, _A3, _A4)
  a b = match a, b with
    Complement (RBT_set rbt1), RBT_set rbt2 ->
      (match ccompare _A3.ccompare_cproper_interval
        with None ->
          failwith "cless_eq_set (Complement RBT_set) RBT_set: ccompare = None"
            (fun _ ->
              cless_eq_set (_A1, _A2, _A3, _A4) (Complement (RBT_set rbt1))
                (RBT_set rbt2))
        | Some c ->
          finite (_A1, _A2, _A3.ccompare_cproper_interval)
            (top_set (_A2, _A3.ccompare_cproper_interval, _A4)) &&
            compl_set_less_eq_aux_fusion (lt_of_comp c) (cproper_interval _A3)
              rbt_keys_generator rbt_keys_generator None
              (init _A3.ccompare_cproper_interval rbt1)
              (init _A3.ccompare_cproper_interval rbt2))
    | RBT_set rbt1, Complement (RBT_set rbt2) ->
        (match ccompare _A3.ccompare_cproper_interval
          with None ->
            failwith
              "cless_eq_set RBT_set (Complement RBT_set): ccompare = None"
              (fun _ ->
                cless_eq_set (_A1, _A2, _A3, _A4) (RBT_set rbt1)
                  (Complement (RBT_set rbt2)))
          | Some c ->
            (if finite (_A1, _A2, _A3.ccompare_cproper_interval)
                  (top_set (_A2, _A3.ccompare_cproper_interval, _A4))
              then set_less_eq_aux_Compl_fusion (lt_of_comp c)
                     (cproper_interval _A3) rbt_keys_generator
                     rbt_keys_generator None
                     (init _A3.ccompare_cproper_interval rbt1)
                     (init _A3.ccompare_cproper_interval rbt2)
              else true))
    | RBT_set rbta, RBT_set rbt ->
        (match ccompare _A3.ccompare_cproper_interval
          with None ->
            failwith "cless_eq_set RBT_set RBT_set: ccompare = None"
              (fun _ ->
                cless_eq_set (_A1, _A2, _A3, _A4) (RBT_set rbta) (RBT_set rbt))
          | Some c ->
            lexord_eq_fusion (fun x y -> lt_of_comp c y x) rbt_keys_generator
              rbt_keys_generator (init _A3.ccompare_cproper_interval rbta)
              (init _A3.ccompare_cproper_interval rbt))
    | Complement a, Complement b ->
        (match ccompare _A3.ccompare_cproper_interval
          with None ->
            failwith "cless_eq_set Complement Complement: ccompare = None"
              (fun _ ->
                le_of_comp (the (ccompare_seta (_A1, _A2, _A3, _A4)))
                  (Complement a) (Complement b))
          | Some _ -> cless_eq_set (_A1, _A2, _A3, _A4) b a)
    | Complement a, b ->
        (match ccompare _A3.ccompare_cproper_interval
          with None ->
            failwith "cless_eq_set Complement1: ccompare = None"
              (fun _ -> cless_eq_set (_A1, _A2, _A3, _A4) (Complement a) b)
          | Some c ->
            (if finite (_A1, _A2, _A3.ccompare_cproper_interval) a &&
                  finite (_A1, _A2, _A3.ccompare_cproper_interval) b
              then finite (_A1, _A2, _A3.ccompare_cproper_interval)
                     (top_set (_A2, _A3.ccompare_cproper_interval, _A4)) &&
                     compl_set_less_eq_aux (lt_of_comp c) (cproper_interval _A3)
                       None
                       (csorted_list_of_set (_A2, _A3.ccompare_cproper_interval)
                         a)
                       (csorted_list_of_set (_A2, _A3.ccompare_cproper_interval)
                         b)
              else failwith "cless_eq_set Complement1: infinite set"
                     (fun _ ->
                       cless_eq_set (_A1, _A2, _A3, _A4) (Complement a) b)))
    | a, Complement b ->
        (match ccompare _A3.ccompare_cproper_interval
          with None ->
            failwith "cless_eq_set Complement2: ccompare = None"
              (fun _ -> cless_eq_set (_A1, _A2, _A3, _A4) a (Complement b))
          | Some c ->
            (if finite (_A1, _A2, _A3.ccompare_cproper_interval) a &&
                  finite (_A1, _A2, _A3.ccompare_cproper_interval) b
              then (if finite (_A1, _A2, _A3.ccompare_cproper_interval)
                         (top_set (_A2, _A3.ccompare_cproper_interval, _A4))
                     then set_less_eq_aux_Compl (lt_of_comp c)
                            (cproper_interval _A3) None
                            (csorted_list_of_set
                              (_A2, _A3.ccompare_cproper_interval) a)
                            (csorted_list_of_set
                              (_A2, _A3.ccompare_cproper_interval) b)
                     else true)
              else failwith "cless_eq_set Complement2: infinite set"
                     (fun _ ->
                       cless_eq_set (_A1, _A2, _A3, _A4) a (Complement b))))
    | a, b ->
        (match ccompare _A3.ccompare_cproper_interval
          with None ->
            failwith "cless_eq_set: ccompare = None"
              (fun _ -> cless_eq_set (_A1, _A2, _A3, _A4) a b)
          | Some c ->
            (if finite (_A1, _A2, _A3.ccompare_cproper_interval) a &&
                  finite (_A1, _A2, _A3.ccompare_cproper_interval) b
              then lexordp_eq (fun x y -> lt_of_comp c y x)
                     (csorted_list_of_set (_A2, _A3.ccompare_cproper_interval)
                       a)
                     (csorted_list_of_set (_A2, _A3.ccompare_cproper_interval)
                       b)
              else failwith "cless_eq_set: infinite set"
                     (fun _ -> cless_eq_set (_A1, _A2, _A3, _A4) a b)));;

let rec ccompare_set (_A1, _A2, _A3, _A4) =
  ({ccompare = ccompare_seta (_A1, _A2, _A3, _A4)} : 'a set ccompare);;

type mapping_impla = Mapping_Choose | Mapping_Assoc_List | Mapping_RBT |
  Mapping_Mapping;;

let mapping_impl_seta : ('a set, mapping_impla) phantom
  = Phantom Mapping_Choose;;

type 'a mapping_impl = {mapping_impl : ('a, mapping_impla) phantom};;
let mapping_impl _A = _A.mapping_impl;;

let mapping_impl_set =
  ({mapping_impl = mapping_impl_seta} : 'a set mapping_impl);;

let rec enum_all_bool p = p false && p true;;

let rec enum_ex_bool p = p false || p true;;

let enum_boola : bool list = [false; true];;

let countable_bool = (() : bool countable);;

let finite_bool = ({countable_finite = countable_bool} : bool finite);;

let enum_bool =
  ({finite_enum = finite_bool; enum = enum_boola; enum_all = enum_all_bool;
     enum_ex = enum_ex_bool}
    : bool enum);;

let rec equal_boola p pa = match p, pa with p, true -> p
                      | p, false -> not p
                      | true, p -> p
                      | false, p -> not p;;

let equal_bool = ({equal = equal_boola} : bool equal);;

let rec comparator_bool x0 x1 = match x0, x1 with false, false -> Eq
                          | false, true -> Lt
                          | true, true -> Eq
                          | true, false -> Gt;;

let rec compare_bool x = comparator_bool x;;

let ccompare_boola : (bool -> bool -> ordera) option = Some compare_bool;;

let ccompare_bool = ({ccompare = ccompare_boola} : bool ccompare);;

let rec equal_proda _A _B (x1, x2) (y1, y2) = eq _A x1 y1 && eq _B x2 y2;;

type 'a plus = {plus : 'a -> 'a -> 'a};;
let plus _A = _A.plus;;

type 'a semigroup_add = {plus_semigroup_add : 'a plus};;

type 'a ab_semigroup_add = {semigroup_add_ab_semigroup_add : 'a semigroup_add};;

type 'a zero = {zero : 'a};;
let zero _A = _A.zero;;

type 'a monoid_add =
  {semigroup_add_monoid_add : 'a semigroup_add; zero_monoid_add : 'a zero};;

type 'a comm_monoid_add =
  {ab_semigroup_add_comm_monoid_add : 'a ab_semigroup_add;
    monoid_add_comm_monoid_add : 'a monoid_add};;

type 'a embed_nat = {iota : nat -> 'a};;
let iota _A = _A.iota;;

type 'a tfin = {tfin : 'a set};;
let tfin _A = _A.tfin;;

type 'a timestamp =
  {comm_monoid_add_timestamp : 'a comm_monoid_add;
    semilattice_sup_timestamp : 'a semilattice_sup;
    embed_nat_timestamp : 'a embed_nat; tfin_timestamp : 'a tfin};;

type 'a i = Abs_I of ('a * ('a * (bool * bool)));;

let rec rep_I _A (Abs_I x) = x;;

let rec equal_prod _A _B = ({equal = equal_proda _A _B} : ('a * 'b) equal);;

let rec equal_I (_A1, _A2)
  x xb =
    equal_proda _A1 (equal_prod _A1 (equal_prod equal_bool equal_bool))
      (rep_I _A2 x) (rep_I _A2 xb);;

type ('a, 'b) regex = Lookahead of ('a, 'b) formula | Symbol of ('a, 'b) formula
  | Plus of ('a, 'b) regex * ('a, 'b) regex |
  Times of ('a, 'b) regex * ('a, 'b) regex | Star of ('a, 'b) regex
and ('a, 'b) formula = Bool of bool | Atom of 'a | Neg of ('a, 'b) formula |
  Bin of (bool -> bool -> bool) * ('a, 'b) formula * ('a, 'b) formula |
  Prev of 'b i * ('a, 'b) formula | Next of 'b i * ('a, 'b) formula |
  Since of ('a, 'b) formula * 'b i * ('a, 'b) formula |
  Until of ('a, 'b) formula * 'b i * ('a, 'b) formula |
  MatchP of 'b i * ('a, 'b) regex | MatchF of 'b i * ('a, 'b) regex;;

let rec equal_formulaa _A (_B1, _B2)
  x0 x1 = match x0, x1 with MatchP (x91, x92), MatchF (x101, x102) -> false
    | MatchF (x101, x102), MatchP (x91, x92) -> false
    | Until (x81, x82, x83), MatchF (x101, x102) -> false
    | MatchF (x101, x102), Until (x81, x82, x83) -> false
    | Until (x81, x82, x83), MatchP (x91, x92) -> false
    | MatchP (x91, x92), Until (x81, x82, x83) -> false
    | Since (x71, x72, x73), MatchF (x101, x102) -> false
    | MatchF (x101, x102), Since (x71, x72, x73) -> false
    | Since (x71, x72, x73), MatchP (x91, x92) -> false
    | MatchP (x91, x92), Since (x71, x72, x73) -> false
    | Since (x71, x72, x73), Until (x81, x82, x83) -> false
    | Until (x81, x82, x83), Since (x71, x72, x73) -> false
    | Next (x61, x62), MatchF (x101, x102) -> false
    | MatchF (x101, x102), Next (x61, x62) -> false
    | Next (x61, x62), MatchP (x91, x92) -> false
    | MatchP (x91, x92), Next (x61, x62) -> false
    | Next (x61, x62), Until (x81, x82, x83) -> false
    | Until (x81, x82, x83), Next (x61, x62) -> false
    | Next (x61, x62), Since (x71, x72, x73) -> false
    | Since (x71, x72, x73), Next (x61, x62) -> false
    | Prev (x51, x52), MatchF (x101, x102) -> false
    | MatchF (x101, x102), Prev (x51, x52) -> false
    | Prev (x51, x52), MatchP (x91, x92) -> false
    | MatchP (x91, x92), Prev (x51, x52) -> false
    | Prev (x51, x52), Until (x81, x82, x83) -> false
    | Until (x81, x82, x83), Prev (x51, x52) -> false
    | Prev (x51, x52), Since (x71, x72, x73) -> false
    | Since (x71, x72, x73), Prev (x51, x52) -> false
    | Prev (x51, x52), Next (x61, x62) -> false
    | Next (x61, x62), Prev (x51, x52) -> false
    | Bin (x41, x42, x43), MatchF (x101, x102) -> false
    | MatchF (x101, x102), Bin (x41, x42, x43) -> false
    | Bin (x41, x42, x43), MatchP (x91, x92) -> false
    | MatchP (x91, x92), Bin (x41, x42, x43) -> false
    | Bin (x41, x42, x43), Until (x81, x82, x83) -> false
    | Until (x81, x82, x83), Bin (x41, x42, x43) -> false
    | Bin (x41, x42, x43), Since (x71, x72, x73) -> false
    | Since (x71, x72, x73), Bin (x41, x42, x43) -> false
    | Bin (x41, x42, x43), Next (x61, x62) -> false
    | Next (x61, x62), Bin (x41, x42, x43) -> false
    | Bin (x41, x42, x43), Prev (x51, x52) -> false
    | Prev (x51, x52), Bin (x41, x42, x43) -> false
    | Neg x3, MatchF (x101, x102) -> false
    | MatchF (x101, x102), Neg x3 -> false
    | Neg x3, MatchP (x91, x92) -> false
    | MatchP (x91, x92), Neg x3 -> false
    | Neg x3, Until (x81, x82, x83) -> false
    | Until (x81, x82, x83), Neg x3 -> false
    | Neg x3, Since (x71, x72, x73) -> false
    | Since (x71, x72, x73), Neg x3 -> false
    | Neg x3, Next (x61, x62) -> false
    | Next (x61, x62), Neg x3 -> false
    | Neg x3, Prev (x51, x52) -> false
    | Prev (x51, x52), Neg x3 -> false
    | Neg x3, Bin (x41, x42, x43) -> false
    | Bin (x41, x42, x43), Neg x3 -> false
    | Atom x2, MatchF (x101, x102) -> false
    | MatchF (x101, x102), Atom x2 -> false
    | Atom x2, MatchP (x91, x92) -> false
    | MatchP (x91, x92), Atom x2 -> false
    | Atom x2, Until (x81, x82, x83) -> false
    | Until (x81, x82, x83), Atom x2 -> false
    | Atom x2, Since (x71, x72, x73) -> false
    | Since (x71, x72, x73), Atom x2 -> false
    | Atom x2, Next (x61, x62) -> false
    | Next (x61, x62), Atom x2 -> false
    | Atom x2, Prev (x51, x52) -> false
    | Prev (x51, x52), Atom x2 -> false
    | Atom x2, Bin (x41, x42, x43) -> false
    | Bin (x41, x42, x43), Atom x2 -> false
    | Atom x2, Neg x3 -> false
    | Neg x3, Atom x2 -> false
    | Bool x1, MatchF (x101, x102) -> false
    | MatchF (x101, x102), Bool x1 -> false
    | Bool x1, MatchP (x91, x92) -> false
    | MatchP (x91, x92), Bool x1 -> false
    | Bool x1, Until (x81, x82, x83) -> false
    | Until (x81, x82, x83), Bool x1 -> false
    | Bool x1, Since (x71, x72, x73) -> false
    | Since (x71, x72, x73), Bool x1 -> false
    | Bool x1, Next (x61, x62) -> false
    | Next (x61, x62), Bool x1 -> false
    | Bool x1, Prev (x51, x52) -> false
    | Prev (x51, x52), Bool x1 -> false
    | Bool x1, Bin (x41, x42, x43) -> false
    | Bin (x41, x42, x43), Bool x1 -> false
    | Bool x1, Neg x3 -> false
    | Neg x3, Bool x1 -> false
    | Bool x1, Atom x2 -> false
    | Atom x2, Bool x1 -> false
    | MatchF (x101, x102), MatchF (y101, y102) ->
        equal_I (_B1, _B2) x101 y101 && equal_regex _A (_B1, _B2) x102 y102
    | MatchP (x91, x92), MatchP (y91, y92) ->
        equal_I (_B1, _B2) x91 y91 && equal_regex _A (_B1, _B2) x92 y92
    | Until (x81, x82, x83), Until (y81, y82, y83) ->
        equal_formulaa _A (_B1, _B2) x81 y81 &&
          (equal_I (_B1, _B2) x82 y82 && equal_formulaa _A (_B1, _B2) x83 y83)
    | Since (x71, x72, x73), Since (y71, y72, y73) ->
        equal_formulaa _A (_B1, _B2) x71 y71 &&
          (equal_I (_B1, _B2) x72 y72 && equal_formulaa _A (_B1, _B2) x73 y73)
    | Next (x61, x62), Next (y61, y62) ->
        equal_I (_B1, _B2) x61 y61 && equal_formulaa _A (_B1, _B2) x62 y62
    | Prev (x51, x52), Prev (y51, y52) ->
        equal_I (_B1, _B2) x51 y51 && equal_formulaa _A (_B1, _B2) x52 y52
    | Bin (x41, x42, x43), Bin (y41, y42, y43) ->
        equal_funa enum_bool (equal_fun enum_bool equal_bool) x41 y41 &&
          (equal_formulaa _A (_B1, _B2) x42 y42 &&
            equal_formulaa _A (_B1, _B2) x43 y43)
    | Neg x3, Neg y3 -> equal_formulaa _A (_B1, _B2) x3 y3
    | Atom x2, Atom y2 -> eq _A x2 y2
    | Bool x1, Bool y1 -> equal_boola x1 y1
and equal_regex _A (_B1, _B2)
  x0 x1 = match x0, x1 with Times (x41, x42), Star x5 -> false
    | Star x5, Times (x41, x42) -> false
    | Plus (x31, x32), Star x5 -> false
    | Star x5, Plus (x31, x32) -> false
    | Plus (x31, x32), Times (x41, x42) -> false
    | Times (x41, x42), Plus (x31, x32) -> false
    | Symbol x2, Star x5 -> false
    | Star x5, Symbol x2 -> false
    | Symbol x2, Times (x41, x42) -> false
    | Times (x41, x42), Symbol x2 -> false
    | Symbol x2, Plus (x31, x32) -> false
    | Plus (x31, x32), Symbol x2 -> false
    | Lookahead x1, Star x5 -> false
    | Star x5, Lookahead x1 -> false
    | Lookahead x1, Times (x41, x42) -> false
    | Times (x41, x42), Lookahead x1 -> false
    | Lookahead x1, Plus (x31, x32) -> false
    | Plus (x31, x32), Lookahead x1 -> false
    | Lookahead x1, Symbol x2 -> false
    | Symbol x2, Lookahead x1 -> false
    | Star x5, Star y5 -> equal_regex _A (_B1, _B2) x5 y5
    | Times (x41, x42), Times (y41, y42) ->
        equal_regex _A (_B1, _B2) x41 y41 && equal_regex _A (_B1, _B2) x42 y42
    | Plus (x31, x32), Plus (y31, y32) ->
        equal_regex _A (_B1, _B2) x31 y31 && equal_regex _A (_B1, _B2) x32 y32
    | Symbol x2, Symbol y2 -> equal_formulaa _A (_B1, _B2) x2 y2
    | Lookahead x1, Lookahead y1 -> equal_formulaa _A (_B1, _B2) x1 y1;;

let rec equal_formula _A (_B1, _B2) =
  ({equal = equal_formulaa _A (_B1, _B2)} : ('a, 'b) formula equal);;

let rec equal_list _A
  x0 x1 = match x0, x1 with [], x21 :: x22 -> false
    | x21 :: x22, [] -> false
    | x21 :: x22, y21 :: y22 -> eq _A x21 y21 && equal_list _A x22 y22
    | [], [] -> true;;

let rec equal_iarraya _A
  asa bs = equal_list _A (Array.to_list asa) (Array.to_list bs);;

let rec equal_iarray _A = ({equal = equal_iarraya _A} : ('a array) equal);;

let rec comparator_list
  comp_a x1 x2 = match comp_a, x1, x2 with
    comp_a, x :: xa, y :: ya ->
      (match comp_a x y with Eq -> comparator_list comp_a xa ya | Lt -> Lt
        | Gt -> Gt)
    | comp_a, x :: xa, [] -> Gt
    | comp_a, [], y :: ya -> Lt
    | comp_a, [], [] -> Eq;;

let rec ccompare_list _A
  = (match ccompare _A with None -> None
      | Some comp_a -> Some (comparator_list comp_a));;

let rec ccompare_iarraya _A
  = (match ccompare_list _A with None -> None
      | Some c -> Some (fun xs ys -> c (Array.to_list xs) (Array.to_list ys)));;

let rec ccompare_iarray _A =
  ({ccompare = ccompare_iarraya _A} : ('a array) ccompare);;

let mapping_impl_iarraya : (('a array), mapping_impla) phantom
  = Phantom Mapping_RBT;;

let mapping_impl_iarray =
  ({mapping_impl = mapping_impl_iarraya} : ('a array) mapping_impl);;

let equal_literal = ({equal = (fun a b -> ((a : string) = b))} : string equal);;

let ord_literal =
  ({less_eq = (fun a b -> ((a : string) <= b));
     less = (fun a b -> ((a : string) < b))}
    : string ord);;

let preorder_literal = ({ord_preorder = ord_literal} : string preorder);;

let order_literal = ({preorder_order = preorder_literal} : string order);;

let ceq_literala : (string -> string -> bool) option
  = Some (fun a b -> ((a : string) = b));;

let ceq_literal = ({ceq = ceq_literala} : string ceq);;

let set_impl_literala : (string, set_impla) phantom = Phantom Set_RBT;;

let set_impl_literal = ({set_impl = set_impl_literala} : string set_impl);;

let linorder_literal = ({order_linorder = order_literal} : string linorder);;

let rec compare_literal x = comparator_of (equal_literal, linorder_literal) x;;

let ccompare_literala : (string -> string -> ordera) option
  = Some compare_literal;;

let ccompare_literal = ({ccompare = ccompare_literala} : string ccompare);;

type enat = Enat of nat | Infinity_enat;;

let rec equal_enata x0 x1 = match x0, x1 with Enat nat, Infinity_enat -> false
                      | Infinity_enat, Enat nat -> false
                      | Enat nata, Enat nat -> equal_nata nata nat
                      | Infinity_enat, Infinity_enat -> true;;

let equal_enat = ({equal = equal_enata} : enat equal);;

let rec plus_enata q qa = match q, qa with q, Infinity_enat -> Infinity_enat
                     | Infinity_enat, q -> Infinity_enat
                     | Enat m, Enat n -> Enat (plus_nat m n);;

let plus_enat = ({plus = plus_enata} : enat plus);;

let zero_enata : enat = Enat zero_nat;;

let zero_enat = ({zero = zero_enata} : enat zero);;

let rec less_eq_enat q x1 = match q, x1 with Infinity_enat, Enat n -> false
                       | q, Infinity_enat -> true
                       | Enat m, Enat n -> less_eq_nat m n;;

let rec less_enat x0 q = match x0, q with Infinity_enat, q -> false
                    | Enat m, Infinity_enat -> true
                    | Enat m, Enat n -> less_nat m n;;

let ord_enat = ({less_eq = less_eq_enat; less = less_enat} : enat ord);;

let rec sup_enata x = max ord_enat x;;

let sup_enat = ({sup = sup_enata} : enat sup);;

let tfin_enata : enat set
  = Collect_set (fun x -> not (equal_enata x Infinity_enat));;

let tfin_enat = ({tfin = tfin_enata} : enat tfin);;

let preorder_enat = ({ord_preorder = ord_enat} : enat preorder);;

let order_enat = ({preorder_order = preorder_enat} : enat order);;

let ceq_enata : (enat -> enat -> bool) option = Some equal_enata;;

let ceq_enat = ({ceq = ceq_enata} : enat ceq);;

let semigroup_add_enat =
  ({plus_semigroup_add = plus_enat} : enat semigroup_add);;

let monoid_add_enat =
  ({semigroup_add_monoid_add = semigroup_add_enat; zero_monoid_add = zero_enat}
    : enat monoid_add);;

let rec iota_enat n = Enat n;;

let embed_nat_enat = ({iota = iota_enat} : enat embed_nat);;

let semilattice_sup_enat =
  ({sup_semilattice_sup = sup_enat; order_semilattice_sup = order_enat} :
    enat semilattice_sup);;

let ab_semigroup_add_enat =
  ({semigroup_add_ab_semigroup_add = semigroup_add_enat} :
    enat ab_semigroup_add);;

let comm_monoid_add_enat =
  ({ab_semigroup_add_comm_monoid_add = ab_semigroup_add_enat;
     monoid_add_comm_monoid_add = monoid_add_enat}
    : enat comm_monoid_add);;

let timestamp_enat =
  ({comm_monoid_add_timestamp = comm_monoid_add_enat;
     semilattice_sup_timestamp = semilattice_sup_enat;
     embed_nat_timestamp = embed_nat_enat; tfin_timestamp = tfin_enat}
    : enat timestamp);;

let ccompare_enata : (enat -> enat -> ordera) option
  = Some (fun x y ->
           (if equal_enata x y then Eq
             else (if less_enat x y then Lt else Gt)));;

let ccompare_enat = ({ccompare = ccompare_enata} : enat ccompare);;

let rec comparator_prod
  comp_a comp_b (x, xa) (y, ya) =
    (match comp_a x y with Eq -> comp_b xa ya | Lt -> Lt | Gt -> Gt);;

let rec ccompare_proda _A _B
  = (match ccompare _A with None -> None
      | Some comp_a ->
        (match ccompare _B with None -> None
          | Some comp_b -> Some (comparator_prod comp_a comp_b)));;

let rec ccompare_prod _A _B =
  ({ccompare = ccompare_proda _A _B} : ('a * 'b) ccompare);;

let rec mapping_impl_choose2
  x y = match x, y with Mapping_RBT, Mapping_RBT -> Mapping_RBT
    | Mapping_Assoc_List, Mapping_Assoc_List -> Mapping_Assoc_List
    | Mapping_Mapping, Mapping_Mapping -> Mapping_Mapping
    | x, y -> Mapping_Choose;;

let rec mapping_impl_proda _A _B
  = Phantom
      (mapping_impl_choose2 (of_phantom (mapping_impl _A))
        (of_phantom (mapping_impl _B)));;

let rec mapping_impl_prod _A _B =
  ({mapping_impl = mapping_impl_proda _A _B} : ('a * 'b) mapping_impl);;

type ('b, 'a) alist = Alist of ('b * 'a) list;;

type transition = Eps_trans of nat * nat | Symb_trans of nat |
  Split_trans of nat * nat;;

type ('a, 'b) mapping = Assoc_List_Mapping of ('a, 'b) alist |
  RBT_Mapping of ('a, 'b) mapping_rbt | Mapping of ('a -> 'b option);;

type ('a, 'b, 'c, 'd, 'e, 'f) window_ext =
  Window_ext of
    (('b * 'a), 'b) mapping * ('b, bool) mapping * nat * 'd * 'e * nat * 'd *
      'e * ('b * ('b * ('c * nat) option)) list * ('b * 'c) list * 'f;;

type ('a, 'b, 'c) vydra_aux = VYDRA_None | VYDRA_Bool of bool * 'c |
  VYDRA_Atom of 'a * 'c | VYDRA_Neg of ('a, 'b, 'c) vydra_aux |
  VYDRA_Bin of
    (bool -> bool -> bool) * ('a, 'b, 'c) vydra_aux * ('a, 'b, 'c) vydra_aux
  | VYDRA_Prev of 'b i * ('a, 'b, 'c) vydra_aux * 'c * ('b * bool) option |
  VYDRA_Next of 'b i * ('a, 'b, 'c) vydra_aux * 'c * 'b option |
  VYDRA_Since of
    'b i * ('a, 'b, 'c) vydra_aux * ('a, 'b, 'c) vydra_aux * ('c * 'b) option *
      nat * nat * nat option * 'b option
  | VYDRA_Until of
      'b i * ('c * 'b) option * ('a, 'b, 'c) vydra_aux *
        ('a, 'b, 'c) vydra_aux * ('c * 'b) option * nat *
        ('b * (bool * bool)) option
  | VYDRA_MatchP of
      'b i * transition array * nat *
        ((bool array), nat set, 'b, (('c * 'b) option),
          (('a, 'b, 'c) vydra_aux list), unit)
          window_ext
  | VYDRA_MatchF of
      'b i * transition array * nat *
        ((bool array), nat set, 'b, (('c * 'b) option),
          (('a, 'b, 'c) vydra_aux list), unit)
          window_ext;;

type ('a, 'b) regexa = Test of ('a, 'b) formulaa | Wild |
  Plusa of ('a, 'b) regexa * ('a, 'b) regexa |
  Timesa of ('a, 'b) regexa * ('a, 'b) regexa | Stara of ('a, 'b) regexa
and ('a, 'b) formulaa = Boola of bool | Atoma of 'a | Nega of ('a, 'b) formulaa
  | Bina of (bool -> bool -> bool) * ('a, 'b) formulaa * ('a, 'b) formulaa |
  Preva of 'b i * ('a, 'b) formulaa | Nexta of 'b i * ('a, 'b) formulaa |
  Sincea of ('a, 'b) formulaa * 'b i * ('a, 'b) formulaa |
  Untila of ('a, 'b) formulaa * 'b i * ('a, 'b) formulaa |
  MatchPa of 'b i * ('a, 'b) regexa | MatchFa of 'b i * ('a, 'b) regexa;;

type ('a, 'b, 'c, 'd, 'e, 'f) args_ext =
  Args_ext of
    'b * ('b -> 'a -> 'b) * ('b -> bool) * ('d -> ('d * 'c) option) *
      ('d -> 'c option) * ('e -> ('e * 'a) option) * 'f;;

type ('b, 'a) comp_fun_idem = Abs_comp_fun_idem of ('b -> 'a -> 'a);;

type 'a semilattice_set = Abs_semilattice_set of ('a -> 'a -> 'a);;

let rec eps _B = function Lookahead phi -> true
                 | Symbol phi -> false
                 | Plus (r, s) -> eps _B r || eps _B s
                 | Times (r, s) -> eps _B r && eps _B s
                 | Star r -> true;;

let rec nth
  (x :: xs) n =
    (if equal_nata n zero_nat then x else nth xs (minus_nat n one_nat));;

let rec upt i j = (if less_nat i j then i :: upt (suc i) j else []);;

let rec foldb _A x xc = folda (fun a _ -> x a) (impl_ofa _A xc);;

let rec map f x1 = match f, x1 with f, [] -> []
              | f, x21 :: x22 -> f x21 :: map f x22;;

let rec fun_upda equal f aa b a = (if equal aa a then b else f a);;

let rec balance_right
  a k x xa3 = match a, k, x, xa3 with
    a, k, x, Branch (R, b, s, y, c) ->
      Branch (R, a, k, x, Branch (B, b, s, y, c))
    | Branch (B, a, k, x, b), s, y, Empty ->
        balance (Branch (R, a, k, x, b)) s y Empty
    | Branch (B, a, k, x, b), s, y, Branch (B, va, vb, vc, vd) ->
        balance (Branch (R, a, k, x, b)) s y (Branch (B, va, vb, vc, vd))
    | Branch (R, a, k, x, Branch (B, b, s, y, c)), t, z, Empty ->
        Branch (R, balance (paint R a) k x b, s, y, Branch (B, c, t, z, Empty))
    | Branch (R, a, k, x, Branch (B, b, s, y, c)), t, z,
        Branch (B, va, vb, vc, vd)
        -> Branch
             (R, balance (paint R a) k x b, s, y,
               Branch (B, c, t, z, Branch (B, va, vb, vc, vd)))
    | Empty, k, x, Empty -> Empty
    | Branch (R, va, vb, vc, Empty), k, x, Empty -> Empty
    | Branch (R, va, vb, vc, Branch (R, ve, vf, vg, vh)), k, x, Empty -> Empty
    | Empty, k, x, Branch (B, va, vb, vc, vd) -> Empty
    | Branch (R, ve, vf, vg, Empty), k, x, Branch (B, va, vb, vc, vd) -> Empty
    | Branch (R, ve, vf, vg, Branch (R, vi, vj, vk, vl)), k, x,
        Branch (B, va, vb, vc, vd)
        -> Empty;;

let rec balance_left
  x0 s y c = match x0, s, y, c with
    Branch (R, a, k, x, b), s, y, c ->
      Branch (R, Branch (B, a, k, x, b), s, y, c)
    | Empty, k, x, Branch (B, a, s, y, b) ->
        balance Empty k x (Branch (R, a, s, y, b))
    | Branch (B, va, vb, vc, vd), k, x, Branch (B, a, s, y, b) ->
        balance (Branch (B, va, vb, vc, vd)) k x (Branch (R, a, s, y, b))
    | Empty, k, x, Branch (R, Branch (B, a, s, y, b), t, z, c) ->
        Branch (R, Branch (B, Empty, k, x, a), s, y, balance b t z (paint R c))
    | Branch (B, va, vb, vc, vd), k, x,
        Branch (R, Branch (B, a, s, y, b), t, z, c)
        -> Branch
             (R, Branch (B, Branch (B, va, vb, vc, vd), k, x, a), s, y,
               balance b t z (paint R c))
    | Empty, k, x, Empty -> Empty
    | Empty, k, x, Branch (R, Empty, vb, vc, vd) -> Empty
    | Empty, k, x, Branch (R, Branch (R, ve, vf, vg, vh), vb, vc, vd) -> Empty
    | Branch (B, va, vb, vc, vd), k, x, Empty -> Empty
    | Branch (B, va, vb, vc, vd), k, x, Branch (R, Empty, vf, vg, vh) -> Empty
    | Branch (B, va, vb, vc, vd), k, x,
        Branch (R, Branch (R, vi, vj, vk, vl), vf, vg, vh)
        -> Empty;;

let rec combine
  xa0 x = match xa0, x with Empty, x -> x
    | Branch (v, va, vb, vc, vd), Empty -> Branch (v, va, vb, vc, vd)
    | Branch (R, a, k, x, b), Branch (R, c, s, y, d) ->
        (match combine b c
          with Empty -> Branch (R, a, k, x, Branch (R, Empty, s, y, d))
          | Branch (R, b2, t, z, c2) ->
            Branch (R, Branch (R, a, k, x, b2), t, z, Branch (R, c2, s, y, d))
          | Branch (B, b2, t, z, c2) ->
            Branch (R, a, k, x, Branch (R, Branch (B, b2, t, z, c2), s, y, d)))
    | Branch (B, a, k, x, b), Branch (B, c, s, y, d) ->
        (match combine b c
          with Empty -> balance_left a k x (Branch (B, Empty, s, y, d))
          | Branch (R, b2, t, z, c2) ->
            Branch (R, Branch (B, a, k, x, b2), t, z, Branch (B, c2, s, y, d))
          | Branch (B, b2, t, z, c2) ->
            balance_left a k x (Branch (B, Branch (B, b2, t, z, c2), s, y, d)))
    | Branch (B, va, vb, vc, vd), Branch (R, b, k, x, c) ->
        Branch (R, combine (Branch (B, va, vb, vc, vd)) b, k, x, c)
    | Branch (R, a, k, x, b), Branch (B, va, vb, vc, vd) ->
        Branch (R, a, k, x, combine b (Branch (B, va, vb, vc, vd)));;

let rec rbt_comp_del
  c x xa2 = match c, x, xa2 with c, x, Empty -> Empty
    | c, x, Branch (uu, a, y, s, b) ->
        (match c x y with Eq -> combine a b
          | Lt -> rbt_comp_del_from_left c x a y s b
          | Gt -> rbt_comp_del_from_right c x a y s b)
and rbt_comp_del_from_left
  c x xa2 y s b = match c, x, xa2, y, s, b with
    c, x, Branch (B, lt, z, v, rt), y, s, b ->
      balance_left (rbt_comp_del c x (Branch (B, lt, z, v, rt))) y s b
    | c, x, Empty, y, s, b -> Branch (R, rbt_comp_del c x Empty, y, s, b)
    | c, x, Branch (R, va, vb, vc, vd), y, s, b ->
        Branch (R, rbt_comp_del c x (Branch (R, va, vb, vc, vd)), y, s, b)
and rbt_comp_del_from_right
  c x a y s xa5 = match c, x, a, y, s, xa5 with
    c, x, a, y, s, Branch (B, lt, z, v, rt) ->
      balance_right a y s (rbt_comp_del c x (Branch (B, lt, z, v, rt)))
    | c, x, a, y, s, Empty -> Branch (R, a, y, s, rbt_comp_del c x Empty)
    | c, x, a, y, s, Branch (R, va, vb, vc, vd) ->
        Branch (R, a, y, s, rbt_comp_del c x (Branch (R, va, vb, vc, vd)));;

let rec rbt_comp_delete c k t = paint B (rbt_comp_del c k t);;

let rec delete _A
  xb xc =
    Mapping_RBTa (rbt_comp_delete (the (ccompare _A)) xb (impl_ofa _A xc));;

let rec list_remove1
  equal x xa2 = match equal, x, xa2 with
    equal, x, y :: xs ->
      (if equal x y then xs else y :: list_remove1 equal x xs)
    | equal, x, [] -> [];;

let rec removea _A
  xb xc = Abs_dlist (list_remove1 (the (ceq _A)) xb (list_of_dlist _A xc));;

let rec insert (_A1, _A2)
  xa x1 = match xa, x1 with
    xa, Complement x -> Complement (remove (_A1, _A2) xa x)
    | x, RBT_set rbt ->
        (match ccompare _A2
          with None ->
            failwith "insert RBT_set: ccompare = None"
              (fun _ -> insert (_A1, _A2) x (RBT_set rbt))
          | Some _ -> RBT_set (insertb _A2 x () rbt))
    | x, DList_set dxs ->
        (match ceq _A1
          with None ->
            failwith "insert DList_set: ceq = None"
              (fun _ -> insert (_A1, _A2) x (DList_set dxs))
          | Some _ -> DList_set (inserta _A1 x dxs))
    | x, Set_Monad xs -> Set_Monad (x :: xs)
    | x, Collect_set a ->
        (match ceq _A1
          with None ->
            failwith "insert Collect_set: ceq = None"
              (fun _ -> insert (_A1, _A2) x (Collect_set a))
          | Some eq -> Collect_set (fun_upda eq a x true))
and remove (_A1, _A2)
  x xa1 = match x, xa1 with
    x, Complement a -> Complement (insert (_A1, _A2) x a)
    | x, RBT_set rbt ->
        (match ccompare _A2
          with None ->
            failwith "remove RBT_set: ccompare = None"
              (fun _ -> remove (_A1, _A2) x (RBT_set rbt))
          | Some _ -> RBT_set (delete _A2 x rbt))
    | x, DList_set dxs ->
        (match ceq _A1
          with None ->
            failwith "remove DList_set: ceq = None"
              (fun _ -> remove (_A1, _A2) x (DList_set dxs))
          | Some _ -> DList_set (removea _A1 x dxs))
    | x, Collect_set a ->
        (match ceq _A1
          with None ->
            failwith "remove Collect: ceq = None"
              (fun _ -> remove (_A1, _A2) x (Collect_set a))
          | Some eq -> Collect_set (fun_upda eq a x false));;

let rec image (_A1, _A2) (_B1, _B2, _B3)
  h x1 = match h, x1 with
    h, RBT_set rbt ->
      (match ccompare _A2
        with None ->
          failwith "image RBT_set: ccompare = None"
            (fun _ -> image (_A1, _A2) (_B1, _B2, _B3) h (RBT_set rbt))
        | Some _ ->
          foldb _A2 (comp (insert (_B1, _B2)) h) rbt (bot_set (_B1, _B2, _B3)))
    | g, DList_set dxs ->
        (match ceq _A1
          with None ->
            failwith "image DList_set: ceq = None"
              (fun _ -> image (_A1, _A2) (_B1, _B2, _B3) g (DList_set dxs))
          | Some _ ->
            foldc _A1 (comp (insert (_B1, _B2)) g) dxs
              (bot_set (_B1, _B2, _B3)))
    | f, Complement (Complement b) -> image (_A1, _A2) (_B1, _B2, _B3) f b
    | f, Collect_set a ->
        failwith "image Collect_set"
          (fun _ -> image (_A1, _A2) (_B1, _B2, _B3) f (Collect_set a))
    | f, Set_Monad xs -> Set_Monad (map f xs);;

let rec sub asa n = IArray.sub' (asa, integer_of_nat n);;

let rec foldl f a x2 = match f, a, x2 with f, a, [] -> a
                | f, a, x :: xs -> foldl f (f a x) xs;;

let rec map_of _A
  x0 k = match x0, k with
    (l, v) :: ps, k -> (if eq _A l k then Some v else map_of _A ps k)
    | [], k -> None;;

let rec t0 _B
  init_hd run_hd =
    (match run_hd init_hd with None -> None | Some (e, (t, _)) -> Some (e, t));;

let rec comp_fun_idem_apply (Abs_comp_fun_idem x) = x;;

let rec set_fold_cfi (_A1, _A2)
  f b x2 = match f, b, x2 with
    f, b, RBT_set rbt ->
      (match ccompare _A2
        with None ->
          failwith "set_fold_cfi RBT_set: ccompare = None"
            (fun _ -> set_fold_cfi (_A1, _A2) f b (RBT_set rbt))
        | Some _ -> foldb _A2 (comp_fun_idem_apply f) rbt b)
    | f, b, DList_set dxs ->
        (match ceq _A1
          with None ->
            failwith "set_fold_cfi DList_set: ceq = None"
              (fun _ -> set_fold_cfi (_A1, _A2) f b (DList_set dxs))
          | Some _ -> foldc _A1 (comp_fun_idem_apply f) dxs b)
    | f, b, Set_Monad xs -> fold (comp_fun_idem_apply f) xs b
    | f, b, Collect_set p ->
        failwith "set_fold_cfi not supported on Collect_set"
          (fun _ -> set_fold_cfi (_A1, _A2) f b (Collect_set p))
    | f, b, Complement a ->
        failwith "set_fold_cfi not supported on Complement"
          (fun _ -> set_fold_cfi (_A1, _A2) f b (Complement a));;

let rec sup_cfi _A
  = Abs_comp_fun_idem (sup _A.semilattice_sup_lattice.sup_semilattice_sup);;

let rec sup_setb (_A1, _A2, _A3, _A4, _A5)
  a = (if finite
            ((finite_UNIV_set _A1),
              (ceq_set (_A2, _A3, _A4.ccompare_cproper_interval)),
              (ccompare_set (_A1, _A3, _A4, _A5)))
            a
        then set_fold_cfi
               ((ceq_set (_A2, _A3, _A4.ccompare_cproper_interval)),
                 (ccompare_set (_A1, _A3, _A4, _A5)))
               (sup_cfi (lattice_set (_A2, _A3, _A4.ccompare_cproper_interval)))
               (bot_set (_A3, _A4.ccompare_cproper_interval, _A5)) a
        else failwith "Sup: infinite"
               (fun _ -> sup_setb (_A1, _A2, _A3, _A4, _A5) a));;

let rec length asa = nat_of_integer (IArray.length' asa);;

let rec step_eps_sucs
  transs len bs q =
    (if less_nat q len
      then (match sub transs q
             with Eps_trans (p, n) ->
               (if less_nat n (length bs) && sub bs n
                 then insert (ceq_nat, ccompare_nat) p
                        (set_empty (ceq_nat, ccompare_nat)
                          (of_phantom set_impl_nata))
                 else set_empty (ceq_nat, ccompare_nat)
                        (of_phantom set_impl_nata))
             | Symb_trans _ ->
               set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)
             | Split_trans (p, pa) ->
               insert (ceq_nat, ccompare_nat) p
                 (insert (ceq_nat, ccompare_nat) pa
                   (set_empty (ceq_nat, ccompare_nat)
                     (of_phantom set_impl_nata))))
      else set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata));;

let rec step_eps_set
  transs len bs r =
    sup_setb
      (finite_UNIV_nat, cenum_nat, ceq_nat, cproper_interval_nat, set_impl_nat)
      (image (ceq_nat, ccompare_nat)
        ((ceq_set
           (cenum_nat, ceq_nat,
             cproper_interval_nat.ccompare_cproper_interval)),
          (ccompare_set
            (finite_UNIV_nat, ceq_nat, cproper_interval_nat, set_impl_nat)),
          set_impl_set)
        (step_eps_sucs transs len bs) r);;

let rec step_eps_closure_set
  transs len r bs =
    (let ra = sup_seta (ceq_nat, ccompare_nat) r (step_eps_set transs len bs r)
       in
      (if set_eq (cenum_nat, ceq_nat, ccompare_nat) r ra then r
        else step_eps_closure_set transs len ra bs));;

let rec step_symb_sucs
  transs len q =
    (if less_nat q len
      then (match sub transs q
             with Eps_trans (_, _) ->
               set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)
             | Symb_trans p ->
               insert (ceq_nat, ccompare_nat) p
                 (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata))
             | Split_trans (_, _) ->
               set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata))
      else set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata));;

let rec step_symb_set
  transs len r =
    sup_setb
      (finite_UNIV_nat, cenum_nat, ceq_nat, cproper_interval_nat, set_impl_nat)
      (image (ceq_nat, ccompare_nat)
        ((ceq_set
           (cenum_nat, ceq_nat,
             cproper_interval_nat.ccompare_cproper_interval)),
          (ccompare_set
            (finite_UNIV_nat, ceq_nat, cproper_interval_nat, set_impl_nat)),
          set_impl_set)
        (step_symb_sucs transs len) r);;

let rec delta
  transs len r bs =
    step_symb_set transs len (step_eps_closure_set transs len r bs);;

let rec impl_of (Alist x) = x;;

let rec update _A
  k v x2 = match k, v, x2 with k, v, [] -> [(k, v)]
    | k, v, p :: ps ->
        (if eq _A (fst p) k then (k, v) :: ps else p :: update _A k v ps);;

let rec updatea _A xc xd xe = Alist (update _A xc xd (impl_of xe));;

let rec fun_upd _A f a b = (fun x -> (if eq _A x a then b else f x));;

let rec updateb (_A1, _A2)
  k v x2 = match k, v, x2 with
    k, v, RBT_Mapping t ->
      (match ccompare _A1
        with None ->
          failwith "update RBT_Mapping: ccompare = None"
            (fun _ -> updateb (_A1, _A2) k v (RBT_Mapping t))
        | Some _ -> RBT_Mapping (insertb _A1 k v t))
    | k, v, Assoc_List_Mapping al -> Assoc_List_Mapping (updatea _A2 k v al)
    | k, v, Mapping m -> Mapping (fun_upd _A2 m k (Some v));;

let rec lookup _A xa = map_of _A (impl_of xa);;

let rec lookupa (_A1, _A2) = function RBT_Mapping t -> lookupb _A1 t
                             | Assoc_List_Mapping al -> lookup _A2 al;;

let rec cac (_A1, _A2)
  accept ac q =
    (match lookupa (_A1, _A2) ac q
      with None -> (let res = accept q in (res, updateb (_A1, _A2) q res ac))
      | Some v -> (v, ac));;

let rec membera _A x0 y = match x0, y with [], y -> false
                     | x :: xs, y -> eq _A x y || membera _A xs y;;

let rec rderive _B
  = function Lookahead phi -> Lookahead (Bool false)
    | Symbol phi -> Lookahead phi
    | Plus (r, s) -> Plus (rderive _B r, rderive _B s)
    | Times (r, s) ->
        (if eps _B s then Plus (rderive _B r, Times (r, rderive _B s))
          else Times (r, rderive _B s))
    | Star r -> Times (Star r, rderive _B r);;

let rec collect_subfmlas _A (_B1, _B2)
  x0 phis = match x0, phis with
    Lookahead phi, phis ->
      (if membera (equal_formula _A (_B1, _B2)) phis phi then phis
        else phis @ [phi])
    | Symbol phi, phis ->
        (if membera (equal_formula _A (_B1, _B2)) phis phi then phis
          else phis @ [phi])
    | Plus (r, s), phis ->
        collect_subfmlas _A (_B1, _B2) s (collect_subfmlas _A (_B1, _B2) r phis)
    | Times (r, s), phis ->
        collect_subfmlas _A (_B1, _B2) s (collect_subfmlas _A (_B1, _B2) r phis)
    | Star r, phis -> collect_subfmlas _A (_B1, _B2) r phis;;

let rec wf_fmla _A (_B1, _B2)
  = function Bool b -> true
    | Atom a -> true
    | Neg phi -> wf_fmla _A (_B1, _B2) phi
    | Bin (f, phi, psi) ->
        wf_fmla _A (_B1, _B2) phi && wf_fmla _A (_B1, _B2) psi
    | Prev (i, phi) -> wf_fmla _A (_B1, _B2) phi
    | Next (i, phi) -> wf_fmla _A (_B1, _B2) phi
    | Since (phi, i, psi) ->
        wf_fmla _A (_B1, _B2) phi && wf_fmla _A (_B1, _B2) psi
    | Until (phi, i, psi) ->
        wf_fmla _A (_B1, _B2) phi && wf_fmla _A (_B1, _B2) psi
    | MatchP (i, r) ->
        wf_regex _A (_B1, _B2) r &&
          list_all (wf_fmla _A (_B1, _B2)) (collect_subfmlas _A (_B1, _B2) r [])
    | MatchF (i, r) ->
        wf_regex _A (_B1, _B2) r &&
          list_all (wf_fmla _A (_B1, _B2)) (collect_subfmlas _A (_B1, _B2) r [])
and wf_regex _A (_B1, _B2)
  = function Lookahead phi -> false
    | Symbol phi -> wf_fmla _A (_B1, _B2) phi
    | Plus (r, s) -> wf_regex _A (_B1, _B2) r && wf_regex _A (_B1, _B2) s
    | Times (r, s) ->
        wf_regex _A (_B1, _B2) s &&
          (not (eps _B2 s) || wf_regex _A (_B1, _B2) r)
    | Star r -> wf_regex _A (_B1, _B2) r;;

let rec map_optiona f x1 = match f, x1 with f, None -> None
                      | f, Some x2 -> Some (f x2);;

let rec memL _A
  x xb xd =
    (match rep_I _A xd
      with (a, (_, (true, _))) ->
        less_eq
          _A.semilattice_sup_timestamp.order_semilattice_sup.preorder_order.ord_preorder
          (plus _A.comm_monoid_add_timestamp.monoid_add_comm_monoid_add.semigroup_add_monoid_add.plus_semigroup_add
            x a)
          xb
      | (a, (_, (false, _))) ->
        less _A.semilattice_sup_timestamp.order_semilattice_sup.preorder_order.ord_preorder
          (plus _A.comm_monoid_add_timestamp.monoid_add_comm_monoid_add.semigroup_add_monoid_add.plus_semigroup_add
            x a)
          xb);;

let rec until_ready _A
  i t c zo =
    (let (a, b) = (c, zo) in
      (if equal_nata a zero_nat then false
        else (match b with None -> false
               | Some (ta, (b1, b2)) -> b2 && memL _A t ta i || not b1)));;

let rec read_t _B = function None -> None
                    | Some (e, t) -> Some t;;

let rec memR _A
  x xb xd =
    (match rep_I _A xd
      with (_, (b, (_, true))) ->
        less_eq
          _A.semilattice_sup_timestamp.order_semilattice_sup.preorder_order.ord_preorder
          xb (plus _A.comm_monoid_add_timestamp.monoid_add_comm_monoid_add.semigroup_add_monoid_add.plus_semigroup_add
               x b)
      | (_, (b, (_, false))) ->
        less _A.semilattice_sup_timestamp.order_semilattice_sup.preorder_order.ord_preorder
          xb (plus _A.comm_monoid_add_timestamp.monoid_add_comm_monoid_add.semigroup_add_monoid_add.plus_semigroup_add
               x b));;

let rec while_until_cond _A
  i t = (fun (_, (_, (epsi, (c, zo)))) ->
          not (until_ready _A i t c zo) &&
            (match read_t _A epsi with None -> false
              | Some ta -> memR _A t ta i));;

let rec run_t _B
  run_hd x1 = match run_hd, x1 with run_hd, None -> None
    | run_hd, Some (e, t) ->
        (match run_hd e with None -> Some (None, t)
          | Some (ea, (ta, _)) -> Some (Some (ea, ta), t));;

let rec while_until_body _B
  run_hd run =
    (fun (vphi, (vpsi, (epsi, (c, _)))) ->
      (let Some (epsia, t) = run_t _B run_hd epsi in
        (match run vphi with None -> None
          | Some (vphia, (_, b1)) ->
            (match run vpsi with None -> None
              | Some (vpsia, (_, b2)) ->
                Some (vphia,
                       (vpsia, (epsia, (suc c, Some (t, (b1, b2))))))))));;

let rec while_since_cond _A
  i t = (fun (_, (e, (cpsi, (_, _)))) ->
          less_nat zero_nat cpsi && memL _A (the (read_t _A e)) t i);;

let rec while_since_body _B
  run_hd run =
    (fun (vpsi, (e, (cpsi, (cppsi, tppsi)))) ->
      (match run vpsi with None -> None
        | Some (vpsia, (t, b)) ->
          Some (vpsia,
                 (fst (the (run_t _B run_hd e)),
                   (minus_nat cpsi one_nat,
                     ((if b then Some cpsi else cppsi),
                       (if b then Some t else tppsi)))))));;

let rec whilea b c s = (if b s then whilea b c (c s) else s);;

let rec pred_option p z = (match z with None -> false | Some a -> p a);;

let rec map_option f z = (match z with None -> None | Some a -> f a);;

let rec while_break p f x = whilea (pred_option p) (map_option f) (Some x);;

let rec w_ac_update
  w_aca (Window_ext
          (w_st, w_ac, w_i, w_ti, w_si, w_j, w_tj, w_sj, w_s, w_e, more))
    = Window_ext
        (w_st, w_aca w_ac, w_i, w_ti, w_si, w_j, w_tj, w_sj, w_s, w_e, more);;

let rec w_read_t
  (Args_ext (w_init, w_step, w_accept, w_run_t, w_read_t, w_run_sub, more)) =
    w_read_t;;

let rec w_ti
  (Window_ext (w_st, w_ac, w_i, w_ti, w_si, w_j, w_tj, w_sj, w_s, w_e, more)) =
    w_ti;;

let rec w_j
  (Window_ext (w_st, w_ac, w_i, w_ti, w_si, w_j, w_tj, w_sj, w_s, w_e, more)) =
    w_j;;

let rec w_i
  (Window_ext (w_st, w_ac, w_i, w_ti, w_si, w_j, w_tj, w_sj, w_s, w_e, more)) =
    w_i;;

let rec matchP_loop_cond _A
  args i t =
    (fun w ->
      less_nat (w_i w) (w_j w) && memL _A (the (w_read_t args (w_ti w))) t i);;

let rec w_accept
  (Args_ext (w_init, w_step, w_accept, w_run_t, w_read_t, w_run_sub, more)) =
    w_accept;;

let rec w_tj
  (Window_ext (w_st, w_ac, w_i, w_ti, w_si, w_j, w_tj, w_sj, w_s, w_e, more)) =
    w_tj;;

let rec w_ac
  (Window_ext (w_st, w_ac, w_i, w_ti, w_si, w_j, w_tj, w_sj, w_s, w_e, more)) =
    w_ac;;

let rec w_e
  (Window_ext (w_st, w_ac, w_i, w_ti, w_si, w_j, w_tj, w_sj, w_s, w_e, more)) =
    w_e;;

let rec w_ti_update
  w_tia (Window_ext
          (w_st, w_ac, w_i, w_ti, w_si, w_j, w_tj, w_sj, w_s, w_e, more))
    = Window_ext
        (w_st, w_ac, w_i, w_tia w_ti, w_si, w_j, w_tj, w_sj, w_s, w_e, more);;

let rec w_st_update
  w_sta (Window_ext
          (w_st, w_ac, w_i, w_ti, w_si, w_j, w_tj, w_sj, w_s, w_e, more))
    = Window_ext
        (w_sta w_st, w_ac, w_i, w_ti, w_si, w_j, w_tj, w_sj, w_s, w_e, more);;

let rec w_si_update
  w_sia (Window_ext
          (w_st, w_ac, w_i, w_ti, w_si, w_j, w_tj, w_sj, w_s, w_e, more))
    = Window_ext
        (w_st, w_ac, w_i, w_ti, w_sia w_si, w_j, w_tj, w_sj, w_s, w_e, more);;

let rec w_s_update
  w_sa (Window_ext
         (w_st, w_ac, w_i, w_ti, w_si, w_j, w_tj, w_sj, w_s, w_e, more))
    = Window_ext
        (w_st, w_ac, w_i, w_ti, w_si, w_j, w_tj, w_sj, w_sa w_s, w_e, more);;

let rec w_i_update
  w_ia (Window_ext
         (w_st, w_ac, w_i, w_ti, w_si, w_j, w_tj, w_sj, w_s, w_e, more))
    = Window_ext
        (w_st, w_ac, w_ia w_i, w_ti, w_si, w_j, w_tj, w_sj, w_s, w_e, more);;

let rec w_e_update
  w_ea (Window_ext
         (w_st, w_ac, w_i, w_ti, w_si, w_j, w_tj, w_sj, w_s, w_e, more))
    = Window_ext
        (w_st, w_ac, w_i, w_ti, w_si, w_j, w_tj, w_sj, w_s, w_ea w_e, more);;

let rec w_run_sub
  (Args_ext (w_init, w_step, w_accept, w_run_t, w_read_t, w_run_sub, more)) =
    w_run_sub;;

let rec w_run_t
  (Args_ext (w_init, w_step, w_accept, w_run_t, w_read_t, w_run_sub, more)) =
    w_run_t;;

let rec w_st
  (Window_ext (w_st, w_ac, w_i, w_ti, w_si, w_j, w_tj, w_sj, w_s, w_e, more)) =
    w_st;;

let rec w_si
  (Window_ext (w_st, w_ac, w_i, w_ti, w_si, w_j, w_tj, w_sj, w_s, w_e, more)) =
    w_si;;

let rec mmap_update _A = update _A;;

let rec mmap_lookup _A = map_of _A;;

let rec w_step
  (Args_ext (w_init, w_step, w_accept, w_run_t, w_read_t, w_run_sub, more)) =
    w_step;;

let rec w_init
  (Args_ext (w_init, w_step, w_accept, w_run_t, w_read_t, w_run_sub, more)) =
    w_init;;

let rec w_s
  (Window_ext (w_st, w_ac, w_i, w_ti, w_si, w_j, w_tj, w_sj, w_s, w_e, more)) =
    w_s;;

let rec set_aux (_A1, _A2)
  = function Set_Monada -> (fun a -> Set_Monad a)
    | Set_Choose ->
        (match ccompare _A2
          with None ->
            (match ceq _A1 with None -> (fun a -> Set_Monad a)
              | Some _ ->
                foldl (fun s x -> insert (_A1, _A2) x s)
                  (DList_set (emptyb _A1)))
          | Some _ ->
            foldl (fun s x -> insert (_A1, _A2) x s) (RBT_set (emptyc _A2)))
    | impl ->
        foldl (fun s x -> insert (_A1, _A2) x s) (set_empty (_A1, _A2) impl);;

let rec set (_A1, _A2, _A3)
  xs = set_aux (_A1, _A2) (of_phantom (set_impl _A3)) xs;;

let rec mmap_keys (_A1, _A2, _A3) kvs = set (_A1, _A2, _A3) (map fst kvs);;

let rec loop_cond _A (_F1, _F2, _F3)
  j = (fun (_, (_, (i, (_, (_, (q, (s, _))))))) ->
        less _A i j &&
          not (member (_F1, _F2) q (mmap_keys (_F1, _F2, _F3) s)));;

let rec cstep (_A1, _A2) (_B1, _B2)
  step st q bs =
    (match lookupa ((ccompare_prod _A1 _B1), (equal_prod _A2 _B2)) st (q, bs)
      with None ->
        (let res = step q bs in
          (res, updateb ((ccompare_prod _A1 _B1), (equal_prod _A2 _B2)) (q, bs)
                  res st))
      | Some v -> (v, st));;

let rec mmap_combine _A
  k v c x3 = match k, v, c, x3 with k, v, c, [] -> [(k, v)]
    | k, v, c, p :: ps ->
        (let (ka, va) = p in
          (if eq _A k ka then (k, c va v) :: ps
            else p :: mmap_combine _A k v c ps));;

let rec mmap_fold _A
  m e f c r =
    foldl (fun (ra, ea) p ->
            (let ((k, v), eb) = f (p, ea) in (mmap_combine _A k v c ra, eb)))
      (r, e) m;;

let rec drop_cur
  i = (fun (q, tstp) ->
        (q, (match tstp with None -> tstp
              | Some (_, tp) -> (if equal_nata tp i then None else tstp))));;

let rec adv_d (_A1, _A2) (_B1, _B2)
  step st i b s =
    mmap_fold _A2 s st
      (fun (a, c) ->
        (let (x, v) = a in
          (fun sta ->
            (let (xa, aa) = cstep (_A1, _A2) (_B1, _B2) step sta x b in
              ((xa, drop_cur i v), aa))))
          c)
      (fun x _ -> x) [];;

let rec loop_body (_A1, _A2) (_B1, _B2)
  step accept run_t run_sub =
    (fun (st, (ac, (i, (ti, (si, (q, (s, tstp))))))) ->
      (let Some (tia, t) = run_t ti in
       let Some (sia, b) = run_sub si in
       let (sa, sta) = adv_d (_A1, _A2) (_B1, _B2) step st i b s in
       let (qa, stb) = cstep (_A1, _A2) (_B1, _B2) step sta q b in
       let (beta, aca) = cac (_A1, _A2) accept ac qa in
        (stb, (aca, (suc i,
                      (tia, (sia, (qa, (sa,
 (if beta then Some (t, i) else tstp))))))))));;

let rec adv_start (_A1, _A2) (_B1, _B2, _B3, _B4) _C
  args w =
    (let init = w_init args in
     let step = w_step args in
     let accept = w_accept args in
     let run_t = w_run_t args in
     let run_sub = w_run_sub args in
     let st = w_st w in
     let ac = w_ac w in
     let i = w_i w in
     let ti = w_ti w in
     let si = w_si w in
     let j = w_j w in
     let s = w_s w in
     let e = w_e w in
     let Some (tia, t) = run_t ti in
     let Some (sia, bs) = run_sub si in
     let (sa, sta) = adv_d (_B2, _B3) (_A1, _A2) step st i bs s in
     let ea = mmap_update _B3 (fst (the (mmap_lookup _B3 s init))) t e in
     let (st_cur, (ac_cur, (_, (_, (_, (q_cur, (s_cur, tstp_cur))))))) =
       whilea (loop_cond ord_nat (_B1, _B2, _B4) j)
         (loop_body (_B2, _B3) (_A1, _A2) step accept run_t run_sub)
         (sta, (ac, (suc i, (tia, (sia, (init, (sa, None)))))))
       in
     let sb =
       mmap_update _B3 init
         (match mmap_lookup _B3 s_cur q_cur with None -> (q_cur, tstp_cur)
           | Some (q, tstp) ->
             (match tstp with None -> (q, tstp_cur) | Some (_, _) -> (q, tstp)))
         sa
       in
      w_e_update (fun _ -> ea)
        (w_s_update (fun _ -> sb)
          (w_si_update (fun _ -> sia)
            (w_ti_update (fun _ -> tia)
              (w_i_update (fun _ -> suc i)
                (w_ac_update (fun _ -> ac_cur)
                  (w_st_update (fun _ -> st_cur) w)))))));;

let rec ex_key (_A1, _A2) _B
  x0 time accept ac = match x0, time, accept, ac with
    [], time, accept, ac -> (false, ac)
    | (q, t) :: qts, time, accept, ac ->
        (if time t
          then (match cac (_A1, _A2) accept ac q with (true, aca) -> (true, aca)
                 | (false, aca) -> ex_key (_A1, _A2) _B qts time accept aca)
          else ex_key (_A1, _A2) _B qts time accept ac);;

let rec w_tj_update
  w_tja (Window_ext
          (w_st, w_ac, w_i, w_ti, w_si, w_j, w_tj, w_sj, w_s, w_e, more))
    = Window_ext
        (w_st, w_ac, w_i, w_ti, w_si, w_j, w_tja w_tj, w_sj, w_s, w_e, more);;

let rec w_sj_update
  w_sja (Window_ext
          (w_st, w_ac, w_i, w_ti, w_si, w_j, w_tj, w_sj, w_s, w_e, more))
    = Window_ext
        (w_st, w_ac, w_i, w_ti, w_si, w_j, w_tj, w_sja w_sj, w_s, w_e, more);;

let rec w_j_update
  w_ja (Window_ext
         (w_st, w_ac, w_i, w_ti, w_si, w_j, w_tj, w_sj, w_s, w_e, more))
    = Window_ext
        (w_st, w_ac, w_i, w_ti, w_si, w_ja w_j, w_tj, w_sj, w_s, w_e, more);;

let rec w_sj
  (Window_ext (w_st, w_ac, w_i, w_ti, w_si, w_j, w_tj, w_sj, w_s, w_e, more)) =
    w_sj;;

let rec mmap_fold_s (_A1, _A2) (_B1, _B2)
  step st accept ac bs t j x7 = match step, st, accept, ac, bs, t, j, x7 with
    step, st, accept, ac, bs, t, j, [] -> ([], (st, ac))
    | step, st, accept, ac, bs, t, j, (qa, (q, tstp)) :: qbss ->
        (let (qb, sta) = cstep (_A1, _A2) (_B1, _B2) step st q bs in
         let (beta, aca) = cac (_A1, _A2) accept ac qb in
         let (qbssa, (stb, acb)) =
           mmap_fold_s (_A1, _A2) (_B1, _B2) step sta accept aca bs t j qbss in
          ((qa, (qb, (if beta then Some (t, j) else tstp))) :: qbssa,
            (stb, acb)));;

let rec adv_end (_A1, _A2) (_B1, _B2) _C
  args w =
    (let step = w_step args in
     let accept = w_accept args in
     let run_t = w_run_t args in
     let run_sub = w_run_sub args in
     let st = w_st w in
     let ac = w_ac w in
     let j = w_j w in
     let tj = w_tj w in
     let sj = w_sj w in
     let s = w_s w in
     let e = w_e w in
      (match run_t tj with None -> None
        | Some (tja, t) ->
          (match run_sub sj with None -> None
            | Some (sja, bs) ->
              (let (sa, (sta, aca)) =
                 mmap_fold_s (_B1, _B2) (_A1, _A2) step st accept ac bs t j s in
               let (ea, stb) =
                 mmap_fold _B2 e sta
                   (fun (a, b) ->
                     (let (x, y) = a in
                       (fun stb ->
                         (let aa = cstep (_B1, _B2) (_A1, _A2) step stb x bs in
                          let (q, ab) = aa in
                           ((q, y), ab))))
                       b)
                   (sup _C.semilattice_sup_timestamp.sup_semilattice_sup) []
                 in
                Some (w_e_update (fun _ -> ea)
                       (w_s_update (fun _ -> sa)
                         (w_sj_update (fun _ -> sja)
                           (w_tj_update (fun _ -> tja)
                             (w_j_update (fun _ -> suc j)
                               (w_ac_update (fun _ -> aca)
                                 (w_st_update (fun _ -> stb) w)))))))))));;

let rec eval_matchP _A
  args i w =
    (match w_read_t args (w_tj w) with None -> None
      | Some t ->
        (match
          adv_end ((ccompare_iarray ccompare_bool), (equal_iarray equal_bool))
            ((ccompare_set
               (finite_UNIV_nat, ceq_nat, cproper_interval_nat, set_impl_nat)),
              (equal_set
                (cenum_nat, ceq_nat,
                  cproper_interval_nat.ccompare_cproper_interval, equal_nat)))
            _A args w
          with None -> None
          | Some wa ->
            (let wb =
               whilea (matchP_loop_cond _A args i t)
                 (adv_start
                   ((ccompare_iarray ccompare_bool), (equal_iarray equal_bool))
                   ((ceq_set
                      (cenum_nat, ceq_nat,
                        cproper_interval_nat.ccompare_cproper_interval)),
                     (ccompare_set
                       (finite_UNIV_nat, ceq_nat, cproper_interval_nat,
                         set_impl_nat)),
                     (equal_set
                       (cenum_nat, ceq_nat,
                         cproper_interval_nat.ccompare_cproper_interval,
                         equal_nat)),
                     set_impl_set)
                   _A args)
                 wa
               in
             let (beta, ac) =
               ex_key
                 ((ccompare_set
                    (finite_UNIV_nat, ceq_nat, cproper_interval_nat,
                      set_impl_nat)),
                   (equal_set
                     (cenum_nat, ceq_nat,
                       cproper_interval_nat.ccompare_cproper_interval,
                       equal_nat)))
                 _A (w_e wb) (fun ta -> memR _A ta t i) (w_accept args)
                 (w_ac wb)
               in
              Some ((t, beta), w_ac_update (fun _ -> ac) wb))));;

let rec matchF_loop_cond _A
  args i t =
    (fun w ->
      (match w_read_t args (w_tj w) with None -> false
        | Some ta -> memR _A t ta i));;

let rec eval_matchF _A
  args i w =
    (match w_read_t args (w_ti w) with None -> None
      | Some t ->
        (match
          while_break (matchF_loop_cond _A args i t)
            (adv_end
              ((ccompare_iarray ccompare_bool), (equal_iarray equal_bool))
              ((ccompare_set
                 (finite_UNIV_nat, ceq_nat, cproper_interval_nat,
                   set_impl_nat)),
                (equal_set
                  (cenum_nat, ceq_nat,
                    cproper_interval_nat.ccompare_cproper_interval, equal_nat)))
              _A args)
            w
          with None -> None
          | Some wa ->
            (match w_read_t args (w_tj wa) with None -> None
              | Some _ ->
                (let beta =
                   (match
                     snd (the (mmap_lookup
                                (equal_set
                                  (cenum_nat, ceq_nat, ccompare_nat, equal_nat))
                                (w_s wa)
                                (insert (ceq_nat, ccompare_nat) zero_nat
                                  (set_empty (ceq_nat, ccompare_nat)
                                    (of_phantom set_impl_nata)))))
                     with None -> false | Some tstp -> memL _A t (fst tstp) i)
                   in
                  Some ((t, beta),
                         adv_start
                           ((ccompare_iarray ccompare_bool),
                             (equal_iarray equal_bool))
                           ((ceq_set
                              (cenum_nat, ceq_nat,
                                cproper_interval_nat.ccompare_cproper_interval)),
                             (ccompare_set
                               (finite_UNIV_nat, ceq_nat, cproper_interval_nat,
                                 set_impl_nat)),
                             (equal_set
                               (cenum_nat, ceq_nat,
                                 cproper_interval_nat.ccompare_cproper_interval,
                                 equal_nat)),
                             set_impl_set)
                           _A args wa)))));;

let rec init_args
  (init, (step, accept)) (run_t, read_t) run_sub =
    Args_ext (init, step, accept, run_t, read_t, run_sub, ());;

let rec list_ex p x1 = match p, x1 with p, [] -> false
                  | p, x :: xs -> p x || list_ex p xs;;

let rec run_subs
  run = (fun vs ->
          (let vsa = map run vs in
            (if list_ex is_none vsa then None
              else Some (map (comp fst the) vsa,
                          Array.of_list
                            (map (comp (comp snd snd) the) vsa)))));;

let rec mem _A ta t i = memL _A ta t i && memR _A ta t i;;

let rec accept_eps
  transs len r bs =
    member (ceq_nat, ccompare_nat) len (step_eps_closure_set transs len r bs);;

let rec accept transs len r = accept_eps transs len r (Array.of_list []);;

let rec run _B (_C1, _C2)
  run_hd n x2 = match run_hd, n, x2 with run_hd, n, VYDRA_None -> None
    | run_hd, n, VYDRA_Bool (b, e) ->
        (match run_hd e with None -> None
          | Some (ea, (t, _)) -> Some (VYDRA_Bool (b, ea), (t, b)))
    | run_hd, n, VYDRA_Atom (a, e) ->
        (match run_hd e with None -> None
          | Some (ea, (t, x)) ->
            Some (VYDRA_Atom (a, ea), (t, member (_C1, _C2) a x)))
    | run_hd, n, VYDRA_Neg v ->
        (if equal_nata n zero_nat then failwith "undefined"
          else (match run _B (_C1, _C2) run_hd (minus_nat n one_nat) v
                 with None -> None
                 | Some (va, (t, b)) -> Some (VYDRA_Neg va, (t, not b))))
    | run_hd, n, VYDRA_Bin (v, va, vb) ->
        (if equal_nata n zero_nat then failwith "undefined"
          else (match run _B (_C1, _C2) run_hd (minus_nat n one_nat) va
                 with None -> None
                 | Some (vl, (t, bl)) ->
                   (match run _B (_C1, _C2) run_hd (minus_nat n one_nat) vb
                     with None -> None
                     | Some (vr, (_, br)) ->
                       Some (VYDRA_Bin (v, vl, vr), (t, v bl br)))))
    | run_hd, n, VYDRA_Prev (v, va, vb, vc) ->
        (if equal_nata n zero_nat then failwith "undefined"
          else (match run_hd vb with None -> None
                 | Some (e, (t, _)) ->
                   (let beta =
                      (match vc with None -> false
                        | Some (ta, b) -> b && mem _B ta t v)
                      in
                     (match run _B (_C1, _C2) run_hd (minus_nat n one_nat) va
                       with None -> Some (VYDRA_None, (t, beta))
                       | Some (vaa, (_, b)) ->
                         Some (VYDRA_Prev (v, vaa, e, Some (t, b)),
                                (t, beta))))))
    | run_hd, n, VYDRA_Next (v, va, vb, vc) ->
        (if equal_nata n zero_nat then failwith "undefined"
          else (match run_hd vb with None -> None
                 | Some (e, (t, _)) ->
                   (match vc
                     with None ->
                       (match run _B (_C1, _C2) run_hd (minus_nat n one_nat) va
                         with None -> None
                         | Some (vaa, (_, _)) ->
                           run _B (_C1, _C2) run_hd (suc (minus_nat n one_nat))
                             (VYDRA_Next (v, vaa, e, Some t)))
                     | Some ta ->
                       (match run _B (_C1, _C2) run_hd (minus_nat n one_nat) va
                         with None ->
                           (if mem _B ta t v then None
                             else Some (VYDRA_None, (ta, false)))
                         | Some (vaa, (_, b)) ->
                           Some (VYDRA_Next (v, vaa, e, Some t),
                                  (ta, b && mem _B ta t v))))))
    | run_hd, n, VYDRA_Since (v, va, vb, vc, vd, ve, vf, vg) ->
        (if equal_nata n zero_nat then failwith "undefined"
          else (match run _B (_C1, _C2) run_hd (minus_nat n one_nat) va
                 with None -> None
                 | Some (vphi, (t, b1)) ->
                   (let cphi = (if b1 then suc vd else zero_nat) in
                    let cpsi = suc ve in
                    let cppsi = map_optiona suc vf in
                     (match
                       while_break (while_since_cond _B v t)
                         (while_since_body _B run_hd
                           (run _B (_C1, _C2) run_hd (minus_nat n one_nat)))
                         (vb, (vc, (cpsi, (cppsi, vg))))
                       with None -> None
                       | Some (vpsi, (e, (cpsia, (cppsia, tppsi)))) ->
                         (let beta =
                            (match cppsia with None -> false
                              | Some k ->
                                less_eq_nat (minus_nat k one_nat) cphi &&
                                  memR _B (the tppsi) t v)
                            in
                           Some (VYDRA_Since
                                   (v, vphi, vpsi, e, cphi, cpsia, cppsia,
                                     tppsi),
                                  (t, beta)))))))
    | run_hd, n, VYDRA_Until (v, va, vb, vc, vd, ve, vf) ->
        (if equal_nata n zero_nat then failwith "undefined"
          else (match run_t _B run_hd va with None -> None
                 | Some (e, t) ->
                   (match
                     while_break (while_until_cond _B v t)
                       (while_until_body _B run_hd
                         (run _B (_C1, _C2) run_hd (minus_nat n one_nat)))
                       (vb, (vc, (vd, (ve, vf))))
                     with None -> None
                     | Some (vphi, (vpsi, (epsi, (c, zo)))) ->
                       (if equal_nata c zero_nat then None
                         else (match zo with None -> None
                                | Some (ta, (b1, b2)) ->
                                  (if b2 && memL _B t ta v
                                    then Some (VYDRA_Until
         (v, e, vphi, vpsi, epsi, minus_nat c one_nat, zo),
        (t, true))
                                    else (if not b1
   then Some (VYDRA_Until (v, e, vphi, vpsi, epsi, minus_nat c one_nat, zo),
               (t, false))
   else (match read_t _B epsi with None -> None
          | Some _ ->
            Some (VYDRA_Until (v, e, vphi, vpsi, epsi, minus_nat c one_nat, zo),
                   (t, false))))))))))
    | run_hd, n, VYDRA_MatchP (v, va, vb, vc) ->
        (if equal_nata n zero_nat then failwith "undefined"
          else (match
                 eval_matchP _B
                   (init_args
                     (insert (ceq_nat, ccompare_nat) zero_nat
                        (set_empty (ceq_nat, ccompare_nat)
                          (of_phantom set_impl_nata)),
                       (delta va vb, accept va vb))
                     (run_t _B run_hd, read_t _B)
                     (run_subs
                       (run _B (_C1, _C2) run_hd (minus_nat n one_nat))))
                   v vc
                 with None -> None
                 | Some ((t, b), w) ->
                   Some (VYDRA_MatchP (v, va, vb, w), (t, b))))
    | run_hd, n, VYDRA_MatchF (v, va, vb, vc) ->
        (if equal_nata n zero_nat then failwith "undefined"
          else (match
                 eval_matchF _B
                   (init_args
                     (insert (ceq_nat, ccompare_nat) zero_nat
                        (set_empty (ceq_nat, ccompare_nat)
                          (of_phantom set_impl_nata)),
                       (delta va vb, accept va vb))
                     (run_t _B run_hd, read_t _B)
                     (run_subs
                       (run _B (_C1, _C2) run_hd (minus_nat n one_nat))))
                   v vc
                 with None -> None
                 | Some ((t, b), w) ->
                   Some (VYDRA_MatchF (v, va, vb, w), (t, b))));;

let rec state_cnt _B
  = function Lookahead phi -> one_nat
    | Symbol phi -> nat_of_integer (Z.of_int 2)
    | Plus (r, s) ->
        plus_nat (plus_nat one_nat (state_cnt _B r)) (state_cnt _B s)
    | Times (r, s) -> plus_nat (state_cnt _B r) (state_cnt _B s)
    | Star r -> plus_nat one_nat (state_cnt _B r);;

let rec pos _A
  a x1 = match a, x1 with a, [] -> None
    | a, x :: xs ->
        (if eq _A a x then Some zero_nat
          else (match pos _A a xs with None -> None | Some n -> Some (suc n)));;

let rec build_nfa_impl _A (_B1, _B2)
  x0 x1 = match x0, x1 with
    Lookahead phi, (q0, (qf, phis)) ->
      (match pos (equal_formula _A (_B1, _B2)) phi phis
        with None -> [Eps_trans (qf, size_list phis)]
        | Some n -> [Eps_trans (qf, n)])
    | Symbol phi, (q0, (qf, phis)) ->
        (match pos (equal_formula _A (_B1, _B2)) phi phis
          with None -> [Eps_trans (suc q0, size_list phis); Symb_trans qf]
          | Some n -> [Eps_trans (suc q0, n); Symb_trans qf])
    | Plus (r, s), (q0, (qf, phis)) ->
        (let ts_r =
           build_nfa_impl _A (_B1, _B2) r (plus_nat q0 one_nat, (qf, phis)) in
         let ts_s =
           build_nfa_impl _A (_B1, _B2) s
             (plus_nat (plus_nat q0 one_nat) (state_cnt _B2 r),
               (qf, collect_subfmlas _A (_B1, _B2) r phis))
           in
          Split_trans
            (plus_nat q0 one_nat,
              plus_nat (plus_nat q0 one_nat) (state_cnt _B2 r)) ::
            ts_r @ ts_s)
    | Times (r, s), (q0, (qf, phis)) ->
        (let ts_r =
           build_nfa_impl _A (_B1, _B2) r
             (q0, (plus_nat q0 (state_cnt _B2 r), phis))
           in
         let a =
           build_nfa_impl _A (_B1, _B2) s
             (plus_nat q0 (state_cnt _B2 r),
               (qf, collect_subfmlas _A (_B1, _B2) r phis))
           in
          ts_r @ a)
    | Star r, (q0, (qf, phis)) ->
        (let a =
           build_nfa_impl _A (_B1, _B2) r (plus_nat q0 one_nat, (q0, phis)) in
          Split_trans (plus_nat q0 one_nat, qf) :: a);;

let empty : ('a, 'b) alist = Alist [];;

let rec mapping_empty_choose _A
  = (match ccompare _A with None -> Assoc_List_Mapping empty
      | Some _ -> RBT_Mapping (emptyc _A));;

let rec mapping_empty _A = function Mapping_RBT -> RBT_Mapping (emptyc _A)
                           | Mapping_Assoc_List -> Assoc_List_Mapping empty
                           | Mapping_Mapping -> Mapping (fun _ -> None)
                           | Mapping_Choose -> mapping_empty_choose _A;;

let rec emptya (_A1, _A2) = mapping_empty _A1 (of_phantom (mapping_impl _A2));;

let rec init_window (_A1, _A2) (_B1, _B2)
  args t0 sub =
    Window_ext
      (emptya ((ccompare_prod _B1 _A1), (mapping_impl_prod _B2 _A2)),
        emptya (_B1, _B2), zero_nat, t0, sub, zero_nat, t0, sub,
        [(w_init args, (w_init args, None))], [], ());;

let rec suba (_B1, _B2) (_C1, _C2, _C3)
  init_hd run_hd n x3 = match init_hd, run_hd, n, x3 with
    init_hd, run_hd, n, Bool b -> VYDRA_Bool (b, init_hd)
    | init_hd, run_hd, n, Atom a -> VYDRA_Atom (a, init_hd)
    | init_hd, run_hd, n, Neg v ->
        (if equal_nata n zero_nat then failwith "undefined"
          else VYDRA_Neg
                 (suba (_B1, _B2) (_C1, _C2, _C3) init_hd run_hd
                   (minus_nat n one_nat) v))
    | init_hd, run_hd, n, Bin (v, va, vb) ->
        (if equal_nata n zero_nat then failwith "undefined"
          else VYDRA_Bin
                 (v, suba (_B1, _B2) (_C1, _C2, _C3) init_hd run_hd
                       (minus_nat n one_nat) va,
                   suba (_B1, _B2) (_C1, _C2, _C3) init_hd run_hd
                     (minus_nat n one_nat) vb))
    | init_hd, run_hd, n, Prev (v, va) ->
        (if equal_nata n zero_nat then failwith "undefined"
          else VYDRA_Prev
                 (v, suba (_B1, _B2) (_C1, _C2, _C3) init_hd run_hd
                       (minus_nat n one_nat) va,
                   init_hd, None))
    | init_hd, run_hd, n, Next (v, va) ->
        (if equal_nata n zero_nat then failwith "undefined"
          else VYDRA_Next
                 (v, suba (_B1, _B2) (_C1, _C2, _C3) init_hd run_hd
                       (minus_nat n one_nat) va,
                   init_hd, None))
    | init_hd, run_hd, n, Since (v, va, vb) ->
        (if equal_nata n zero_nat then failwith "undefined"
          else VYDRA_Since
                 (va, suba (_B1, _B2) (_C1, _C2, _C3) init_hd run_hd
                        (minus_nat n one_nat) v,
                   suba (_B1, _B2) (_C1, _C2, _C3) init_hd run_hd
                     (minus_nat n one_nat) vb,
                   t0 _B2 init_hd run_hd, zero_nat, zero_nat, None, None))
    | init_hd, run_hd, n, Until (v, va, vb) ->
        (if equal_nata n zero_nat then failwith "undefined"
          else VYDRA_Until
                 (va, t0 _B2 init_hd run_hd,
                   suba (_B1, _B2) (_C1, _C2, _C3) init_hd run_hd
                     (minus_nat n one_nat) v,
                   suba (_B1, _B2) (_C1, _C2, _C3) init_hd run_hd
                     (minus_nat n one_nat) vb,
                   t0 _B2 init_hd run_hd, zero_nat, None))
    | init_hd, run_hd, n, MatchP (v, va) ->
        (if equal_nata n zero_nat then failwith "undefined"
          else (let qf = state_cnt _B2 va in
                let transs =
                  Array.of_list
                    (build_nfa_impl _C3 (_B1, _B2) va (zero_nat, (qf, [])))
                  in
                 VYDRA_MatchP
                   (v, transs, qf,
                     init_window
                       ((ccompare_iarray ccompare_bool), mapping_impl_iarray)
                       ((ccompare_set
                          (finite_UNIV_nat, ceq_nat, cproper_interval_nat,
                            set_impl_nat)),
                         mapping_impl_set)
                       (init_args
                         (insert (ceq_nat, ccompare_nat) zero_nat
                            (set_empty (ceq_nat, ccompare_nat)
                              (of_phantom set_impl_nata)),
                           (delta transs qf, accept transs qf))
                         (run_t _B2 run_hd, read_t _B2)
                         (run_subs
                           (run _B2 (_C1, _C2) run_hd (minus_nat n one_nat))))
                       (t0 _B2 init_hd run_hd)
                       (map (suba (_B1, _B2) (_C1, _C2, _C3) init_hd run_hd
                              (minus_nat n one_nat))
                         (collect_subfmlas _C3 (_B1, _B2) va [])))))
    | init_hd, run_hd, n, MatchF (v, va) ->
        (if equal_nata n zero_nat then failwith "undefined"
          else (let qf = state_cnt _B2 va in
                let transs =
                  Array.of_list
                    (build_nfa_impl _C3 (_B1, _B2) va (zero_nat, (qf, [])))
                  in
                 VYDRA_MatchF
                   (v, transs, qf,
                     init_window
                       ((ccompare_iarray ccompare_bool), mapping_impl_iarray)
                       ((ccompare_set
                          (finite_UNIV_nat, ceq_nat, cproper_interval_nat,
                            set_impl_nat)),
                         mapping_impl_set)
                       (init_args
                         (insert (ceq_nat, ccompare_nat) zero_nat
                            (set_empty (ceq_nat, ccompare_nat)
                              (of_phantom set_impl_nata)),
                           (delta transs qf, accept transs qf))
                         (run_t _B2 run_hd, read_t _B2)
                         (run_subs
                           (run _B2 (_C1, _C2) run_hd (minus_nat n one_nat))))
                       (t0 _B2 init_hd run_hd)
                       (map (suba (_B1, _B2) (_C1, _C2, _C3) init_hd run_hd
                              (minus_nat n one_nat))
                         (collect_subfmlas _C3 (_B1, _B2) va [])))));;

let rec hda (x21 :: x22) = x21;;

let rec hd _A xa = hda (list_of_dlist _A xa);;

let rec tla = function [] -> []
              | x21 :: x22 -> x22;;

let rec tl _A xa = Abs_dlist (tla (list_of_dlist _A xa));;

let rec semilattice_set_apply (Abs_semilattice_set x) = x;;

let rec is_empty _A
  xa = (match impl_ofa _A xa with Empty -> true
         | Branch (_, _, _, _, _) -> false);;

let rec rBT_Impl_fold1
  f x1 = match f, x1 with
    f, Branch (ca, Branch (c, l, ka, va, ra), k, v, r) ->
      folda (fun kb _ -> f kb) r
        (f k (rBT_Impl_fold1 f (Branch (c, l, ka, va, ra))))
    | f, Branch (c, Empty, k, v, r) -> folda (fun ka _ -> f ka) r k
    | f, Empty -> failwith "undefined";;

let rec fold1 _A x xc = rBT_Impl_fold1 x (impl_ofa _A xc);;

let rec nulla _A xa = null (list_of_dlist _A xa);;

let rec set_fold1 (_A1, _A2, _A3)
  f x1 = match f, x1 with
    f, RBT_set rbt ->
      (match ccompare _A2
        with None ->
          failwith "set_fold1 RBT_set: ccompare = None"
            (fun _ -> set_fold1 (_A1, _A2, _A3) f (RBT_set rbt))
        | Some _ ->
          (if is_empty _A2 rbt
            then failwith "set_fold1 RBT_set: empty set"
                   (fun _ -> set_fold1 (_A1, _A2, _A3) f (RBT_set rbt))
            else fold1 _A2 (semilattice_set_apply f) rbt))
    | f, DList_set dxs ->
        (match ceq _A1
          with None ->
            failwith "set_fold1 DList_set: ceq = None"
              (fun _ -> set_fold1 (_A1, _A2, _A3) f (DList_set dxs))
          | Some _ ->
            (if nulla _A1 dxs
              then failwith "set_fold1 DList_set: empty set"
                     (fun _ -> set_fold1 (_A1, _A2, _A3) f (DList_set dxs))
              else foldc _A1 (semilattice_set_apply f) (tl _A1 dxs)
                     (hd _A1 dxs)))
    | f, Set_Monad (x :: xs) -> fold (semilattice_set_apply f) xs x
    | f, Collect_set p ->
        failwith "set_fold1: Collect_set"
          (fun _ -> set_fold1 (_A1, _A2, _A3) f (Collect_set p))
    | f, Complement a ->
        failwith "set_fold1: Complement"
          (fun _ -> set_fold1 (_A1, _A2, _A3) f (Complement a));;

let rec min_sls _A
  = Abs_semilattice_set (min _A.order_linorder.preorder_order.ord_preorder);;

let rec mina (_A1, _A2, _A3, _A4)
  a = set_fold1 (_A1, _A2, _A3) (min_sls _A4) a;;

let rec progress _A (_B1, _B2)
  x0 ts = match x0, ts with
    MatchF (i, r), ts ->
      (if equal_nata (size_list ts) zero_nat then zero_nat
        else (let k =
                min ord_nat (minus_nat (size_list ts) one_nat)
                  (let x :: xs = collect_subfmlas _A (_B1, _B2) r [] in
                    fold (comp (min ord_nat)
                           (fun f -> progress _A (_B1, _B2) f ts))
                      xs (progress _A (_B1, _B2) x ts))
                in
               mina (ceq_nat, ccompare_nat, lattice_nat, linorder_nat)
                 (image (ceq_nat, ccompare_nat)
                   (ceq_nat, ccompare_nat, set_impl_nat) (fun j -> j)
                   (inf_seta (ceq_nat, ccompare_nat)
                     (image (ceq_nat, ccompare_nat)
                       (ceq_nat, ccompare_nat, set_impl_nat) (fun j -> j)
                       (collect cenum_nat
                         (membera equal_nat (upt zero_nat (suc k)))))
                     (image (ceq_nat, ccompare_nat)
                       (ceq_nat, ccompare_nat, set_impl_nat) (fun j -> j)
                       (collect cenum_nat
                         (fun j -> memR _B2 (nth ts j) (nth ts k) i)))))))
    | MatchP (i, r), ts ->
        (let x :: xs = collect_subfmlas _A (_B1, _B2) r [] in
          fold (comp (min ord_nat) (fun f -> progress _A (_B1, _B2) f ts)) xs
            (progress _A (_B1, _B2) x ts))
    | Until (phi, i, psi), ts ->
        (if equal_nata (size_list ts) zero_nat then zero_nat
          else (let k =
                  min ord_nat (minus_nat (size_list ts) one_nat)
                    (min ord_nat (progress _A (_B1, _B2) phi ts)
                      (progress _A (_B1, _B2) psi ts))
                  in
                 mina (ceq_nat, ccompare_nat, lattice_nat, linorder_nat)
                   (image (ceq_nat, ccompare_nat)
                     (ceq_nat, ccompare_nat, set_impl_nat) (fun j -> j)
                     (inf_seta (ceq_nat, ccompare_nat)
                       (image (ceq_nat, ccompare_nat)
                         (ceq_nat, ccompare_nat, set_impl_nat) (fun j -> j)
                         (collect cenum_nat (less_eq_nat zero_nat)))
                       (inf_seta (ceq_nat, ccompare_nat)
                         (image (ceq_nat, ccompare_nat)
                           (ceq_nat, ccompare_nat, set_impl_nat) (fun j -> j)
                           (image (ceq_nat, ccompare_nat)
                             (ceq_nat, ccompare_nat, set_impl_nat) (fun j -> j)
                             (collect cenum_nat (fun j -> less_eq_nat j k))))
                         (image (ceq_nat, ccompare_nat)
                           (ceq_nat, ccompare_nat, set_impl_nat) (fun j -> j)
                           (image (ceq_nat, ccompare_nat)
                             (ceq_nat, ccompare_nat, set_impl_nat) (fun j -> j)
                             (collect cenum_nat
                               (fun j ->
                                 memR _B2 (nth ts j) (nth ts k) i)))))))))
    | Since (phi, i, psi), ts ->
        min ord_nat (progress _A (_B1, _B2) phi ts)
          (progress _A (_B1, _B2) psi ts)
    | Next (i, phi), ts ->
        (if equal_nata (progress _A (_B1, _B2) phi ts) zero_nat then zero_nat
          else minus_nat (progress _A (_B1, _B2) phi ts) one_nat)
    | Prev (i, phi), ts ->
        min ord_nat (size_list ts) (suc (progress _A (_B1, _B2) phi ts))
    | Bin (f, phi, psi), ts ->
        min ord_nat (progress _A (_B1, _B2) phi ts)
          (progress _A (_B1, _B2) psi ts)
    | Neg phi, ts -> progress _A (_B1, _B2) phi ts
    | Atom a, ts -> size_list ts
    | Bool b, ts -> size_list ts;;

let rec right _A x = fst (snd (rep_I _A x));;

let rec interval (_A1, _A2, _A3, _A4)
  xc xd xe xf =
    Abs_I (if less_eq
                _A4.semilattice_sup_timestamp.order_semilattice_sup.preorder_order.ord_preorder
                (zero _A4.comm_monoid_add_timestamp.monoid_add_comm_monoid_add.zero_monoid_add)
                xc &&
                (less_eq
                   _A4.semilattice_sup_timestamp.order_semilattice_sup.preorder_order.ord_preorder
                   xc xd &&
                  (member (_A1, _A2) xc (tfin _A4.tfin_timestamp) &&
                    not (eq _A3 xd
                           (zero _A4.comm_monoid_add_timestamp.monoid_add_comm_monoid_add.zero_monoid_add) &&
                          not xf)))
            then (xc, (xd, (xe, xf)))
            else failwith "malformed interval"
                   (fun _ ->
                     (zero _A4.comm_monoid_add_timestamp.monoid_add_comm_monoid_add.zero_monoid_add,
                       (zero _A4.comm_monoid_add_timestamp.monoid_add_comm_monoid_add.zero_monoid_add,
                         (true, true)))));;

let rec run_vydra _B (_C1, _C2)
  run_hd v =
    (let (n, w) = v in
      map_optiona (apfst (fun a -> (n, a))) (run _B (_C1, _C2) run_hd n w));;

let rec msize_fmla _B
  = function Bool b -> zero_nat
    | Atom a -> zero_nat
    | Neg phi -> suc (msize_fmla _B phi)
    | Bin (f, phi, psi) ->
        suc (plus_nat (msize_fmla _B phi) (msize_fmla _B psi))
    | Prev (i, phi) -> suc (msize_fmla _B phi)
    | Next (i, phi) -> suc (msize_fmla _B phi)
    | Since (phi, i, psi) ->
        suc (max ord_nat (msize_fmla _B phi) (msize_fmla _B psi))
    | Until (phi, i, psi) ->
        suc (max ord_nat (msize_fmla _B phi) (msize_fmla _B psi))
    | MatchP (i, r) -> suc (msize_regex _B r)
    | MatchF (i, r) -> suc (msize_regex _B r)
and msize_regex _B
  = function Lookahead phi -> msize_fmla _B phi
    | Symbol phi -> msize_fmla _B phi
    | Plus (r, s) -> max ord_nat (msize_regex _B r) (msize_regex _B s)
    | Times (r, s) -> max ord_nat (msize_regex _B r) (msize_regex _B s)
    | Star r -> msize_regex _B r;;

let rec init_vydra (_B1, _B2) (_C1, _C2, _C3)
  init_hd run_hd phi =
    (let n = msize_fmla _B2 phi in
      (n, suba (_B1, _B2) (_C1, _C2, _C3) init_hd run_hd n phi));;

let rec mk_db x = set (ceq_literal, ccompare_literal, set_impl_literal) x;;

let rec embed _B f x1 = match f, x1 with f, Lookahead phi -> Test (f phi)
                   | f, Symbol phi -> Timesa (Test (f phi), Wild)
                   | f, Plus (r, s) -> Plusa (embed _B f r, embed _B f s)
                   | f, Times (r, s) -> Timesa (embed _B f r, embed _B f s)
                   | f, Star r -> Stara (embed _B f r);;

let rec mdl2mdl _B
  = function Bool b -> Boola b
    | Atom a -> Atoma a
    | Neg phi -> Nega (mdl2mdl _B phi)
    | Bin (f, phi, psi) -> Bina (f, mdl2mdl _B phi, mdl2mdl _B psi)
    | Prev (i, phi) -> Preva (i, mdl2mdl _B phi)
    | Next (i, phi) -> Nexta (i, mdl2mdl _B phi)
    | Since (phi, i, psi) -> Sincea (mdl2mdl _B phi, i, mdl2mdl _B psi)
    | Until (phi, i, psi) -> Untila (mdl2mdl _B phi, i, mdl2mdl _B psi)
    | MatchP (i, r) -> MatchPa (i, embed _B (mdl2mdl _B) (rderive _B r))
    | MatchF (i, r) -> MatchFa (i, embed _B (mdl2mdl _B) (rderive _B r));;

let rec bounded_future_fmla (_B1, _B2, _B3)
  = function Bool b -> true
    | Atom a -> true
    | Neg phi -> bounded_future_fmla (_B1, _B2, _B3) phi
    | Bin (f, phi, psi) ->
        bounded_future_fmla (_B1, _B2, _B3) phi &&
          bounded_future_fmla (_B1, _B2, _B3) psi
    | Prev (i, phi) -> bounded_future_fmla (_B1, _B2, _B3) phi
    | Next (i, phi) -> bounded_future_fmla (_B1, _B2, _B3) phi
    | Since (phi, i, psi) ->
        bounded_future_fmla (_B1, _B2, _B3) phi &&
          bounded_future_fmla (_B1, _B2, _B3) psi
    | Until (phi, i, psi) ->
        bounded_future_fmla (_B1, _B2, _B3) phi &&
          (bounded_future_fmla (_B1, _B2, _B3) psi &&
            member (_B1, _B2) (right _B3 i) (tfin _B3.tfin_timestamp))
    | MatchP (i, r) -> bounded_future_regex (_B1, _B2, _B3) r
    | MatchF (i, r) ->
        bounded_future_regex (_B1, _B2, _B3) r &&
          member (_B1, _B2) (right _B3 i) (tfin _B3.tfin_timestamp)
and bounded_future_regex (_B1, _B2, _B3)
  = function Lookahead phi -> bounded_future_fmla (_B1, _B2, _B3) phi
    | Symbol phi -> bounded_future_fmla (_B1, _B2, _B3) phi
    | Plus (r, s) ->
        bounded_future_regex (_B1, _B2, _B3) r &&
          bounded_future_regex (_B1, _B2, _B3) s
    | Times (r, s) ->
        bounded_future_regex (_B1, _B2, _B3) r &&
          bounded_future_regex (_B1, _B2, _B3) s
    | Star r -> bounded_future_regex (_B1, _B2, _B3) r;;

let rec wf_fmla_enat x = wf_fmla equal_literal (equal_enat, timestamp_enat) x;;

let rec interval_enat
  x = interval (ceq_enat, ccompare_enat, equal_enat, timestamp_enat) x;;

let rec mdl2mdl_enat x = mdl2mdl timestamp_enat x;;

let rec progress_enat
  x = progress equal_literal (equal_enat, timestamp_enat) x;;

let rec rep_interval_enat x = rep_I timestamp_enat x;;

let rec run_vydra_string_enat
  x = run_vydra timestamp_enat (ceq_literal, ccompare_literal) x;;

let rec init_vydra_string_enat
  x = init_vydra (equal_enat, timestamp_enat)
        (ceq_literal, ccompare_literal, equal_literal) x;;

let rec bounded_future_fmla_enat
  x = bounded_future_fmla (ceq_enat, ccompare_enat, timestamp_enat) x;;

end;; (*struct VYDRA*)
