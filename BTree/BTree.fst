module BTree

type key = int & bool
type degree = pos

type btree0 (d:degree) : Type0 =
  | L
  | N of children d
and children (d:degree) =
  | Last of btree0 d
  | Split of btree0 d & key & children d

let rec all_gt (#d:degree) (x:int) (t:btree0 d) : bool =
  match t with
  | L -> true
  | N cs -> all_gt' x cs
and all_gt' (#d:degree) (x:int) (cs:children d) : bool =
  match cs with
  | Last c -> all_gt x c
  | Split (c, (k, _), cs') -> all_gt x c && x < k && all_gt' x cs'

let rec all_lt (#d:degree) (x:int) (t:btree0 d) : bool =
  match t with
  | L -> true
  | N cs -> all_lt' x cs
and all_lt' (#d:degree) (x:int) (cs:children d) : bool =
  match cs with
  | Last c -> all_lt x c
  | Split (c, (k, _), cs') -> all_lt x c && x > k && all_lt' x cs'

let rec is_btree (#d:degree) (t:btree0 d) : bool =
  match t with
  | L -> true
  | N cs -> is_btree' cs
and is_btree' (#d:degree) (cs:children d) : bool =
  match cs with
  | Last c -> is_btree c
  | Split (c, (k, _), cs') ->
    is_btree c && all_lt k c && all_gt' k cs' && is_btree' cs'

type btree (d:degree) = t:btree0 d{is_btree t}


(** Member *)

let rec member (#d:degree) (x:int) (t:btree0 d) : bool =
  match t with
  | L -> false
  | N cs -> member' x cs
and member' (#d:degree) (x:int) (cs:children d) : bool =
  match cs with
  | Last c -> member x c
  | Split (c, (k, b), cs') ->
    if x < k then member x c else if x > k then member' x cs' else b


(** Insert *)

(** Cantidad de claves en [cs] *)
let rec nkeys (#d:degree) (cs:children d) : nat =
  match cs with
  | Last _ -> 0
  | Split (_, _, cs') -> 1 + nkeys cs'

(** Corta [cs] en el índice [n] *)
let rec cut (#d:degree) (n:nat) (cs:children d{n < nkeys cs})
  : children d & key & children d =
  match cs with
  | Split (c, k, cs') ->
    if n = 0 then Last c, k, cs'
    else let l, m, r = cut (n - 1) cs' in Split (c, k, l), m, r

(* Junta [s], [k], [rest] *)
let rec join (#d:degree) (s:children d) (k:key) (rest:children d)
  : children d =
  match s with
  | Last c -> Split (c, k, rest)
  | Split (c, k', s') -> Split (c, k', join s' k rest)

(** Separa [cs] cuando se pasa de largo *)
let split (#d:degree) (cs:children d) : children d =
  if nkeys cs <= 2 * d then Last (N cs)
  else let l, m, r = cut d cs in Split (N l, m, Last (N r))

let rec ins (#d:degree) (x:int) (t:btree0 d) : children d =
  match t with
  | L -> Split (L, (x, true), Last L)
  | N cs -> split (ins' x cs)
and ins' (#d:degree) (x:int) (cs:children d) : children d =
  match cs with
  | Last c -> ins x c
  | Split (c, (k, b), cs') ->
    if x < k then join (ins x c) (k, b) cs'
    else if x = k then Split (c, (k, true), cs')
    else Split (c, (k, b), ins' x cs')

let insert0 (#d:degree) (x:int) (t:btree0 d) : btree0 d =
  match ins x t with
  | Last t' -> t'
  | cs -> N cs

(** Si todos los elementos de [cs] son menores a [y], entonces al cortar [cs],
    los elementos resultantes siguen siendo menores a [y] *)
let rec cut_lt (#d:degree) (n:nat) (y:int) (cs:children d)
  : Lemma (requires all_lt' y cs /\ n < nkeys cs)
          (ensures (let l, m, r = cut n cs in all_lt' y l /\ y > fst m /\ all_lt' y r)) =
  match cs with
  | Split (_, _, cs') -> if n > 0 then cut_lt (n - 1) y cs'

(** Si todos los elementos de [cs] son menores a [y], entonces al splitear [cs],
    los elementos resultantes siguen siendo menores a [y] *)
let split_lt (#d:degree) (y:int) (cs:children d)
  : Lemma (requires all_lt' y cs) (ensures all_lt' y (split cs)) =
  if nkeys cs > 2 * d then cut_lt d y cs

(** Si todos los elementos de [cs] son mayores a [y], entonces al cortar [cs],
    los elementos resultantes siguen siendo mayores a [y] *)
let rec cut_gt (#d:degree) (n:nat) (y:int) (cs:children d)
  : Lemma (requires all_gt' y cs /\ n < nkeys cs)
          (ensures (let l, m, r = cut n cs in all_gt' y l /\ y < fst m /\ all_gt' y r)) =
  match cs with
  | Split (_, _, cs') -> if n > 0 then cut_gt (n - 1) y cs'

(** Si todos los elementos de [cs] son mayores a [y], entonces al splitear [cs],
    los elementos resultantes siguen siendo mayores a [y] *)
let split_gt (#d:degree) (y:int) (cs:children d)
  : Lemma (requires all_gt' y cs) (ensures all_gt' y (split cs)) =
  if nkeys cs > 2 * d then cut_gt d y cs

(** Si [k] y todos los elementos de [s] y [rest] son menores a [y], entonces todos
    los elementos de juntar [s], [k] y [rest] son menores a [y] *)
let rec join_lt (#d:degree) (y:int) (s:children d) (k:key) (rest:children d)
  : Lemma (requires all_lt' y s /\ fst k < y /\ all_lt' y rest)
          (ensures all_lt' y (join s k rest)) =
  match s with
  | Last _ -> ()
  | Split (_, _, s') -> join_lt y s' k rest

(** Si [k] y todos los elementos de [s] y [rest] son mayores a [y], entonces todos
    los elementos de juntar [s], [k] y [rest] son mayores a [y] *)
let rec join_gt (#d:degree) (y:int) (s:children d) (k:key) (rest:children d)
  : Lemma (requires all_gt' y s /\ fst k > y /\ all_gt' y rest)
          (ensures all_gt' y (join s k rest)) =
  match s with
  | Last _ -> ()
  | Split (_, _, s') -> join_gt y s' k rest

(** Si todos los elementos de [t] son mayores a [y], y [x] es menor a [y]
    entonces todos los elementos de [t] son mayores a [x] *)
let rec all_gt_mono (#d:degree) (x y:int) (t:btree0 d)
  : Lemma (requires all_gt y t /\ x <= y) (ensures all_gt x t) =
  match t with
  | L -> ()
  | N cs -> all_gt_mono' x y cs
and all_gt_mono' (#d:degree) (x y:int) (cs:children d)
  : Lemma (requires all_gt' y cs /\ x <= y) (ensures all_gt' x cs) =
  match cs with
  | Last c -> all_gt_mono x y c
  | Split (c, _, cs') -> all_gt_mono x y c; all_gt_mono' x y cs'

(** Si todos los elementos de [t] son menores a [y], y [x] es mayor a [y]
    entonces todos los elementos de [t] son menores a [x] *)
let rec all_lt_mono (#d:degree) (x y:int) (t:btree0 d)
  : Lemma (requires all_lt y t /\ x >= y) (ensures all_lt x t) =
  match t with
  | L -> ()
  | N cs -> all_lt_mono' x y cs
and all_lt_mono' (#d:degree) (x y:int) (cs:children d)
  : Lemma (requires all_lt' y cs /\ x >= y) (ensures all_lt' x cs) =
  match cs with
  | Last c -> all_lt_mono x y c
  | Split (c, _, cs') -> all_lt_mono x y c; all_lt_mono' x y cs'

(** Si [s] y [rest] son btrees, todos los elementos de [s] son menores a [k],
    y todos los elementos de [rest] son mayores a [k], entonces el resultado
    de juntar [s], [k] y [rest] es un btree.
    Es decir, [join] preserva [is_btree] *)
let rec join_ok (#d:degree) (s:children d) (k:key) (rest:children d)
  : Lemma (requires is_btree' s /\ all_lt' (fst k) s /\ all_gt' (fst k) rest /\ is_btree' rest)
          (ensures is_btree' (join s k rest)) =
  match s with
  | Last _ -> ()
  | Split (_, (k', _), s') ->
    join_ok s' k rest; all_gt_mono' k' (fst k) rest; join_gt k' s' k rest

(** Si todos los elementos de [t] son menores a [y], y [x] es menor a [y],
    entonces todos los elementos de [ins x t] son menores a [y] *)
let rec ins_lt (#d:degree) (x y:int) (t:btree0 d)
  : Lemma (requires all_lt y t /\ x < y) (ensures all_lt' y (ins x t)) =
  match t with
  | L -> ()
  | N cs -> ins_lt' x y cs; split_lt y (ins' x cs)
and ins_lt' (#d:degree) (x y:int) (cs:children d)
  : Lemma (requires all_lt' y cs /\ x < y) (ensures all_lt' y (ins' x cs)) =
  match cs with
  | Last c -> ins_lt x y c
  | Split (c, (k, b), cs') ->
    if x < k then (ins_lt x y c; join_lt y (ins x c) (k, b) cs')
    else if x = k then ()
    else ins_lt' x y cs'

(** Si todos los elementos de [t] son mayores a [y], y [x] es mayores a [y],
    entonces todos los elementos de [ins x t] son mayores a [y] *)
let rec ins_gt (#d:degree) (x y:int) (t:btree0 d)
  : Lemma (requires all_gt y t /\ x > y) (ensures all_gt' y (ins x t)) =
  match t with
  | L -> ()
  | N cs -> ins_gt' x y cs; split_gt y (ins' x cs)
and ins_gt' (#d:degree) (x y:int) (cs:children d)
  : Lemma (requires all_gt' y cs /\ x > y) (ensures all_gt' y (ins' x cs)) =
  match cs with
  | Last c -> ins_gt x y c
  | Split (c, (k, b), cs') ->
    if x < k then (ins_gt x y c; join_gt y (ins x c) (k, b) cs')
    else if x = k then ()
    else ins_gt' x y cs'

(** Si [cs] es un btree, entonces al cortar [cs], [l] es un btree y
    todos sus elementos son menores a [m], y [r] es un btree y todos
    sus elementos son mayores a [m]
    Es decir, [cut] preserva [is_btree] *)
let rec cut_ok (#d:degree) (n:nat) (cs:children d)
  : Lemma (requires is_btree' cs /\ n < nkeys cs)
          (ensures (let l, m, r = cut n cs in
                    is_btree' l /\ all_lt' (fst m) l /\
                    is_btree' r /\ all_gt' (fst m) r)) =
  match cs with
  | Split (c, (k, _), cs') ->
    if n > 0 then (
      cut_ok (n - 1) cs';
      cut_gt (n - 1) k cs';
      let _, m, _ = cut (n - 1) cs' in all_lt_mono (fst m) k c
    )

(** [split] preserva [is_btree] *)
let split_ok (#d:degree) (cs:children d)
  : Lemma (requires is_btree' cs) (ensures is_btree' (split cs)) =
  if nkeys cs > 2 * d then cut_ok d cs

(** [ins] preserva [is_btree] *)
let rec ins_ok (#d:degree) (x:int) (t:btree0 d)
  : Lemma (requires is_btree t) (ensures is_btree' (ins x t)) =
  match t with
  | L -> ()
  | N cs -> ins_ok' x cs; split_ok (ins' x cs)
and ins_ok' (#d:degree) (x:int) (cs:children d)
  : Lemma (requires is_btree' cs) (ensures is_btree' (ins' x cs)) =
  match cs with
  | Last c -> ins_ok x c
  | Split (c, (k, b), cs') ->
    if x < k then (ins_ok x c; ins_lt x k c; join_ok (ins x c) (k, b) cs')
    else if x = k then ()
    else (ins_ok' x cs'; ins_gt' x k cs')

(** [insert0] preserva [is_btree] *)
let insert_ok (#d:degree) (x:int) (t:btree0 d)
  : Lemma (requires is_btree t) (ensures is_btree (insert0 x t)) =
  ins_ok x t

let insert (#d:degree) (x:int) (t:btree d) : btree d =
  insert_ok x t;
  insert0 x t


(** Delete *)

(** Para borrar [x] de [t], lo marcamos como eliminado, y nos ahorramos el
    rebalanceo. *)
let rec delete0 (#d:degree) (x:int) (t:btree0 d) : btree0 d =
  match t with
  | L -> L
  | N cs -> N (delete0' x cs)
and delete0' (#d:degree) (x:int) (cs:children d) : children d =
  match cs with
  | Last c -> Last (delete0 x c)
  | Split (c, (k, b), cs') ->
    if x < k then Split (delete0 x c, (k, b), cs')
    else if x = k then Split (c, (k, false), cs')
    else Split (c, (k, b), delete0' x cs')

(** Si todos los elementos de [t] son menores a [y] entonces todos los
    elementos de [delete0 x t] son menores a [y] *)
let rec delete0_lt (#d:degree) (x y:int) (t:btree0 d)
  : Lemma (requires all_lt y t) (ensures all_lt y (delete0 x t)) =
  match t with
  | L -> ()
  | N cs -> delete0_lt' x y cs
and delete0_lt' (#d:degree) (x y:int) (cs:children d)
  : Lemma (requires all_lt' y cs) (ensures all_lt' y (delete0' x cs)) =
  match cs with
  | Last c -> delete0_lt x y c
  | Split (c, (k, _), cs') ->
    if x < k then delete0_lt x y c
    else if x = k then ()
    else delete0_lt' x y cs'

(** Si todos los elementos de [t] son mayores a [y] entonces todos los
    elementos de [delete0 x t] son mayores a [y] *)
let rec delete0_gt (#d:degree) (x y:int) (t:btree0 d)
  : Lemma (requires all_gt y t) (ensures all_gt y (delete0 x t)) =
  match t with
  | L -> ()
  | N cs -> delete0_gt' x y cs
and delete0_gt' (#d:degree) (x y:int) (cs:children d)
  : Lemma (requires all_gt' y cs) (ensures all_gt' y (delete0' x cs)) =
  match cs with
  | Last c -> delete0_gt x y c
  | Split (c, (k, _), cs') ->
    if x < k then delete0_gt x y c
    else if x = k then ()
    else delete0_gt' x y cs'

(** [delete0] preserva [is_btree] *)
let rec delete0_ok (#d:degree) (x:int) (t:btree0 d)
  : Lemma (requires is_btree t) (ensures is_btree (delete0 x t)) =
  match t with
  | L -> ()
  | N cs -> delete0_ok' x cs
and delete0_ok' (#d:degree) (x:int) (cs:children d)
  : Lemma (requires is_btree' cs) (ensures is_btree' (delete0' x cs)) =
  match cs with
  | Last c -> delete0_ok x c
  | Split (c, (k, _), cs') ->
    if x < k then (delete0_ok x c; delete0_lt x k c)
    else if x = k then ()
    else (delete0_ok' x cs'; delete0_gt' x k cs')

let delete (#d:degree) (x:int) (t:btree d) : btree d =
  delete0_ok x t;
  delete0 x t
