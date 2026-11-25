module BTreeContainer

open Container
module B = BTree

(** [x] está en [t]? *)
let rec in_btree (#d:B.degree) (x:int) (t:B.btree0 d) : bool =
  match t with
  | B.L -> false
  | B.N cs -> in_btree' x cs
and in_btree' (#d:B.degree) (x:int) (cs:B.children d) : bool =
  match cs with
  | B.Last c -> in_btree x c
  | B.Split (c, (k, b), cs') -> (b && x = k) || in_btree x c || in_btree' x cs'

(** Si todos los elementos de [t] son mayores a [y], y [x] es menor a [y],
    entonces [x] no pertenece a [t] *)
let rec all_gt_not_in (#d:B.degree) (x y:int) (t:B.btree0 d)
  : Lemma (requires B.all_gt y t /\ x <= y) (ensures not (in_btree x t)) =
  match t with
  | B.L -> ()
  | B.N cs -> all_gt_not_in' x y cs
and all_gt_not_in' (#d:B.degree) (x y:int) (cs:B.children d)
  : Lemma (requires B.all_gt' y cs /\ x <= y) (ensures not (in_btree' x cs)) =
  match cs with
  | B.Last c -> all_gt_not_in x y c
  | B.Split (c, _, cs') -> all_gt_not_in x y c; all_gt_not_in' x y cs'

(** Si todos los elementos de [t] son menores a [y], y [x] es mayor a [y],
    entonces [x] no pertenece a [t] *)
let rec all_lt_not_in (#d:B.degree) (x y:int) (t:B.btree0 d)
  : Lemma (requires B.all_lt y t /\ x >= y) (ensures not (in_btree x t)) =
  match t with
  | B.L -> ()
  | B.N cs -> all_lt_not_in' x y cs
and all_lt_not_in' (#d:B.degree) (x y:int) (cs:B.children d)
  : Lemma (requires B.all_lt' y cs /\ x >= y) (ensures not (in_btree' x cs)) =
  match cs with
  | B.Last c -> all_lt_not_in x y c
  | B.Split (c, _, cs') -> all_lt_not_in x y c; all_lt_not_in' x y cs'

(** Correctitud de [member] *)
let rec member_ok (#d:B.degree) (x:int) (t:B.btree0 d)
  : Lemma (requires B.is_btree t) (ensures B.member x t == in_btree x t) =
  match t with
  | B.L -> ()
  | B.N cs -> member_ok' x cs
and member_ok' (#d:B.degree) (x:int) (cs:B.children d)
  : Lemma (requires B.is_btree' cs) (ensures B.member' x cs == in_btree' x cs) =
  match cs with
  | B.Last c -> member_ok x c
  | B.Split (c, (k, _), cs') ->
    if x < k then (member_ok x c; all_gt_not_in' x k cs')
    else if x > k then (member_ok' x cs'; all_lt_not_in x k c)
    else (all_lt_not_in x k c; all_gt_not_in' x k cs')

(** [t] está vacío? Hay que recorrerlo entero y revisar sus marcas. *)
let rec is_empty (#d:B.degree) (t:B.btree0 d) : bool =
  match t with
  | B.L -> true
  | B.N cs -> is_empty' cs
and is_empty' (#d:B.degree) (cs:B.children d) : bool =
  match cs with
  | B.Last c -> is_empty c
  | B.Split (c, (_, b), cs') -> not b && is_empty c && is_empty' cs'

(** Si [t] está vacío, entonces [y] noe está en [t] *)
let rec empty_not_in (#d:B.degree) (y:int) (t:B.btree0 d)
  : Lemma (requires is_empty t) (ensures not (in_btree y t)) =
  match t with
  | B.L -> ()
  | B.N cs -> empty_not_in' y cs
and empty_not_in' (#d:B.degree) (y:int) (cs:B.children d)
  : Lemma (requires is_empty' cs) (ensures not (in_btree' y cs)) =
  match cs with
  | B.Last c -> empty_not_in y c
  | B.Split (c, _, cs') -> empty_not_in y c; empty_not_in' y cs'

(** Si [t] no está vacío, entonces existe  [x] tal que [x] está en [t] *)
let rec not_empty_in (#d:B.degree) (t:B.btree0 d)
  : Lemma (requires not (is_empty t)) (ensures exists x. in_btree x t) =
  match t with
  | B.L -> ()
  | B.N cs -> not_empty_in' cs
and not_empty_in' (#d:B.degree) (cs:B.children d)
  : Lemma (requires not (is_empty' cs)) (ensures exists x. in_btree' x cs) =
  match cs with
  | B.Last c -> not_empty_in c
  | B.Split (c, (k, b), cs') ->
    if b then ()
    else if not (is_empty c) then not_empty_in c
    else not_empty_in' cs'

(** [t] modela un conjunto [ss] si:
    [x] está en [t] sii [x] pertenece a [ss] *)
let models (#d:B.degree) (t:B.btree d) (ss:TSet.set int) : prop =
  forall (x:int). in_btree x t <==> TSet.mem x ss

(** [t] está vacío sii modela un conjunto vacío *)
let is_empty_ok (#d:B.degree) (t:B.btree d)
  : Lemma (is_empty t <==> models t TSet.empty) =
  if is_empty t then Classical.forall_intro (fun y -> empty_not_in #d y t)
  else not_empty_in t

(** Si [y] está en [cs], entonces [y] está en alguna de las 3 partes
    resultantes de cortar [cs] *)
let rec cut_in (#d:B.degree) (n:nat) (y:int) (cs:B.children d)
  : Lemma (requires n < B.nkeys cs)
          (ensures (let l, m, r = B.cut n cs in
                    in_btree' y cs == (in_btree' y l || (snd m && y = fst m) || in_btree' y r))) =
  match cs with
  | B.Split (_, _, cs') -> if n > 0 then cut_in (n - 1) y cs'

(** Si [y] está en [cs], entonces [y] está en [cs] spliteado. *)
let split_in (#d:B.degree) (y:int) (cs:B.children d)
  : Lemma (in_btree' y (B.split cs) == in_btree' y cs) =
  if B.nkeys cs > 2 * d then cut_in d y cs

(** Si [y] es igual a [k], o está en [s] o [rest], entonces [y] está
    en el resultado de juntar [s], [k] y [rest]. *)
let rec join_in (#d:B.degree) (y:int) (s:B.children d) (k:B.key) (rest:B.children d)
  : Lemma (in_btree' y (B.join s k rest) ==
           (in_btree' y s || (snd k && y = fst k) || in_btree' y rest)) =
  match s with
  | B.Last _ -> ()
  | B.Split (_, _, s') -> join_in y s' k rest

(** Si [y] está en [t] o [y] = [x], entonces [y] está en [B.ins x t] *)
let rec ins_in (#d:B.degree) (x y:int) (t:B.btree0 d)
  : Lemma (in_btree' y (B.ins x t) == (y = x || in_btree y t)) =
  match t with
  | B.L -> ()
  | B.N cs -> ins_in' x y cs; split_in y (B.ins' x cs)
and ins_in' (#d:B.degree) (x y:int) (cs:B.children d)
  : Lemma (in_btree' y (B.ins' x cs) == (y = x || in_btree' y cs)) =
  match cs with
  | B.Last c -> ins_in x y c
  | B.Split (c, (k, b), cs') ->
    if x < k then (ins_in x y c; join_in y (B.ins x c) (k, b) cs')
    else if x = k then ()
    else ins_in' x y cs'

(** Si [t] modela un conjunto [ss], entonces [B.insert x t] modela
    la unión de [ss] con {[x]} *)
let ins_ok (#d:B.degree) (x:int) (t:B.btree d) (ss:TSet.set int)
  : Lemma (requires models t ss)
          (ensures models (B.insert x t) (TSet.union ss (TSet.singleton x))) =
  Classical.forall_intro (fun y -> ins_in #d x y t)

(** Si [y] está en [t] y [y] <> [x], entonces [y] está en [B.delete0 x t] *)
let rec del_in (#d:B.degree) (x y:int) (t:B.btree0 d)
  : Lemma (requires B.is_btree t)
          (ensures in_btree y (B.delete0 x t) == (in_btree y t && y <> x)) =
  match t with
  | B.L -> ()
  | B.N cs -> del_in' x y cs
and del_in' (#d:B.degree) (x y:int) (cs:B.children d)
  : Lemma (requires B.is_btree' cs)
          (ensures in_btree' y (B.delete0' x cs) == (in_btree' y cs && y <> x)) =
  match cs with
  | B.Last c -> del_in x y c
  | B.Split (c, (k, _), cs') ->
    if x < k then (del_in x y c; all_gt_not_in' x k cs')
    else if x = k then (all_lt_not_in k k c; all_gt_not_in' k k cs')
    else (del_in' x y cs'; all_lt_not_in x k c)

(** Si [t] modela un conjunto [ss], entonces [B.delete x t] modela
    la intersección de [ss] con el complemento de {[x]} *)
let del_ok (#d:B.degree) (x:int) (t:B.btree d) (ss:TSet.set int)
  : Lemma (requires models t ss)
          (ensures models (B.delete x t) (TSet.intersect ss (TSet.complement <| TSet.singleton x))) =
  Classical.forall_intro (fun y -> del_in #d x y t)

instance btree_container0 (d:B.degree) : container0 int (B.btree d) = {
  empty    = (B.L <: B.btree d);
  is_empty = (fun (t:B.btree d) -> is_empty t);
  mem      = (fun x (t:B.btree d) -> B.member x t);
  ins      = (fun x (t:B.btree d) -> B.insert x t);
  del      = (fun x (t:B.btree d) -> B.delete x t);
}

instance btree_container_laws (d:B.degree) : container_laws int (B.btree d) = {
  models      = models;
  empty_ok    = (fun _ -> ());
  is_empty_ok = is_empty_ok;
  mem_ok      = (fun x t _ -> member_ok x t);
  ins_ok      = ins_ok;
  del_ok      = del_ok;
}

instance btree_container (d:B.degree) : container int (B.btree d) = {
  ops  = btree_container0 d;
  laws = btree_container_laws d;
}
