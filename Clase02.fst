module Clase02

(* Polimorfismo paramétrico y lógica constructiva. *)

(* La identidad polimórfica *)
val id0_exp : (a:Type) -> (a -> a)

let id0_exp = fun (a:Type) -> fun (x:a) -> x

// let id0_exp = fun (a:Type) -> fun (x:a) -> x
let id_int  : int  -> int  = id0_exp int
let id_bool : bool -> bool = id0_exp bool

let _ = assert (id_int 1 == 1)
let _ = assert (id_bool true == true)

(* El símbolo # marca un argumento implícito. Estos argumentos se insertan
automáticamente por el typechecker cuando son requeridos. Si hay una única
forma de resolverlos, dada otras restricciones en el contexto, F* usará esa
solución. Si por alguna razón no puede resolverse automáticamente, siempre
pueden darse de forma explícita usando un # en la aplicación. *)

let id (#a:Type) (x:a) : a = x
// let id = fun (#a:Type) -> fun (x:a) -> x
let id_int'  : int -> int   = id
let id_bool' : bool -> bool = id

let _ = assert (id 1 == 1)
let _ = assert (id true == true)

(* Un tipo verdaderemente dependiente *)
val raro : bool -> Type0
let raro (b:bool) : Type =
  if b
  then int
  else string

(* Una función con el tipo `raro`: devuelve un entero o una
cadena según su argumento. *)
let f_raro (x:bool) : raro x =
  if x then 123 else "hola"

let _ = assert (f_raro true  == 123)
let _ = assert (f_raro false == "hola")
// let _ = f_raro false == f_raro true

(* (listas)^n de a *)
let rec nlist (a:Type) (n:nat) : Type =
  match n with
  | 0 -> a
  | n -> list (nlist a (n-1))

let _ = assert (nlist int 0 == int)
let _ = assert (nlist int 1 == list int)
let _ = assert (nlist int 2 == list (list int))

let rec n_singleton (#a:_) (x:a) (n:nat) : nlist a n =
  match n with
  | 0 -> x
  | n -> [n_singleton x (n-1)]

let _ = assert (n_singleton 1 0 == 1)
let _ = assert (n_singleton 1 1 == [1])
let _ = assert (n_singleton 1 2 == [[1]])

(* Lógica constructiva *)

(*
De la librería estándar de F*:

        type tuple2 'a 'b = | Mktuple2 : _1: 'a -> _2: 'b -> tuple2 'a 'b
        let fst (x: tuple2 'a 'b) : 'a = Mktuple2?._1 x
        let snd (x: tuple2 'a 'b) : 'b = Mktuple2?._2 x

        type either a b =
        | Inl : v: a -> either a b
        | Inr : v: b -> either a b

`a & b` es azúcar para `tuple2 a b`
`(x,y)` es azúcar para `Mktuple2 x y`
*)
type yy (a b : Type) = a & b
type oo (a b : Type) = either a b
type falso =
type verd = falso -> falso
type no (a : Type) = a -> falso

let vv : verd = id

(* La conjunción conmuta *)
let comm_yy (#a #b : Type) : yy a b -> yy b a =
  fun p -> (snd p, fst p)
//   fun (x, y) -> (y, x)

(* verd es neutro para la conjunción *)
let neutro_yy (#a:Type) : yy a verd -> a =
  fun (x, _) -> x

let neutro_yy' (#a:Type) : a -> yy a verd =
  fun (x:a) -> (x, vv)

(* La disjunción conmuta *)
(* `function` es azúcar para `fun` con un pattern matching inmediato al argumento. *)
let comm_oo (#a #b : Type) : oo a b -> oo b a =
  function
  | Inl x -> Inr x
  | Inr y -> Inl y

(* Principio de explosión: falso no tiene constructores,
así que con un match vacío podemos demostrar cualquier cosa *)
let ex_falso (#a:Type) (f : falso) : a =
  match f with

(* Demostrar *)
let neu1 (#a:Type) : oo a falso -> a =
  function
  | Inl x -> x

(* Demostrar *)
let neu2 (#a:Type) : a -> oo a falso =
  fun x -> Inl x

(* Distribución de `yy` sobre `oo`, en ambas direcciones *)
let distr_yyoo_1 (#a #b #c : Type)
  : yy a (oo b c) -> oo (yy a b) (yy a c)
  // a /\ (b \/ c)  ==>  (a /\ b) \/ (a /\ c)
  // a * (b + c)    ==>  (a * b) + (a * c)
=
  fun (x, yz) ->
  match yz with
  | Inl y -> Inl (x, y)
  | Inr z -> Inr (x, z)

let distr_yyoo_2 (#a #b #c : Type)
  : oo (yy a b) (yy a c) -> yy a (oo b c)
=
  function
  | Inl (x, y) -> (x, Inl y)
  | Inr (x, z) -> (x, Inr z)

let distr_ooyy_1 (#a #b #c : Type)
  : oo a (yy b c) -> yy (oo a b) (oo a c)
=
  function
  | Inl x -> (Inl x, Inl x)
  | Inr (y, z) -> (Inr y, Inr z)

let distr_ooyy_2 (#a #b #c : Type)
  : yy (oo a b) (oo a c) -> oo a (yy b c)
=
  fun (xy, xz) ->
  match xy with
  | Inl x -> Inl x
  | Inr y -> match xz with
             | Inl x -> Inl x
             | Inr z -> Inr (y, z)

let modus_tollens (#a #b : Type)
  : (a -> b) -> (no b -> no a)
=
  fun ab nb a -> nb (ab a)
  (* Vale la recíproca? *)

let modus_tollendo_ponens (#a #b : Type)
  : (oo a b) -> (no a -> b)
=
  fun ab na ->
  match ab with
  | Inl a -> ex_falso (na a)
  | Inr b -> b
  (* Vale la recíproca? *)

let modus_ponendo_tollens (#a #b : Type)
  : no (yy a b) -> (a -> no b)
=
  fun nab a b -> nab (a, b)
  (* Vale la recíproca? *)

(* Declare y pruebe, si es posible, las leyes de De Morgan
para `yy` y `oo`. ¿Son todas intuicionistas? *)

let demorgan1_ida (#a #b : Type) : oo (no a) (no b) -> no (yy a b) =
  fun naonb (a, b) ->
  match naonb with
  | Inl na -> na a
  | Inr nb -> nb b

let demorgan1_vuelta (#a #b : Type) : no (yy a b) -> oo (no a) (no b) =
  admit()

let demorgan2_ida (#a #b : Type) : yy (no a) (no b) -> no (oo a b) =
  fun (na, nb) aob ->
  match aob with
  | Inl a -> na a
  | Inr b -> nb b

let demorgan2_vuelta (#a #b : Type) : no (oo a b) -> yy (no a) (no b) =
  fun naob ->
  let na : no a = fun a -> naob (Inl a) in
  let nb : no b = fun b -> naob (Inr b) in
  (na, nb)

 (* P y no P no pueden valer a la vez. *)
let no_contradiccion (#a:Type) : no (yy a (no a)) =
  fun (x, f) -> f x

(* Mientras "quede" una negación, sí podemos eliminar doble
negaciones. Pero no podemos llegar a una prueba de a.

Ver también el embebimiento de lógica clásica en lógica intuicionista
via doble negación (spoiler: p se embebe como no (no p), y resulta equivalente
a la lógica clásica. *)
let elim_triple_neg (#a:Type) : no (no (no a)) -> no a =
  fun f a -> f (fun g -> g a)

(* Ejercicio. ¿Se puede en lógica intuicionista? *)
let ley_impl1 (p q : Type) : (p -> q) -> oo (no p) q =
  admit()

(* Ejercicio. ¿Se puede en lógica intuicionista? *)
let ley_impl2 (p q : Type) : oo (no p) q -> (p -> q) =
  fun npoq p ->
  match npoq with
  | Inl np -> ex_falso (np p)
  | Inr q -> q

(* Ejercicio. ¿Se puede en lógica intuicionista? *)
let ley_impl3 (p q : Type) : no (p -> q) -> yy p (no q) =
  admit()

(* Ejercicio. ¿Se puede en lógica intuicionista? *)
let ley_impl4 (p q : Type) : yy p (no q) -> no (p -> q) =
  fun (p, nq) pq -> nq (pq p)

(* Tipos para axiomas clásicos *)
type eliminacion_doble_neg = (#a:Type) -> no (no a) -> a
type tercero_excluido = (a:Type) -> oo a (no a)

(* Ejercicio *)
let lte_implica_edn (lte : tercero_excluido) (#a:Type) : eliminacion_doble_neg =
  fun #a nna ->
  match lte a with
  | Inl a -> a
  | Inr na -> ex_falso (nna na)

(* Ejercicio. ¡Difícil! *)
let edn_implica_lte (edn : eliminacion_doble_neg) (#a:Type) : oo a (no a) =
  let aux : no (no (oo a (no a))) =
    fun naona ->
      let (na, nna) = demorgan2_vuelta naona
      in nna na
  in edn aux

(* Ejercicio: ¿la ley de Peirce es intuicionista o clásica?
Demuestrelá sin axiomas para demostrar que es intuicionista,
o demuestre que implica el tercero excluido para demostrar que
es clásica. *)

type peirce = (#a:Type) -> (#b:Type) -> ((a -> b) -> a) -> a

let lte_implica_peirce (lte : tercero_excluido) : peirce =
  fun #a #b aba ->
  match lte a with
  | Inl a -> a
  | Inr na -> let ab : (a -> b) = fun a -> (na a)
              in aba ab

let peirce_implica_lte (pp : peirce) : tercero_excluido =
  fun x ->
    let mi_pierce : (((oo x (no x)) -> falso) -> oo x (no x)) -> oo x (no x) =
      pp #(oo x (no x)) #falso in
    let f : ((oo x (no x)) -> falso) -> oo x (no x) =
      fun no_x_o_nox ->
        let pf : yy (no x) (no (no x)) = demorgan2_vuelta no_x_o_nox in
        ex_falso ((snd pf) (fst pf)) in
    mi_pierce f