
-- ADT implementation
-- The aim is to implement creation of custom data types into my highscript DSL
-- each ADT can only carry one type parameter like list[int] or pair[int]
-- tagged union is not supported at the moment

-- each ADT is a list of Variants
-- each variant is a list of Recursive or Target types
-- Ty is the type of the DSL
-- Ex is expression in the DSL
-- varinst is the type of the variant instance
-- inst is the type of the ADT instance
-- Ctr is the type of the constructor for a given ADT and Variant
-- mkctr creates a constructor for a given ADT and Variant


inductive Tvar where
  | Rec : Tvar
  | T : Tvar
deriving DecidableEq


abbrev Adt := List (List Tvar)


inductive Ty where
  | int : Ty
  | string : Ty
  | arrow : Ty → Ty → Ty
  | data : (a: Adt) → Ty → Ty


open Ty


infixl:56 "->" => arrow
macro:100 adt:term:100 " [" t:term:100 "]" : term => `(data $adt $t)


mutual

  inductive Ex : (t:Ty) -> Type where
    | intlit : Nat → Ex Ty.int
    | strlit : String → Ex Ty.string
    | data : {adt: Adt} -> {t: Ty} -> (v: inst adt t) → Ex (adt[t])
    | lam : (x: Ex t1) -> (y: Ex t2) -> Ex (t1 -> t2)
    | app : (x: Ex (t1 -> t2)) -> (y: Ex t1) -> Ex t2

  inductive varinst : (a: Adt) -> (t:Ty) -> (v: List Tvar) -> Type
    | nil : varinst a t []
    | T {t:Ty} : (x: Ex t) -> (rest: varinst a t xs) -> varinst a t (Tvar.T::xs)
    | R : (x: (inst a t)) -> (rest: varinst a t xs) -> varinst a t (Tvar.Rec::xs)

  inductive inst  : (a : Adt) → (t:Ty) -> Type
    | k : (data : varinst a t v ) -> inst a t

end


def Ctr : (a:Adt) -> (t:Ty) -> (var: List Tvar) -> Type
  | a, t, [] => inst a t
  | a, t, Tvar.T::xs => Ex t -> Ctr a t xs
  | a, t, Tvar.Rec::xs => inst a t -> Ctr a t xs

def ctr : (a:Adt) -> (t:Ty) -> (v: List Tvar) -> ((varinst a t v) -> inst a t) -> (Ctr a t v)
  | _, _, [], f => (f varinst.nil)
  | a, t, Tvar.T::xs, f => fun (x: Ex t) => (ctr a t xs fun v => f (varinst.T x v))
  | a, t, Tvar.Rec::xs, f => fun (x: inst a t) => (ctr a t xs fun v => f (varinst.R x v))

def mkctr (a:Adt) (t) (v: List Tvar) : Ctr a t v := ctr a t v fun v => inst.k v


def list : Adt := [[], [Tvar.T, Tvar.Rec]]
def NIL {t} := mkctr list t []
def CONS {t} := mkctr list t [Tvar.T, Tvar.Rec]


def example_nil : inst list int := NIL
def ex_cons : inst list int := CONS (Ex.intlit 2) NIL


def pair := [[Tvar.T, Tvar.T]]
def PAIR {t} := mkctr pair t [Tvar.T, Tvar.T]

def expair : inst pair int := PAIR (Ex.intlit 2) (Ex.intlit 3)

def ex_exp_list: Ex (list [int]) := Ex.data ex_cons
def ex_pair2 : Ex (pair[list[int]]) := Ex.data (PAIR ex_exp_list ex_exp_list)
