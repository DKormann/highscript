
-- ADT implementation
-- The aim is to implement creation of custom data types into my highscript DSL
-- each ADT can only carry one type parameter like list[int] or pair[int]
-- tagged union is not supported at the moment

-- each ADT is a list of Variants
-- each variant is a list of Recursive or Target types
-- Ty is the type of the DSL
-- Expr is expression in the DSL
-- varinst is the type of the variant instance
-- inst is the type of the ADT instance
-- Ctr is the type of the constructor for a given ADT and Variant
-- mkctr creates a constructor for a given ADT and Variant


inductive Tvar where
  | Rec : Tvar
  | T : Tvar
deriving DecidableEq

structure Adt where
  name: String
  Variants : List (List Tvar)

inductive Ty where
  | int : Ty
  | string : Ty
  | arrow : Ty → Ty → Ty
  | data : (a: Adt) → Ty → Ty


open Ty

infixl:56 "->" => arrow
macro:100 adt:term:100 " [" t:term:100 "]" : term => `(data $adt $t)

mutual

  inductive Expr : (t:Ty) -> Type where
    | intlit : Nat → Expr Ty.int
    | strlit : String → Expr Ty.string
    | data : {adt: Adt} -> {t: Ty} -> (v: inst adt t) → Expr (adt[t])
    | lam : (x: Expr t1) -> (y: Expr t2) -> Expr (t1 -> t2)
    | app : (x: Expr (t1 -> t2)) -> (y: Expr t1) -> Expr t2

  inductive varinst : (a: Adt) -> (t:Ty) -> (v: List Tvar) -> Type
    | nil : varinst a t []
    | T {t:Ty} : (x: Expr t) -> (rest: varinst a t xs) -> varinst a t (Tvar.T::xs)
    | R : (x: (Expr $ a[t])) -> (rest: varinst a t xs) -> varinst a t (Tvar.Rec::xs)

  inductive inst  : (a : Adt) → (t:Ty) -> Type
    | k : (n:Fin a.Variants.length ) -> (data : varinst a t a.Variants[n]) -> inst a t

end

def Ctr : (a:Adt) -> (t:Ty) -> (var: List Tvar) -> Type
  | a, t, [] => Expr $ a[t]
  | a, t, Tvar.T::xs => Expr t -> Ctr a t xs
  | a, t, Tvar.Rec::xs => Expr (a[t]) -> Ctr a t xs

def ctr : (a:Adt) -> (t:Ty) -> (v: List Tvar) -> ((varinst a t v) -> Expr (a[t])) -> (Ctr a t v)
  | _, _, [], f => (f varinst.nil)
  | a, t, Tvar.T::xs, f => fun x => ctr a t xs fun v => f $ varinst.T x v
  | a, t, Tvar.Rec::xs, f => fun x => ctr a t xs fun v => f $ varinst.R x v

def mkctr (a:Adt) (t) (n:Nat) (p:n<a.Variants.length := by decide): Ctr a t a.Variants[n] := ctr a t a.Variants[n] fun v => Expr.data $ inst.k ⟨n,p⟩ v


def list : Adt := ⟨"list", [[], [Tvar.T, Tvar.Rec]]⟩
def NIL {t} := mkctr list t 0
def CONS {t} := mkctr list t 1

def example_nil : Expr $ list[int] := NIL
def ex_cons : Expr $ list[int] := CONS (Expr.intlit 2) NIL

def pair : Adt := ⟨"pair", [[Tvar.T, Tvar.T]]⟩
def PAIR {t} := mkctr pair t 0

def expair : Expr (pair[int]) := PAIR (Expr.intlit 2) (Expr.intlit 3)
def ex_pair2 : Expr (pair[list[int]]) := (PAIR ex_cons ex_cons)

def option : Adt := ⟨"option", [[Tvar.T], []]⟩
def SOME {t} := mkctr option t 0
def NONE {t} := mkctr option t 1




-- matching on ADTs
