
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

structure Var (t:Ty) where name: String

def list2prodt : (k: List Type) -> Type | [] => Unit | [x] => x | x::xs => x × (list2prodt xs)

mutual

  inductive Expr : (t:Ty) -> Type where
    | intlit : Nat → Expr Ty.int
    | strlit : String → Expr Ty.string
    | var : (v : Var t) → Expr t
    | data : {adt: Adt} -> {t: Ty} -> (v: inst adt t) → Expr (adt[t])
    | lam : (x: Var t1) -> (y: Expr t2) -> Expr (t1 -> t2)
    | app : (x: Expr (t1 -> t2)) -> (y: Expr t1) -> Expr t2
    | matcher : (x: Expr (a[t])) -> (_match a (a.Variants.map (fun x => x)) t res) -> Expr res

  inductive varinst : (a: Adt) -> (t:Ty) -> (v: List Tvar) -> Type
    | nil : varinst a t []
    | T {t:Ty} : (x: Expr t) -> (rest: varinst a t xs) -> varinst a t (Tvar.T::xs)
    | R : (x: (Expr $ a[t])) -> (rest: varinst a t xs) -> varinst a t (Tvar.Rec::xs)

  inductive inst : (a : Adt) → (t:Ty) -> Type
    | k : (n:Fin a.Variants.length ) -> (data : varinst a t a.Variants[n]) -> inst a t

  inductive MatchCase : (a:Adt) -> (t:Ty) -> (v: List Tvar) -> (res:Ty) -> Type
    | nil : Expr res -> MatchCase a t [] res
    | T : (x: Var t) -> (rest: MatchCase a t xs res) -> MatchCase a t (Tvar.T::xs) res
    | R : (x: (Var $ a[t])) -> (rest: MatchCase a t xs res) -> MatchCase a t (Tvar.Rec::xs) res

  inductive _match : (a:Adt) -> (vs:List (List Tvar)) -> (t:Ty) -> (res:Ty) -> Type
    | nil : _match a [] t res
    | cons : (x: MatchCase a (Expr t) v res) -> (_match a xs t res) -> _match a (v::xs) t res


end

def Mara := "Looovve"
#check "Dominik" ++ Mara




def Ctr : (a:Adt) -> (t:Ty) -> (var: List Tvar) -> Type
  | a, t, [] => Expr $ a[t]
  | a, t, Tvar.T::xs => Expr t -> Ctr a t xs
  | a, t, Tvar.Rec::xs => Expr (a[t]) -> Ctr a t xs

def ctr : (a:Adt) -> (t:Ty) -> (v: List Tvar) -> ((varinst a t v) -> Expr (a[t])) -> (Ctr a t v)
  | _, _, [], f => (f varinst.nil)
  | a, t, Tvar.T::xs, f => fun x => ctr a t xs fun v => f $ varinst.T x v
  | a, t, Tvar.Rec::xs, f => fun x => ctr a t xs fun v => f $ varinst.R x v

def mkctr (a:Adt) (t) (n:Nat) (p:n<a.Variants.length := by decide): Ctr a t a.Variants[n] := ctr a t a.Variants[n] fun v => Expr.data $ inst.k ⟨n,p⟩ v

-- match
def list := Adt.mk "list" [[], [Tvar.T, Tvar.Rec]]
def option := Adt.mk "option" [[], [Tvar.T]]

def NIL {t} := mkctr list t 0
def CONS {t} := mkctr list t 1

def lsi : Expr (list[int]) := CONS (Expr.intlit 22) NIL

def newVar (s:String) : Var t := { name := s}
def makelam (tag:String) (builder : (Expr a) -> Expr b) : Expr (arrow a b) :=
  let x: Var a := (newVar tag)
  Expr.lam x $ builder (Expr.var x)

macro:100 "lam" x:ident "->" body:term:100 : term => `(makelam $(Lean.quote (x.getId.toString)) fun $x => $body)
-- macro:100 "~" arg:term "{" mat:term "}" : term =>


def xx : Var int := newVar "x"
def ll : Expr (int -> int) := lam x -> x

def mat : Expr int := Expr.matcher lsi $ _match.cons
  (MatchCase.nil $ Expr.intlit 33)
  (_match.cons
    ((MatchCase.T ((newVar "head") : Var int) $ MatchCase.R (newVar "tail") $ MatchCase.nil $ Expr.intlit 22) : MatchCase list int [Tvar.T, Tvar.Rec] int)
    _match.nil
  )



#check Prod.map
#check Prod.foldI
#check ((1, 2): Nat× Nat).map
