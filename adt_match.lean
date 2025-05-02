
inductive Tvar where
  | Rec : Tvar
  | T : Tvar
deriving DecidableEq

abbrev TT := Tvar.T
abbrev RR := Tvar.Rec

@[reducible]
def Tvar.choose {a} (t:a) (r:a) : Tvar → a | Tvar.T => t | Tvar.Rec => r

def x  := Tvar.T.choose 1 2

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

inductive definedList: (a:Type) -> (l: List a ) -> Type
  | nil : definedList a []
  | cons : (x: a) -> definedList a xs → definedList a (x::xs)

mutual

  inductive Expr : (t:Ty) -> Type where
    | intlit : Nat → Expr Ty.int
    | strlit : String → Expr Ty.string
    | var : (v : Var t) → Expr t
    | data : {adt: Adt} -> {t: Ty} -> (v: DataInst adt t) → Expr (adt[t])
    | lam : (x: Var t1) -> (y: Expr t2) -> Expr (t1 -> t2)
    | app : (x: Expr (t1 -> t2)) -> (y: Expr t1) -> Expr t2
    | matcher : (x: Expr (a[t])) -> (Match a a.Variants t res) -> Expr res

  inductive VariantInst : (a: Adt) -> (t:Ty) -> (v: List Tvar) -> Type
    | nil : VariantInst a t []
    | cons : (tv:Tvar) -> (x: (Expr $ tv.choose t $ a[t] )) -> (rest: VariantInst a t xs) -> VariantInst a t (tv::xs)

  inductive DataInst : (a : Adt) → (t:Ty) -> Type
    | k : (n:Fin a.Variants.length ) -> (data : VariantInst a t a.Variants[n]) -> DataInst a t

  inductive MatchCase : (r:Ty) -> (t:Ty) -> (v: List Tvar) -> (res: Ty) -> Type
    | nil : (e:Expr res) -> MatchCase r t [] res
    | cons : (tv.choose (Var t) (Var r)) -> (MatchCase r t xs res) -> MatchCase r t (tv::xs) res

  inductive Match : (a:Adt) -> (vs:List (List Tvar)) -> (t:Ty) -> (res:Ty) -> Type
    | nil : Match a [] t res
    | cons : (x: MatchCase (a[t]) t v res) -> (Match a xs t res) -> Match a (v::xs) t res

end

def Ctr : (a:Adt) -> (t:Ty) -> (var: List Tvar) -> Type
  | a, t, [] => Expr $ a[t]
  | a, t, Tvar.T::xs => Expr t -> Ctr a t xs
  | a, t, Tvar.Rec::xs => Expr (a[t]) -> Ctr a t xs


def ctr : (a:Adt) -> (t:Ty) -> (v: List Tvar) -> ((VariantInst a t v) -> Expr (a[t])) -> (Ctr a t v)
  | _, _, [], f => (f VariantInst.nil)
  | a, t, Tvar.T::xs, f => fun x => ctr a t xs fun v => f $ VariantInst.cons Tvar.T x v
  | a, t, Tvar.Rec::xs, f => fun x => ctr a t xs fun v => f $ VariantInst.cons Tvar.Rec x v

def mkctr (a:Adt) (t) (n:Nat) (p:n<a.Variants.length := by decide): Ctr a t a.Variants[n] :=
  ctr a t a.Variants[n] fun v => Expr.data $ DataInst.k ⟨n,p⟩ v

def newVar (s:String) : Var t := { name := s}
def makelam (tag:String) (builder : (Expr a) -> Expr b) : Expr (arrow a b) :=
  let x: Var a := (newVar tag)
  Expr.lam x $ builder (Expr.var x)

macro:100 "lam" x:ident "->" body:term:100 : term => `(makelam $(Lean.quote (x.getId.toString)) fun $x => $body)

def CaseMaker (a t res: Ty) (vars : List Tvar) : (v:List Tvar) -> Type
  | [] => (Expr res) -> (MatchCase a t vars res)
  | tv::vs => (tv.choose (Var t) (Var a)) -> (CaseMaker a t res vars vs)

def caseMaker (a t res: Ty) (vars: List Tvar) : (v: List Tvar) -> (MatchCase a t v res -> MatchCase a t vars res) -> (CaseMaker a t res vars v)
  | [], f => fun (ex:Expr res) => f (MatchCase.nil ex)
  | tv::vs, f => fun (va: tv.choose (Var t) (Var (a))) => caseMaker a t res vars vs fun (cs) => f (MatchCase.cons va cs)

def mkcase  (a:Adt) (t res:Ty) (n:Nat) (p: n<a.Variants.length:= by decide) (vs:List Tvar := a.Variants[n]): (CaseMaker (a[t]) t res vs vs):=
  caseMaker (a[t]) t res vs vs (fun x => x)

def MatchMaker (a:Adt) (t res:Ty): (varis:List (List Tvar)) -> Type
  | [] => Match a (a.Variants) t res | vs::vss => (MatchCase (a[t]) t vs res) -> MatchMaker a t res vss

def matchMaker (a:Adt) (t res:Ty): (varis:List (List Tvar)) -> (f: Match a varis t res -> Match a a.Variants t res) -> MatchMaker a t res varis
  | [], f => (f Match.nil : Match a a.Variants t res)
  | vs::vss, f => fun (cs:MatchCase (a[t]) t vs res) => matchMaker a t res vss fun m => f (Match.cons cs m)

def mkmatch (a:Adt) (t res:Ty) : MatchMaker a t res (a.Variants) := matchMaker a t res (a.Variants) fun m => m


def list := Adt.mk "list" [[], [Tvar.T, Tvar.Rec]]
def option := Adt.mk "option" [[], [Tvar.T]]

def NIL {t} := mkctr list t 0
def CONS {t} := mkctr list t 1

def lsi : Expr (list[int]) := CONS (Expr.intlit 22) NIL

def cons := list.Variants[1]
def cm : CaseMaker (list[int]) int int cons cons := mkcase list int int 1

def ccf : (Var int) -> (Var (list[int])) -> Expr int -> MatchCase (list[int]) int cons int := cm
def ccs := cm (newVar "h") (newVar "t") (Expr.intlit 2)

def matcc := (mkmatch list int int)
  ((mkcase list int int 0) (Expr.intlit 1))
  ((mkcase list int int 1) (newVar "h" : Var int) (newVar "t") (Expr.intlit 2))

def matcv : Expr int := Expr.matcher lsi matcc
