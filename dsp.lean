


inductive Ty
| int
| string
| arrow: Ty-> Ty -> Ty
| option: Ty -> Ty
| list: Ty -> Ty
| tree: Ty -> Ty
open Ty

structure Var (t: Ty) where
name: String


inductive Expr : Ty → Type
| var : (v : Var t) → Expr t
| intlit : Nat → Expr int
| stringlit : String → Expr string
| lam {a b : Ty} (param : Var a) (body : Expr b) : Expr (arrow a b)
| app {a b : Ty} (f : Expr (arrow a b)) (x : Expr a) : Expr b

| sup {a:Ty} (label: Nat) (x: Expr a) (y: Expr a) : Expr a
| dup {a b:Ty} (label: Nat) (x y: Var a) (z: Expr a) (r: Expr b): Expr b

| none : Expr (option a)
| some  (x : Expr a) : Expr (option a)
| nil : Expr (list a)
| cons  (x : Expr a) (xs : Expr (list a)) : Expr (list a)
| leaf (x: Expr a) : Expr $ tree a
| node (l: Expr $ tree a) (r: Expr $ tree a) : Expr $ tree a
| mmatch {a b : Ty} (x: Expr (option a)) (dft: Expr b) (bdr: Var a) (bod: Expr b) : Expr b
| lmatch {a b : Ty} (x: Expr $ list a) (n: Expr b) (h: Var a) (t: Var $ list a) (bod: Expr b): Expr b
| tmatch {a b : Ty} (x: Expr $ tree a) (lfb: Var a) (r: Expr b) (ln rn: Var $ tree a) (bod: Expr b): Expr b


class ToMatch (r:Ty) (t: Type) where make :t -> Expr r

instance {a b} : ToMatch (b:Ty) ((Expr $ option a) × (Expr b) × (Var a) × (Expr b)) where
  make := λ ⟨x, d, v, e⟩ => Expr.mmatch x d v e
instance {a b} : ToMatch (b:Ty) ((Expr $ list a) × (Expr b) × ((Var a) × (Var $ list a)) × (Expr b)) where
  make := λ (x, d, (va, vb), e) => Expr.lmatch x d va vb e
instance {a b} : ToMatch (b:Ty) ((Expr $ tree a) × ((Var a) × (Expr b)) × ((Var $ tree a) × (Var $ tree a)) × (Expr b)) where
  make := λ (x, (va, vb), (la, ra), e) => Expr.tmatch x va vb la ra e

def makeMatch {r:Ty} {t:Type} [ToMatch r t] (x: t) : Expr r := ToMatch.make x

class ToVar (t:Type) (b:Ty) where make : t → Var b
instance {b} : ToVar (String) b where make n := Var.mk n
instance {a} : ToVar (Var a) a where make v := v

class ToExpr (t: Type) (b:Ty) where make : t → Expr b
instance : ToExpr (Expr b) b where make e := e
instance : ToExpr Nat int where make n := Expr.intlit n
instance : ToExpr String string where make n := Expr.stringlit n
-- instance : ToExpr (Var a) a where make v := Expr.var v
instance : ToExpr (Var int) int where make v := Expr.var v
instance {a b} [ToExpr a b] : ToExpr (Option a) (option b) where make o := match o with
  | Option.none => Expr.none
  | Option.some x => Expr.some (ToExpr.make x)
def lExpr {a b} [ToExpr a b] (l:List a) : Expr (list b) := match l with
  | [] => Expr.nil
  | x::xs => Expr.cons (ToExpr.make x) (lExpr xs)
instance [ToExpr a b] : ToExpr (List a) (Ty.list b) where make o := (lExpr o)


def eval  (x:Expr r) := match x with
  | Expr.var v => v.name
  | Expr.intlit n => toString n
  | Expr.stringlit s => s
  | Expr.lam p b => s!"λ{p.name}. {eval b}"
  | Expr.app f x => s!"({eval f} {eval x})"

  | Expr.sup l x y => s!"&{l}\{{eval x} {eval y}}"
  | Expr.dup l x y z r => s!"!&{l}\{{x.name} {y.name}}={eval z} {eval r}"

  | Expr.nil => "#Nil"
  | Expr.cons x xs => s!"#Cons\{{eval x} {eval xs}}"
  | Expr.leaf x => s!"#Leaf\{{eval x}}"
  | Expr.node l r => s!"#Node\{{eval l} {eval r}}"

  | Expr.none => "none"
  | Expr.some x => s!"some {eval x}"
  | Expr.mmatch i d b x => s!"~({eval i}) \{ #None:{eval d} #Some\{{b.name}}: {eval x}}"
  | Expr.lmatch i d h t bod => s!"~({eval i}) \{ #Nil:{eval d} #Cons\{{h.name} {t.name}}: {eval bod}}"
  | Expr.tmatch x lfb r ln rn bod => s!"~({eval x}) \{ #Leaf\{{lfb.name}:{eval r} #Node\{{ln.name} {rn.name}} : {eval bod}}"


notation "(" a "•" b ")" => Expr.app a (ToExpr.make b)

def lam {a b} [ToVar a ta] [ToExpr b tb] (x: a) (e: b) : Expr (arrow ta tb) :=
  Expr.lam (ToVar.make x) (ToExpr.make e)

def app {ta tb} {b} [ToExpr b ta] (f: (Expr (arrow ta tb))) (x: b) :=
  let fn : Expr (arrow ta tb) := ToExpr.make f
  Expr.app fn (ToExpr.make x)


abbrev INT := Expr int

def ii := INT

def arro a b := Expr (arrow a b)

def as (t:Ty) (e:Expr t) := e

infixl:56 ":" => as
infixl:56 "->" => Ty.arrow




#eval
  let x: Var int := ⟨"x"⟩

  let somi: Expr (option int) := Expr.some (Expr.intlit 22)

  let mmatchi : Expr int := (ToMatch.make (somi, Expr.intlit 33, x, Expr.var x))

  let lsi :Expr (list int) := (ToExpr.make [22, 33, 44])

  let fn := (int -> int) : lam x (Expr.var x)

  let l2 := (int -> int) : lam x x

  let ap := app fn x

  let ap2 : ii := app fn x



  eval ap
