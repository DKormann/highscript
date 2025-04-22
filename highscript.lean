import Std.Data.HashMap


inductive Ty
| int
| string
| arrow: Ty-> Ty -> Ty
| option: Ty -> Ty

open Ty

structure Var (t: Ty) where
name: String

inductive Expr : Ty -> Ty → Type
| var : (v : Var t) → Expr s t
| self : Expr s s
| intlit : Nat → Expr s int
| stringlit : String → Expr s string
| lam {a b : Ty} (param : Var a) (body : Expr s b) : Expr s (arrow a b)
| app {a b : Ty} (f : Expr s (arrow a b)) (x : Expr s a) : Expr s b
| as (t: Ty) (x: Expr s t) : Expr s t
| ftag : String -> Expr s s
| fn: String -> Expr s s -> Expr s s

abbrev exp {s} a := Expr s a

def comp_term (fn:String) (e: Expr a b) : String :=
  match e with
  | Expr.var v => v.name
  | Expr.self => "@" ++ fn
  | Expr.intlit n => toString n
  | Expr.stringlit s => s
  | Expr.lam p b => "λ" ++ p.name ++ "." ++ comp_term fn b
  | Expr.app f x => "(" ++ comp_term fn f ++ " " ++ comp_term fn x ++ ")"
  | Expr.as t x => comp_term fn x
  | Expr.ftag n => "@" ++ n
  | Expr.fn n x => "@" ++ n

def collect {s: Ty} (e: Expr s t) (m: Std.HashMap String String) : (Std.HashMap String String) :=
 match e with
  | Expr.fn n x => if m.contains n then m else m.insert n $ "@" ++ n ++ " = " ++ comp_term n x
  | Expr.lam _ b => collect b m
  | Expr.app f x => collect x (collect f m)
  | Expr.as _ x => collect x m
  | e => m


def compile (e: Expr s s) : String :=
  let m := collect e (Std.HashMap.empty)
  let all_code := m.fold (init := "") (fun acc k v => acc ++ v ++ "\n")
  all_code


class ToVar (t:Type) (b:Ty) where
  make : t → Var b
instance {b} : ToVar (String) b where make n := Var.mk n
instance {a} : ToVar (Var a) a where make v := v

class ToExpr (t:Type) (a b:Ty) where
  make : t → Expr a b
instance : ToExpr (Expr a b) a b where make e := e
instance : ToExpr String a b where make n := Expr.var (Var.mk n)

def app {a b : Ty} (f : Expr s (arrow a b)) (x : Expr s a) : Expr s b := Expr.app f x

abbrev fn (n) (e: Expr s s) := Expr.fn n e
abbrev self {s}  := @Expr.self s

def as {s} (t:Ty) (x: Expr s t): Expr s t := x

infixl:56 "->" => arrow
infixl:56 ":" => as
infixl:56 "*" => Expr.app
infixl:56 "•" => Expr.app

def lam (builder : (Expr s a) -> Expr s b) : Expr s (arrow a b) :=
  let x: Var a := (Var.mk "x")
  let body := builder (Expr.var x)
  Expr.lam x body

#eval

  let t :Expr (arrow int int) (arrow int int) := (lam fun x => (Expr.intlit 42))
  comp_term "main" t

#eval

  let main := (int->int) : fn "main" (lam fun x => (self * (x)))

  compile main
