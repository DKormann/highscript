import Lean
import Std.Data.HashMap


inductive Ty
| int
| string
| arrow: Ty-> Ty -> Ty
| option: Ty -> Ty

open Ty

structure Var (t: Ty) where
name: String

inductive Expr : Ty → Type
| var : (v : Var t) → Expr t
-- | self : (t:Ty) -> Expr t
| intlit : Nat → Expr int
| stringlit : String → Expr string
| lam {a b : Ty} (param : Var a) (body : Expr b) : Expr (arrow a b)
| app {a b : Ty} (f : Expr (arrow a b)) (x : Expr a) : Expr b
| as (t: Ty) (x: Expr t) : Expr t
| ftag : String -> (s:Ty) -> Expr s
| fn: String -> Expr s -> Expr s


def comp_term (fn:String) (e: Expr b) : String :=
  match e with
  | Expr.var v => v.name
  | Expr.intlit n => toString n
  | Expr.stringlit s => s
  | Expr.lam p b => "λ" ++ p.name ++ "." ++ comp_term fn b
  | Expr.app f x => "(" ++ comp_term fn f ++ " " ++ comp_term fn x ++ ")"
  | Expr.as t x => comp_term fn x
  | Expr.ftag n t => "@" ++ n
  | Expr.fn n x => "@" ++ n

def collect {t} (e: Expr t) (m: Std.HashMap String String) : (Std.HashMap String String) :=
 match e with
  | Expr.fn n x => if m.contains n then m else m.insert n $ "@" ++ n ++ " = " ++ comp_term n x
  | Expr.lam _ b => collect b m
  | Expr.app f x => collect x (collect f m)
  | Expr.as _ x => collect x m
  | e => m


def compile {s} (e: Expr s) : String :=
  let m := collect e (Std.HashMap.empty)
  let all_code := m.fold (init := "") (fun acc _ v => acc ++ v ++ "\n")
  all_code


class ToVar (t:Type) (b:Ty) where
  make : t → Var b
instance {b} : ToVar (String) b where make n := Var.mk n
instance {a} : ToVar (Var a) a where make v := v

class ToExpr (t:Type) (b:Ty) where
  make : t → Expr b
instance : ToExpr (Expr b)  b where make e := e
instance : ToExpr String b where make n := Expr.var (Var.mk n)
instance : ToExpr (Var a) a where make v := Expr.var v

def app {a b : Ty} (f : Expr (arrow a b)) (x : Expr a) : Expr b := Expr.app f x

abbrev fn (n) (e: Expr s) := Expr.fn n e

def astype  (t:Ty) (x: Expr t): Expr t := x

infixl:56 "->" => arrow
infixl:56 "*" => Expr.app
infixl:56 "•" => Expr.app


def makelam (builder : (Expr a) -> Expr b) : Expr (arrow a b) :=
  let x: Var a := (Var.mk "x")
  let body := builder (Expr.var x)
  Expr.lam x body

def tag (n:String) : Expr s := Expr.ftag n s

macro:100 "lam" x:ident "->" body:term:100 : term => `(makelam fun $x => $body)

macro:100 "@" n:ident "=" val:term "; " body:term : term=> `(let $n := $val; $body)
macro:50 v:term:50 "as" t:term:51 : term => `(astype $t $v)


#eval



  let x := Expr.intlit 44 as int
  let f := lam x -> (x) as (int -> int)



  compile f



#eval
  @tt = 44;
  tt
