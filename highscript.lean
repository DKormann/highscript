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
| intlit : Nat → Expr int
| stringlit : String → Expr string
| lam {a b : Ty} (param : Var a) (body : Expr b) : Expr (arrow a b)
| app {a b : Ty} (f : Expr (arrow a b)) (x : Expr a) : Expr b
| as (t: Ty) (x: Expr t) : Expr t
| ftag : String -> (s:Ty) -> Expr s
| fn: String -> Expr s -> Expr s
| sup : Nat -> (Expr t) -> (Expr t) -> Expr t
| nsup : (Expr t) -> (Expr t) -> Expr t
| dub : Nat -> (Var t) -> (Var t) -> (Expr t) -> (Expr t) -> Expr t


def compile_term (fn:String) (e: Expr b) : String :=
  match e with
  | Expr.var v => v.name
  | Expr.intlit n => toString n
  | Expr.stringlit s => s
  | Expr.lam p b => "λ" ++ p.name ++ "." ++ compile_term fn b
  | Expr.app f x => "(" ++ compile_term fn f ++ " " ++ compile_term fn x ++ ")"
  | Expr.as t x => compile_term fn x
  | Expr.ftag n t => "@" ++ n
  | Expr.fn n x => "@" ++ n
  | Expr.sup l a b => s!"&{l}\{{compile_term fn a} {compile_term fn b}}"
  | Expr.nsup a b => s!"&\{{compile_term fn a} {compile_term fn b}}}"
  | Expr.dub l a b x y => s!"!&{l}\{{a.name} {b.name}} = {compile_term fn x} {compile_term fn y}"


def collect {t} (e: Expr t) (m: Std.HashMap String String) : (Std.HashMap String String) :=
 match e with
  | Expr.fn n x =>
    let m := collect x m
    if m.contains n then m else m.insert n $ "@" ++ n ++ " = " ++ compile_term n x
  | Expr.lam _ b => collect b m
  | Expr.app f x => collect x (collect f m)
  | Expr.as _ x => collect x m
  | Expr.sup _ a b => collect a (collect b m)
  | Expr.nsup a b => collect a (collect b m)
  | Expr.dub _ _ _ x y => collect x (collect y m)
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

def expr {a b} [ToExpr a b] (x: a) : Expr b := ToExpr.make x

-- def app {a b : Ty} (f : Expr (arrow a b)) (x : Expr a) : Expr b := Expr.app f x

abbrev fn (n:String) (e: Expr s) := Expr.fn n e

def astype  (t:Ty) (x: Expr t): Expr t := x

infixl:56 "->" => arrow



def makelam (builder : (Expr a) -> Expr b) : Expr (arrow a b) :=
  let x: Var a := (Var.mk "x")
  let body := builder (Expr.var x)
  Expr.lam x body

def tag (n:String) : Expr s := Expr.ftag n s

macro:100 "lam" x:ident "->" body:term:100 : term => `(makelam fun $x => $body)


macro:50 "@" n:ident ":" typ:term:50 "; " body:term:50 : term=> `(let $n := Expr.ftag $(Lean.quote (n.getId.toString)) $typ; $body)
macro:50 "@" n:ident "=" val:term:50 "; " body:term:50 : term=> `(let $n := fn $(Lean.quote (n.getId.toString)) $val; $body)
macro:50 "#" n:num : term => `(Expr.intlit $n)
macro:50 "#" n:str : term => `(Expr.stringlit $n)

macro:50 v:term:50 "as" t:term:51 : term => `(astype $t $v)
macro:50  a:term:50 "(" b:term:50 ")" : term => `(Expr.app $a $b)

macro:50 "var" n:ident ":" t:term:50 ";" bod:term  : term => `(let $n :Var $t := Var.mk $(Lean.quote (n.getId.toString)); $bod)
macro:50  "&" l:num "{" a:term:50 "," b:term:50  "}" "=" c:term:50 ";" d:term:50 : term => `(Expr.dub $l $a $b $c $d)
macro:50  "&" l:num "{" a:term:50 "," b:term:50  "}" : term => `(Expr.sup $l $a $b)


#eval
  let x := Expr.intlit 44 as int
  let f := lam x -> (x) as (int -> int)
  let main := fn "main" $ lam x -> (x) as (int -> int)
  compile main

#eval
  @main = &1 { #1, #2} as int;
  compile main

#eval

  var x : int;
  var y : int;
  let ex :=  &1 { x, y} = #3; (Expr.var x) as int
  @hello = #"hello";
  @main = ex;
  compile main


#eval

  @tt : int -> int;
  @tt = lam x -> (tt (x)) as (int -> int);

  let d := #22 as int;

  @main = tt;
  compile main
