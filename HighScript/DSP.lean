

import Lean
import Std.Data.HashMap

set_option linter.unusedVariables false

inductive Ty
| int
| string
| arrow: Ty-> Ty -> Ty
| option: Ty -> Ty

open Ty
-- export Ty (int string arrow option)

structure Var (t: Ty) where
name: String



def newVar (s:String) : Var t := { name := s}
def Var.eq (v:Var t) (o:Var s) : Bool := v.name == o.name-- && v.num == o.num
def Var.dup (v:Var t) : Var t × Var t := (⟨v.name++"1"⟩, ⟨v.name ++ "2"⟩)

instance : Repr (Var t) where reprPrec v _ := s!"{v.name}"

inductive Expr : Ty → Type
  | var : (v : Var t) → Expr t
  | intlit : Nat → Expr int
  | stringlit : String → Expr string
  | arith : (op: String) -> Expr int -> Expr int -> Expr int
  | lam {a b : Ty} (param : Var a) (body : Expr b) : Expr (arrow a b)
  | app {a b : Ty} (f : Expr (arrow a b)) (x : Expr a) : Expr b
  | as (t: Ty) (x: Expr t) : Expr t
  | ftag : String -> (s:Ty) -> Expr s
  | fn: String -> Expr s -> Expr s
  | sup : Nat -> (Expr t) -> (Expr t) -> Expr t
  | nsup : (Expr t) -> (Expr t) -> Expr t
  | dub : Nat -> (Var u) -> (Var u) -> (Expr u) -> (Expr t) -> Expr t

def compile_term (fn:String) (e: Expr b) : String :=
  match e with
  | Expr.var v => v.name
  | Expr.intlit n => toString n
  | Expr.stringlit s => s
  | Expr.arith op a b => s!"({op} {compile_term fn a} {compile_term fn b})"
  | Expr.lam p b => "λ" ++ p.name ++ " " ++ compile_term fn b
  | Expr.app f x => "(" ++ compile_term fn f ++ " " ++ compile_term fn x ++ ")"
  | Expr.as t x => compile_term fn x
  | Expr.ftag n t => "@" ++ n
  | Expr.fn n x => "@" ++ n
  | Expr.sup l a b => s!"&{l}\{{compile_term fn a} {compile_term fn b}}"
  | Expr.nsup a b => s!"&\{{compile_term fn a} {compile_term fn b}}}"
  | Expr.dub l a b x y => s!"!&{l}\{{a.name} {b.name}} = {compile_term fn x} {compile_term fn y}"

def collect {t} (e: Expr t) (m: Std.HashMap String String) : (Std.HashMap String String) :=
 match e with
  | Expr.var v => m
  | Expr.intlit n => m
  | Expr.stringlit s => m
  | Expr.ftag n t => m
  | Expr.arith op a b => collect a (collect b m)
  | Expr.fn n x =>
    let m := collect x m
    if m.contains n then m else m.insert n $ "@" ++ n ++ " = " ++ compile_term n x
  | Expr.lam _ b => collect b m
  | Expr.app f x => collect x (collect f m)
  | Expr.as _ x => collect x m
  | Expr.sup _ a b => collect a (collect b m)
  | Expr.nsup a b => collect a (collect b m)
  | Expr.dub _ _ _ x y => collect x (collect y m)


def Expr.replace (e:Expr b) (v: String) (v': String) : Expr b :=
  match e with
  | var x => if (x.name == v) then var (Var.mk v') else var x
  | arith op a b => arith op (replace a v v') (replace b v v')
  | lam a b => if (a.name == v) then .lam a b else lam a (replace b v v')
  | app f x => app (replace f v v') (replace x v v')
  | fn n x => fn n (replace x v v')
  | sup n a b => sup n (replace a v v') (replace b v v')
  | nsup a b => nsup (replace a v v') (replace b v v')
  | dub n a b x y => Expr.dub n a b (if a.name == v ∨ b.name == v then x else (x.replace v v')) (y.replace v v')
  | k => k

def Expr.fmap {s} (e:Expr s) (f : {u:Ty} -> Expr u -> Expr u) : Expr s :=
  match e with
  | Expr.var v => f (Expr.var v)
  | Expr.arith op a b => f (Expr.arith op (f a) (f b))
  | Expr.lam a b => f (Expr.lam a (f b))
  | Expr.app ff x => f (Expr.app (f ff) (f x))
  | Expr.as t x => f (Expr.as t (f x))
  | Expr.fn n x => f (Expr.fn n (f x))
  | Expr.ftag n t => f (Expr.ftag n t)
  | Expr.sup n a b => f (Expr.sup n (f a) (f b))
  | Expr.nsup a b => f (Expr.nsup (f a) (f b))
  | Expr.dub n a b x y => f (Expr.dub n a b (f x) (f y))
  | k => k

def resolve  {s} : List String -> Expr ta -> Expr tb -> (Expr ta -> Expr tb -> Expr s) -> Expr s := fun c a b fn =>
  match c with
  | [] => fn a b
  | c::cs =>
    let (c', c'') := (c ++ "1", c ++ "2")
    let ex := resolve cs (a.replace c c') (b.replace c c'') fn
    let ex := @Expr.dub int s 0 (newVar c') (newVar c'') (Expr.var (newVar c)) ex
    ex


def merger {s ta tb : Ty} : (Expr ta)× (List String) -> (Expr tb)×(List String) -> (Expr ta -> Expr tb -> Expr s) -> (Expr s) × (List String) := fun (a,as) (b,bs) fn =>
  let collisions := (as.filter (fun i => i ∈ bs))
  let res := resolve collisions a b fn
  (res, bs ++ as.removeAll collisions)

def Expr.linearize (e:Expr b) : Expr b × List String :=

  match e with
  | Expr.var x => (Expr.var x, [x.name])
  | Expr.arith op a b =>
    merger (a.linearize) (b.linearize) (fun a' b' => Expr.arith op a' b')
  | Expr.dub n a b x r =>
    let (x', xs) := x.linearize
    let xs := xs.removeAll ([a.name, b.name])
    merger (x', xs) (r.linearize) (fun x'' r'' => Expr.dub n a b x'' r'')
  | Expr.lam a bod =>
    let (b', bs) := bod.linearize
    let bs := bs.filter (fun i => i != a.name)
    (Expr.lam a b', bs)
  | .app a b => merger a.linearize b.linearize (fun a' b' => Expr.app a' b')
  | .as t x => x.linearize
  | .fn n x =>
    let (x', xs) := x.linearize
    (Expr.fn n x', xs)
  | .sup n a b => merger a.linearize b.linearize (fun a' b' => Expr.sup n a' b')
  | .nsup a b => merger a.linearize b.linearize (fun a' b' => Expr.nsup a' b')
  | k => (k,[])


def compile {s} (e: Expr s) : String :=
  let m := collect (e.linearize).fst (Std.HashMap.empty)
  let all_code := m.fold (init := "") (fun acc _ v => acc ++ v ++ "\n")
  all_code


class ToVar (t:Type) (b:Ty) where
  make : t → Var b
instance {b} : ToVar (String) b where make n := newVar n
instance {a} : ToVar (Var a) a where make v := v

class ToExpr (t:Type) (b:Ty) where
  make : t → Expr b
instance : ToExpr (Expr b)  b where make e := e
instance : ToExpr String b where make n := Expr.var (newVar n)
instance : ToExpr (Var a) a where make v := Expr.var v

def expr {a b} [ToExpr a b] (x: a) : Expr b := ToExpr.make x
abbrev fn (n:String) (e: Expr s) := Expr.fn n e

def astype  (t:Ty) (x: Expr t): Expr t := x

infixl:56 "->" => arrow



def makelam (tag:String) (builder : (Expr a) -> Expr b) : Expr (arrow a b) :=
  let x: Var a := (newVar tag)
  let body := builder (Expr.var x)
  Expr.lam x body

def tag (n:String) : Expr s := Expr.ftag n s

macro:100 "lam" x:ident "->" body:term:100 : term => `(makelam $(Lean.quote (x.getId.toString)) fun $x => $body)


macro:50 "@" n:ident ":" typ:term:50 "; " body:term:50 : term=> `(let $n := Expr.ftag $(Lean.quote (n.getId.toString)) $typ; $body)
macro:50 "@" n:ident "=" val:term:50 "; " body:term:50 : term=> `(let $n := fn $(Lean.quote (n.getId.toString)) $val; $body)
macro:50 "#" n:num : term => `(Expr.intlit $n)
macro:50 "#" n:str : term => `(Expr.stringlit $n)

macro:50 v:term:50 "as" t:term:51 : term => `(astype $t $v)
macro:50  a:term:50 "(" b:term:50 ")" : term => `(Expr.app $a $b)

macro:50 "var" n:ident ":" t:term:50 ";" bod:term  : term => `(let $n :Var $t := newVar $(Lean.quote (n.getId.toString)); $bod)
macro:50  "&" l:num "{" a:term:50 "," b:term:50  "}" "=" c:term:50 ";" d:term:50 : term => `(Expr.dub $l $a $b $c $d)
macro:50  "&" l:num "{" a:term:50 "," b:term:50  "}" : term => `(Expr.sup $l $a $b)
macro:50  a:term:50 "+" b:term:51 : term => `(Expr.arith "+" $a $b)
macro:50  a:term:50 "-" b:term:51 : term => `(Expr.arith "-" $a $b)
macro:60  a:term:60 "*" b:term:61 : term => `(Expr.arith "*" $a $b)
macro:60  a:term:60 "/" b:term:61 : term => `(Expr.arith "/" $a $b)


macro "MyMacro" : term => `(Expr.intlit 22)
def MyConst := 22

#eval
  let main := fn "main" $ lam x -> (x) as (int -> int)
  compile main

#eval
  @main = &1 { #1, #2} as int;
  compile main

#eval
  var x : int;
  var y : int;
  let ex :=  &1 { x, y} = #3; (Expr.var x) as int
  @main = ex;
  compile main

#eval
  @tt : int -> int;
  @tt = lam x -> (tt (x)) as (int -> int);
  @main = tt;
  compile main

#eval

  @main = lam x -> ((lam y -> x as (int -> int)) (x));
  compile (main)


def TOTO := 123
