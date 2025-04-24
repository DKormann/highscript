
structure Var where
  name: String
  num: Nat

instance : BEq Var where beq (a b:Var) : Bool := a.name == b.name && a.num == b.num

def newVar (s:String) : Var := { name := s, num := 1}
def Var.dup (v:Var) : Var × Var := (⟨v.name, v.num * 2⟩, ⟨v.name, v.num * 2 + 1⟩)


#eval
  let x : Var := newVar "x"
  let (x1, x2) := Var.dup x
  let (x3, x4) := Var.dup x1
  x1

inductive Expr : Type
  | var : Var -> Expr
  | bind : (x:Var) -> (Expr) -> (Expr) -> Expr
  | add : Expr -> Expr -> Expr
  | dup : Var -> Var -> Var -> Expr -> Expr
open Expr



def getFrees : (e:Expr) → List Var
  | .bind x v r => x :: (getFrees v ++ (getFrees r).filter (fun y => y != x))
  | .var x => [x]
  | .add a b => (getFrees a) ++ (getFrees b)
  | .dup a b x r => (getFrees r).filter (fun y => y != a && y != b) ++ [x]


def Expr.replaceVar (e:Expr) (v:Var) (v':Var) : Expr := match e with
  | .bind x vl r => Expr.bind x (vl.replaceVar v v') (if x==v then r else r.replaceVar v v')
  | .var x => if x == v then .var v' else .var x
  | .add a b => .add (a.replaceVar v v') (b.replaceVar v v')
  | .dup a b x r =>
    if x == v then .dup a b v' r
    else if a == v ∨ b == v then e
    else .dup a b x (r.replaceVar v v')






def compile : (e:Expr) -> String
  | .bind x v r => s!"{x.name} = {compile v} ; {compile r}"
  | .var x => x.name
  | .add a b => s!"({compile a} + {compile b}})"
  | .dup a b x r => s!"~\{{a.name} {b.name}} = {x.name} ; {compile r}}"



macro:50 "#" n:str : term => `(Expr.var $ newVar $n)

example : (compile (dup (newVar "a") (newVar "b") (newVar "x") (#"r")) = "~{a b} = x ; r}") := by rfl
example : ((compile (#"n")) = "n") := by rfl
