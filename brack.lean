


inductive Ty : Type
| int
| string
| arrow: Ty -> Ty -> Ty
| option: Ty -> Ty
| list: Ty -> Ty
open Ty

inductive Expr: Ty -> Type
  | int : Nat → Expr Ty.int
  | string : String → Expr string
  | leaf : Expr a
  | add : Expr int → Expr int → Expr int
  | var : String → Expr a
  | none : Expr (option a)
  | some : Expr a → Expr (option a)
  | nil : Expr (list a)
  | cons : Expr a → Expr (list a) → Expr (list a)
  | astype : (t:Ty) → Expr t → Expr t


def compile (e:Expr t) : String := match e with
  | Expr.int n => toString n
  | Expr.string s => s
  | Expr.add x y => compile x ++ " + " ++ compile y
  | Expr.leaf => "leaf"
  | Expr.var n => n
  | Expr.none => "none"
  | Expr.some x => "some(" ++ compile x ++ ")"
  | Expr.nil => "nil"
  | Expr.cons x xs => "cons(" ++ compile x ++ ", " ++ compile xs ++ ")"
  | Expr.astype t x => "astype(" ++ compile x ++ ")"



declare_syntax_cat brack
syntax num : brack
syntax str : brack
syntax:60 brack:60 " + " brack:61 : brack
syntax "leaf" : brack
syntax "#" term "#" : brack
syntax "(" brack ")" : brack
syntax "none" : brack
syntax "some(" brack ")" : brack
syntax "nil" : brack
syntax "cons(" brack "," brack ")" : brack
syntax:50 brack:50 "as" term:51 : brack



syntax "`[ " brack "]" : term
macro_rules
  | `(`[ $x:str]) => `(Expr.string $x)
  | `(`[ $x:num]) => `(Expr.int $x)
  | `(`[ $x + $y]) => `(Expr.add `[ $x] `[ $y])
  | `(`[ leaf]) => `(Expr.leaf)
  | `(`[ #$x#]) => pure x
  | `(`[ ($x:brack) ]) => `(`[ $x])
  | `(`[ none]) => `(Expr.none)
  | `(`[ some($x:brack)]) => `(Expr.some `[ $x])
  | `(`[ nil]) => `(Expr.nil)
  | `(`[ cons($x:brack, $y:brack)]) => `(Expr.cons `[ $x] `[ $y])
  | `(`[ $y:brack as $x]) => `( Expr.astype $x `[ $y])




-- #eval
#eval compile `[ 1 + 2]
#eval
  let x: Expr int := `[ leaf]
  let y: Expr string := `[ leaf]
  let s:= `[ #x# + #x#]
  let l:= `[ cons(1 + 2, cons(2, nil))]
  let o:= `[ leaf as int ]
  compile l
