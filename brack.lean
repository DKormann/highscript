


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

-- declare Expr grammar parse trees
declare_syntax_cat brack
syntax num : brack
syntax str : brack
syntax:60 brack:60 " + " brack:61 : brack
syntax "bottom" : brack
syntax "#" term "#" : brack
syntax "(" brack ")" : brack
syntax "none" : brack
syntax "some(" brack ")" : brack
syntax "nil" : brack
syntax "cons(" brack "," brack ")" : brack


syntax "`[Expr| " brack "]" : term
macro_rules
  | `(`[Expr| $x:str]) => `(Expr.string $x)
  | `(`[Expr| $x:num]) => `(Expr.int $x)
  | `(`[Expr| $x + $y]) => `(Expr.add `[Expr| $x] `[Expr| $y])
  | `(`[Expr| bottom]) => `(Expr.leaf)
  | `(`[Expr| #$x#]) => pure x
  | `(`[Expr| ($x:brack) ]) => `(`[Expr| $x])
  | `(`[Expr| none]) => `(Expr.none)
  | `(`[Expr| some($x:brack)]) => `(Expr.some `[Expr| $x])
  | `(`[Expr| nil]) => `(Expr.nil)
  | `(`[Expr| cons($x:brack, $y:brack)]) => `(Expr.cons `[Expr| $x] `[Expr| $y])




-- #eval
#eval `[Expr| 1 + 2]
#eval
  let x: Expr int := `[Expr| bottom]
  -- let y: Expr string := `[Expr| bottom]
  let s:= `[Expr| #x# + #x#]
  let l:= `[Expr| cons(1 + 2, cons(2, nil))]
  l
