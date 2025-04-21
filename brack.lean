inductive Ty : Type
| int
| string
open Ty


inductive Expr: Ty -> Type

  | int : Nat → Expr Ty.int
  | string : String → Expr string
  | leaf : Expr a
  | add : Expr int → Expr int → Expr int
  | var : String → Expr a

-- declare Expr grammar parse trees
declare_syntax_cat brack
syntax num : brack
syntax str : brack
syntax:60 brack:60 " + " brack:61 : brack
syntax "bottom" : brack
syntax "#" term "#" : brack



syntax "`[Expr| " brack "]" : term
macro_rules
  | `(`[Expr| $x:str]) => `(Expr.string $x)
  | `(`[Expr| $x:num]) => `(Expr.int $x)
  | `(`[Expr| $x + $y]) => `(Expr.add `[Expr| $x] `[Expr| $y])
  | `(`[Expr| bottom]) => `(Expr.leaf)
  | `(`[Expr| #$x#]) => pure x



-- #eval
#eval `[Expr| 1 + 2]
#eval
  let x: Expr int := `[Expr| bottom]
  -- let y: Expr string := `[Expr| bottom]
  let s:= `[Expr| #x# + #x#]
  s
