import Lean

open Lean Elab Meta


inductive IMPType
  | nat  : IMPType
  | bool : IMPType
  | string : IMPType

open IMPType

inductive IMPLit : IMPType → Type
  | nat  : Nat  → IMPLit IMPType.nat
  | bool : Bool → IMPLit IMPType.bool
  | string : String → IMPLit IMPType.string

inductive IMPUnOp : IMPType -> IMPType → Type
  | not : IMPUnOp IMPType.bool IMPType.bool

inductive IMPBinOp : IMPType → IMPType → Type
  | add : IMPBinOp IMPType.nat IMPType.nat
  | and : IMPBinOp IMPType.bool IMPType.bool
  | less : IMPBinOp IMPType.nat IMPType.bool

inductive IMPExpr : IMPType -> Type
  | lit : IMPLit x → IMPExpr x
  | var : String → IMPExpr u
  | un  : IMPUnOp a b → IMPExpr a → IMPExpr b
  | bin : IMPBinOp a b → IMPExpr a → IMPExpr a → IMPExpr b

inductive IMPProgram
  | Skip   : IMPProgram
  | Assign : String → IMPExpr u → IMPProgram
  | Seq    : IMPProgram → IMPProgram → IMPProgram
  | If     : IMPExpr bool → IMPProgram → IMPProgram → IMPProgram
  | While  : IMPExpr bool → IMPProgram → IMPProgram



declare_syntax_cat imp_lit
syntax num       : imp_lit
syntax "true"    : imp_lit
syntax "false"   : imp_lit

def elabIMPLit : Syntax → MetaM Expr
  -- `mkAppM` creates an `Expr.app`, given the function `Name` and the args
  -- `mkNatLit` creates an `Expr` from a `Nat`
  | `(imp_lit| $n:num) => mkAppM ``IMPLit.nat  #[mkNatLit n.getNat]
  | `(imp_lit| true  ) => mkAppM ``IMPLit.bool #[.const ``Bool.true []]
  | `(imp_lit| false ) => mkAppM ``IMPLit.bool #[.const ``Bool.false []]
  | _ => throwUnsupportedSyntax

elab "test_elabIMPLit " l:imp_lit : term => elabIMPLit l

#reduce test_elabIMPLit 4     -- IMPLit.nat 4
#reduce test_elabIMPLit true  -- IMPLit.bool true
#reduce test_elabIMPLit false -- IMPLit.bool true


declare_syntax_cat imp_unop
syntax "not"     : imp_unop

def elabIMPUnOp : Syntax → MetaM Expr
  | `(imp_unop| not) => return .const ``IMPUnOp.not []
  | _ => throwUnsupportedSyntax

declare_syntax_cat imp_binop
syntax "+"       : imp_binop
syntax "and"     : imp_binop
syntax "<"       : imp_binop

def elabIMPBinOp : Syntax → MetaM Expr
  | `(imp_binop| +)   => return .const ``IMPBinOp.add []
  | `(imp_binop| and) => return .const ``IMPBinOp.and []
  | `(imp_binop| <)   => return .const ``IMPBinOp.less []
  | _ => throwUnsupportedSyntax

declare_syntax_cat                   imp_expr
syntax imp_lit                     : imp_expr
syntax ident                       : imp_expr
syntax imp_unop imp_expr           : imp_expr
syntax imp_expr imp_binop imp_expr : imp_expr
syntax "(" imp_expr ")" : imp_expr


partial def elabIMPExpr : Syntax → MetaM Expr
  | `(imp_expr| $l:imp_lit) => do
    let l ← elabIMPLit l
    mkAppM ``IMPExpr.lit #[l]
  -- `mkStrLit` creates an `Expr` from a `String`
  | `(imp_expr| $i:ident) => mkAppM ``IMPExpr.var #[mkStrLit i.getId.toString]
  | `(imp_expr| $b:imp_unop $e:imp_expr) => do
    let b ← elabIMPUnOp b
    let e ← elabIMPExpr e -- recurse!
    mkAppM ``IMPExpr.un #[b, e]
  | `(imp_expr| $l:imp_expr $b:imp_binop $r:imp_expr) => do
    let l ← elabIMPExpr l -- recurse!
    let r ← elabIMPExpr r -- recurse!
    let b ← elabIMPBinOp b
    mkAppM ``IMPExpr.bin #[b, l, r]
  | `(imp_expr| ($e:imp_expr)) => elabIMPExpr e
  | _ => throwUnsupportedSyntax

elab "test_elabIMPExpr " e:imp_expr : term => elabIMPExpr e

#reduce test_elabIMPExpr a
-- IMPExpr.var "a"

#reduce test_elabIMPExpr a + 5
-- IMPExpr.bin IMPBinOp.add (IMPExpr.var "a") (IMPExpr.lit (IMPLit.nat 5))

#reduce test_elabIMPExpr 1 + 2
-- IMPExpr.bin IMPBinOp.add (IMPExpr.lit (IMPLit.nat 1)) (IMPExpr.lit (IMPLit.bool true))


declare_syntax_cat           imp_program
syntax "skip"              : imp_program
syntax ident ":=" imp_expr : imp_program

syntax imp_program ";;" imp_program : imp_program

syntax "if" imp_expr "then" imp_program "else" imp_program "fi" : imp_program
syntax "while" imp_expr "do" imp_program "od" : imp_program

partial def elabIMPProgram : Syntax → MetaM Expr
  | `(imp_program| skip) => return .const ``IMPProgram.Skip []
  | `(imp_program| $i:ident := $e:imp_expr) => do
    let i : Expr := mkStrLit i.getId.toString
    let e ← elabIMPExpr e
    mkAppM ``IMPProgram.Assign #[i, e]
  | `(imp_program| $p₁:imp_program ;; $p₂:imp_program) => do
    let p₁ ← elabIMPProgram p₁
    let p₂ ← elabIMPProgram p₂
    mkAppM ``IMPProgram.Seq #[p₁, p₂]
  | `(imp_program| if $e:imp_expr then $pT:imp_program else $pF:imp_program fi) => do
    let e ← elabIMPExpr e
    let pT ← elabIMPProgram pT
    let pF ← elabIMPProgram pF
    mkAppM ``IMPProgram.If #[e, pT, pF]
  | `(imp_program| while $e:imp_expr do $pT:imp_program od) => do
    let e ← elabIMPExpr e
    let pT ← elabIMPProgram pT
    mkAppM ``IMPProgram.While #[e, pT]
  | _ => throwUnsupportedSyntax


elab ">>" p:imp_program "<<" : term => elabIMPProgram p

#reduce >>
a := 5;;
if not a and 3 < 4 then
  c := 5
else
  a := a + 1
fi;;
b := 10
<<
