-- parsing and compiling of AST (compilation needed for display)

import Lean
open Lean Meta Macro Elab


inductive Vec (Tag T: Type)
  | nil : Tag -> Vec Tag T
  | cons : T -> Vec Tag T -> Vec Tag T
deriving  BEq, Hashable, Repr

def Vec.mk {Tag T: Type} (tag:Tag) :(t:List T) -> Vec Tag T
  | .nil => Vec.nil tag
  | .cons a r => Vec.cons a $ Vec.mk tag r

def Vec.size : (v: Vec Tag T) -> Nat
  | .nil _ => 0
  | .cons _ xs => 1 + xs.size

def Vec.tag:  (Vec Tag T) -> Tag
  | .nil tag => tag
  | .cons _ xs => xs.tag

def Vec.toList : (v: Vec Tag T) -> List T
  | .nil _ => []
  | .cons a xs => a :: xs.toList

inductive Ty
  | bool
  | nat
  | string
  | arrow: Ty -> Ty -> Ty
  | adt : Vec String (Vec String (Option Ty)) -> Ty
deriving BEq, Hashable, Repr


abbrev DataField := Option Ty
abbrev Variant := Vec String DataField
abbrev Adt := Vec String Variant


def DataField.Ty : (self: DataField) -> (adt: Adt) -> Ty
  | none, a => .adt a
  | some t, _ => t

instance : Repr DataField where
  reprPrec df _ := match df with
    | none => "self"
    | some t => repr t

def v  := (Vec.mk "list" [0 ])
def cons :Variant := Vec.mk "cons" [.some Ty.nat, .none]
def nil : Variant := Vec.mk "nil" []
def list : Adt := Vec.mk "list" [cons, nil]



instance: Repr Variant where
  reprPrec v _ := s!"#{v.tag} \{{ " ".intercalate $ v.toList.map (fun x => match x with | .none => "self" | .some t => "x")}}"

instance: Repr Adt where
  reprPrec a _ := s!"data {a.tag} \{{ " ".intercalate $ a.toList.map (fun v => (reprStr v))}}"



open Ty
-- def nat := Ty.nat
-- def string := Ty.string
-- -- def bool := Ty.bool
-- def arrow := Ty.arrow


def Vec.get : (n:Nat) -> (a:Adt) -> Option Variant
  | _, Vec.nil n => .none
  | 0, .cons x xs => .some x
  | n+1, .cons _ r => r.get n



structure Var (t: Ty) where
  name: String
deriving BEq, Hashable, Repr, DecidableEq

def Var.typed (t: Ty) (name: String) : Var t := ⟨name⟩


def Var.ty (v:Var t) := t
def newVar (name:String) : Var t := ⟨name⟩


structure TypedVar where
  t: Ty
  name: String

instance : BEq TypedVar where
  beq a b := a.name == b.name && a.t == b.t

def TypedVar.var (x:TypedVar) := @Var.mk x.t x.name

def TypedVar.from {t:Ty} (v: Var t) := TypedVar.mk t v.name



inductive UnOp : Ty -> Ty → Type
  | not : UnOp Ty.bool Ty.bool
  | as : (τ:Ty) → UnOp τ τ
  | lam : {τ₁ τ₂:Ty} → Var τ₁ → UnOp τ₂ (Ty.arrow τ₁ τ₂)

inductive BinOp : Ty → Ty → Ty → Type
  | add : BinOp Ty.nat Ty.nat Ty.nat
  | and : BinOp Ty.bool Ty.bool Ty.bool
  | less : BinOp Ty.nat Ty.nat Ty.bool
  | app : {τ₁ τ₂:Ty} → BinOp (Ty.arrow τ₁ τ₂) τ₁ τ₂
  | lett : {τ₁ τ₂:Ty} → Var τ₁ → BinOp τ₁ τ₂ τ₂

inductive Lit : Ty → Type
  | nat  : Nat  → Lit Ty.nat
  | bool : Bool → Lit Ty.bool



mutual

  inductive HExpr : Ty -> Type
    | lit : Lit x → HExpr x
    | var : Var u → HExpr u
    | un  : UnOp a b → HExpr a → HExpr b
    | bin : BinOp a b c → HExpr a → HExpr b → HExpr c
    | iff : HExpr Ty.bool → HExpr τ → HExpr τ → HExpr τ
    | data : (a:Adt) -> (n:Nat) -> Instance a (a.get n) -> HExpr (.adt a)
    | mmatch : (a:Adt) -> HExpr (.adt a) -> (shared : List TypedVar := []) -> (css: Match a (a.toList) res) -> HExpr res

  inductive Instance : Adt -> Option Variant -> Type
    | nil : (name:String) -> Instance a $ .some $ .nil name
    | cons : (v:HExpr $ vo.Ty a) -> Instance a (some xs) -> Instance a (some (.cons vo xs))

  inductive Match : Adt -> List Variant -> Ty -> Type
    | nil : Match a [] res
    | cons {v: Variant}: (c:MatchCase a v res) -> Match a xs res -> Match a (v::xs) res

  inductive MatchCase : (arg: Adt) -> (done: Variant) -> (res:Ty) -> Type
    | nil : (VName:String) -> HExpr res -> MatchCase arg (.nil VName) res
    | cons {df : DataField} : (v:Var (df.Ty arg)) -> MatchCase arg xs res -> MatchCase arg (Vec.cons df xs) res


end

open Ty

section HExpr_fields

  @[match_pattern] def HExpr.nat (n: Nat) := HExpr.lit (Lit.nat n)
  @[match_pattern] def HExpr.bool (b: Bool) := HExpr.lit (Lit.bool b)
  @[match_pattern] def HExpr.not (e: HExpr Ty.bool) := HExpr.un (UnOp.not) e
  @[match_pattern] def HExpr.as (τ: Ty) (e: HExpr τ) := HExpr.un (UnOp.as τ) e
  @[match_pattern] def HExpr.lam (v: Var τ₁) (e: HExpr τ₂) := HExpr.un (UnOp.lam v) e
  @[match_pattern] def HExpr.add (e₁ e₂: HExpr Ty.nat) := HExpr.bin (BinOp.add) e₁ e₂
  @[match_pattern] def HExpr.and (e₁ e₂: HExpr Ty.bool) := HExpr.bin (BinOp.and) e₁ e₂
  @[match_pattern] def HExpr.less (e₁ e₂: HExpr Ty.nat) := HExpr.bin (BinOp.less) e₁ e₂
  @[match_pattern] def HExpr.app (e₁: HExpr (Ty.arrow τ₁ τ₂)) (e₂: HExpr τ₁) := HExpr.bin (BinOp.app) e₁ e₂
  @[match_pattern] def HExpr.lett (v: Var τ₁) (e₁: HExpr τ₁) (e₂: HExpr τ₂) := HExpr.bin (BinOp.lett v) e₁ e₂


end HExpr_fields

def getTy  (_: HExpr u) : Ty := u


declare_syntax_cat high_lit
syntax num       : high_lit
syntax "true"    : high_lit
syntax "false"   : high_lit


def elabLit : Syntax → MetaM Expr
  | `(high_lit| $n:num) => mkAppM ``Lit.nat  #[mkNatLit n.getNat]
  | `(high_lit| true  ) => mkAppM ``Lit.bool #[.const ``Bool.true []]
  | `(high_lit| false ) => mkAppM ``Lit.bool #[.const ``Bool.false []]
  | _ => throwUnsupportedSyntax

declare_syntax_cat high_unop
syntax "not"     : high_unop

def elabUnOp : Syntax → MetaM Expr
  | `(high_unop| not) => return .const ``UnOp.not []
  | _ => throwUnsupportedSyntax

declare_syntax_cat high_binop
syntax "+"       : high_binop
syntax "and"     : high_binop
syntax "<"       : high_binop

def elabBinOp : Syntax → MetaM Expr
  | `(high_binop| +)   => return .const ``BinOp.add []
  | `(high_binop| and) => return .const ``BinOp.and []
  | `(high_binop| <)   => return .const ``BinOp.less []
  | _ => throwUnsupportedSyntax

declare_syntax_cat                                high_expr
syntax high_lit                                 : high_expr
syntax ident                                    : high_expr
syntax high_unop high_expr                      : high_expr
syntax high_expr high_binop high_expr           : high_expr
syntax "let" ident "=" high_expr "in" high_expr : high_expr
syntax "(" high_expr ")"                        : high_expr


declare_syntax_cat high_data
declare_syntax_cat high_data_variant
syntax "#" ident "{" term,* "}" : high_data_variant
syntax "data" ident "{" high_data_variant,* "}" : high_data

syntax high_data high_expr                      : high_expr

partial def elabDataVariantTerm : Syntax -> TermElabM Expr
  | `(high_data_variant| #$name:ident { $fields: term,*}) => do
    return ← mkAppM ``Vec.mk #[
      mkStrLit name.getId.toString,
      ← mkListLit (mkConst ``DataField []) $
        ← fields.getElems.toList.mapM (fun (f : TSyntax `term) => do
          let x ← Term.elabTerm f none
          let x : Expr ← mkAppM ``some #[ x ]
          return x
    )]

  | _ => throwUnsupportedSyntax

elab "test_elabDataVariant " v:high_data_variant : term => elabDataVariantTerm v


#check test_elabDataVariant #cons { nat, nat}


partial def elabDataTerm : Syntax -> TermElabM (Name × Expr)
  | `(high_data| data $name:ident { $vars:high_data_variant,* } ) => do
    let val ← (mkAppM ``Vec.mk #[
      mkStrLit name.getId.toString,
      ← mkListLit (mkConst ``Variant []) $
        ← vars.getElems.toList.mapM (fun (v:TSyntax `high_data_variant) => do return ← elabDataVariantTerm v)])
    return .mk name.getId val
  | _ => throwUnsupportedSyntax

elab "test_elabData" v:high_data : term => elabDataTerm v

#check test_elabData data list {#nil{}, #cons{nat, nat}}

declare_syntax_cat high_instance



-- syntax "#"
declare_syntax_cat high_match





partial def elabExpr : Syntax → TermElabM Expr
  | `(high_expr| $l:high_lit) => do
    let l ← elabLit l
    mkAppM ``HExpr.lit #[l]

  | `(high_expr| ($op:high_unop $e:high_expr)) => do
    let op ← elabUnOp op
    let e ← elabExpr e
    mkAppM ``HExpr.un #[op, e]

  | `(high_expr| $e₁:high_expr $op:high_binop $e₂:high_expr) => do
    let op ← elabBinOp op
    let e₁ ← elabExpr e₁
    let e₂ ← elabExpr e₂
    mkAppM ``HExpr.bin #[op, e₁, e₂]

  | `(high_expr| let $i:ident = $e₁:high_expr in $e₂:high_expr) => do
    let e₁ ← elabExpr e₁
    -- let τ ← mkAppM ``getTy #[e₁] >>= reduce
    let τ ← mkAppM ``getTy #[e₁]
    let τ ← reduce τ
    withLocalDecl i.getId BinderInfo.default τ (fun _ => do
      -- let q ← Term.elabTerm sorry none
      let e₂ ← elabExpr e₂
      let var ← mkAppM ``Var.typed #[τ, mkStrLit i.getId.toString]
      mkAppM ``HExpr.lett #[var, e₁, e₂]
    )
  | `(high_expr| $x:ident ) => do
    let lctx ←  getLCtx ;
    let some locl ← pure <| lctx.findFromUserName? x.getId
      | throwError "Variable {x.getId} not found in local context"
    let fvar := mkFVar locl.fvarId
    let τ ← inferType fvar
    let var ← mkAppM ``Var.typed #[τ, mkStrLit x.getId.toString]
    mkAppM ``HExpr.var #[var]

  | `(high_expr| $dat:high_data $rest:high_expr ) => do
    let dat ← elabDataTerm dat
    let rest ← elabExpr rest
    sorry

  | `(high_expr| ($e:high_expr)) => do elabExpr e


  | _ => throwUnsupportedSyntax

elab "test_elabExpr " e:high_expr : term => elabExpr e

#reduce HExpr.lett (Var.mk "a") (HExpr.lit $ Lit.nat 2) (HExpr.lit $ Lit.nat 3)

#reduce test_elabExpr let a = 2 in 2

#check test_elabExpr let a = 2 in let a = true in a

#check test_elabExpr let a = 2 in a
