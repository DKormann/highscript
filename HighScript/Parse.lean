-- parsing and compiling of AST (compilation needed for display)

import Lean
open  Lean.Meta Lean.Macro Lean.Elab


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

open Ty


instance: Repr Ty where
  reprPrec x _ :=
    match x with
    | Ty.bool => "bool"
    | nat => "nat"
    | string => "string"
    | arrow a b  => s!"{reprStr a} -> {reprStr b}"
    | adt v  => v.tag



abbrev DataField := Option Ty
abbrev Variant := Vec String DataField
abbrev Adt := Vec String Variant


def DataField.Ty : (self: DataField) -> (adt: Adt) -> Ty
  | none, a => .adt a
  | some t, _ => t

instance : Repr DataField where
  reprPrec df _ := match df with
    | none => "self"
    | some t => reprStr t

def v     := (Vec.mk "list" [0 ])
def cons  :Variant := Vec.mk "cons" [.some Ty.nat, .none]
def nil   : Variant := Vec.mk "nil" []
def list  : Adt := Vec.mk "list" [cons, nil]



instance: Repr Variant where
  reprPrec v _ := s!"#{v.tag} \{{ " ".intercalate $ v.toList.map (fun x => reprStr x)}}"


instance: Repr Adt where
  reprPrec a _ := s!"data {a.tag} \{{ " ".intercalate $ a.toList.map (fun v => (reprStr v))}}"

#eval list



def Vec.get : (n:Nat) -> (a:Adt) -> Option Variant
  | _, Vec.nil _ => .none
  | 0, .cons x _ => .some x
  | n+1, .cons _ r => r.get n



structure Var (t: Ty) where
  name: String
deriving BEq, Hashable, Repr, DecidableEq

def Var.typed (t: Ty) (name: String) : Var t := ⟨name⟩


def Var.ty (_:Var t) := t
def newVar (name:String) : Var t := ⟨name⟩


structure TypedVar where
  t: Ty
  name: String
deriving Repr


instance : BEq TypedVar where
  beq a b := a.name == b.name && a.t == b.t

def TypedVar.var (x:TypedVar) := @Var.mk x.t x.name

def TypedVar.from {t:Ty} (v: Var t) := TypedVar.mk t v.name

inductive Lit : Ty → Type
  | nat  : Nat  → Lit Ty.nat
  | bool : Bool → Lit Ty.bool
deriving Repr

inductive UnOp : Ty -> Ty → Type
  | not : UnOp Ty.bool Ty.bool
  | as : (τ:Ty) → UnOp τ τ
  | lam : {τ₁ τ₂:Ty} → Var τ₁ → UnOp τ₂ (Ty.arrow τ₁ τ₂)
deriving Repr

inductive BinOp : Ty → Ty → Ty → Type
  | add : BinOp Ty.nat Ty.nat Ty.nat
  | and : BinOp Ty.bool Ty.bool Ty.bool
  | less : BinOp Ty.nat Ty.nat Ty.bool
  | app : {τ₁ τ₂:Ty} → BinOp (Ty.arrow τ₁ τ₂) τ₁ τ₂
  | lett : {τ₁ τ₂:Ty} → Var τ₁ → BinOp τ₁ τ₂ τ₂
deriving Repr



mutual

  inductive Expr : Ty -> Type
    | lit : Lit x → Expr x
    | var : Var u → Expr u
    | un  : UnOp a b → Expr a → Expr b
    | bin : BinOp a b c → Expr a → Expr b → Expr c
    | iff : Expr Ty.bool → Expr τ → Expr τ → Expr τ
    | data : (a:Adt) -> (n:Nat) -> Instance a (a.get n) -> Expr (.adt a)
    | mmatch : (a:Adt) -> Expr (.adt a) -> (shared : List TypedVar := []) -> (css: Match a (a.toList) res) -> Expr res
  deriving Repr

  inductive Instance : Adt -> Option Variant -> Type
    | nil : (name:String) -> Instance a $ .some $ .nil name
    | cons : (v:Expr $ vo.Ty a) -> Instance a (some xs) -> Instance a (some (.cons vo xs))
  deriving Repr

  inductive Match : Adt -> List Variant -> Ty -> Type
    | nil : Match a [] res
    | cons {v: Variant}: (c:MatchCase a v res) -> Match a xs res -> Match a (v::xs) res
  deriving Repr

  inductive MatchCase : (arg: Adt) -> (done: Variant) -> (res:Ty) -> Type
    | nil : (VName:String) -> Expr res -> MatchCase arg (.nil VName) res
    | cons {df : DataField} : (v:Var (df.Ty arg)) -> MatchCase arg xs res -> MatchCase arg (Vec.cons df xs) res

end


open Ty

section HExpr_fields

  @[match_pattern] def Expr.nat (n: Nat) := Expr.lit (Lit.nat n)
  @[match_pattern] def Expr.bool (b: Bool) := Expr.lit (Lit.bool b)
  @[match_pattern] def Expr.not (e: Expr Ty.bool) := Expr.un (UnOp.not) e
  @[match_pattern] def Expr.as (τ: Ty) (e: Expr τ) := Expr.un (UnOp.as τ) e
  @[match_pattern] def Expr.lam (v: Var τ₁) (e: Expr τ₂) := Expr.un (UnOp.lam v) e
  @[match_pattern] def Expr.add (e₁ e₂: Expr Ty.nat) := Expr.bin (BinOp.add) e₁ e₂
  @[match_pattern] def Expr.and (e₁ e₂: Expr Ty.bool) := Expr.bin (BinOp.and) e₁ e₂
  @[match_pattern] def Expr.less (e₁ e₂: Expr Ty.nat) := Expr.bin (BinOp.less) e₁ e₂
  @[match_pattern] def Expr.app (e₁: Expr (Ty.arrow τ₁ τ₂)) (e₂: Expr τ₁) := Expr.bin (BinOp.app) e₁ e₂
  @[match_pattern] def Expr.lett (v: Var τ₁) (e₁: Expr τ₁) (e₂: Expr τ₂) := Expr.bin (BinOp.lett v) e₁ e₂


end HExpr_fields

def getTy  (_: Expr u) : Ty := u


declare_syntax_cat high_lit
syntax num       : high_lit
syntax "true"    : high_lit
syntax "false"   : high_lit

def _Expr := Lean.Expr


def elabLit : Lean.Syntax → MetaM _Expr
  | `(high_lit| $n:num) => mkAppM ``Lit.nat  #[Lean.mkNatLit n.getNat]
  | `(high_lit| true  ) => mkAppM ``Lit.bool #[.const ``Bool.true []]
  | `(high_lit| false ) => mkAppM ``Lit.bool #[.const ``Bool.false []]
  | _ => throwUnsupportedSyntax



declare_syntax_cat high_unop
syntax "not"     : high_unop

def elabUnOp : Lean.Syntax → MetaM _Expr
  | `(high_unop| not) => return .const ``UnOp.not []
  | _ => throwUnsupportedSyntax

declare_syntax_cat high_binop
syntax "+"       : high_binop
syntax "and"     : high_binop
syntax "<"       : high_binop

def elabBinOp : Lean.Syntax → MetaM _Expr
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





-- declare_syntax_cat high_data_variant
-- syntax "#" ident "{" term,* "}" : high_data_variant


declare_syntax_cat typed_var
syntax ident ":" ident : typed_var

declare_syntax_cat construction
syntax " #" ident typed_var* : construction
syntax " #" ident : construction

macro "foreach" terms:ident* "end" :term => do
  let arr := terms.toList.toArray
  return ← `([$[$arr],*])


declare_syntax_cat high_data
syntax "data" ident ident* "{" construction* "}" : high_data

syntax high_data high_expr : high_expr

syntax "unquote" term: high_expr

syntax "test_macroData" high_data high_expr : term


partial def elabExpr : Lean.Syntax → TermElabM _Expr

  | `(high_expr| unquote $x:term) => Term.elabTerm x none

  | `(high_expr| $dat:high_data $rest:high_expr ) => do
    let dat := Term.elabTerm (← `( test_macroData $dat $rest)) none
    dat
  | `(high_expr| $l:high_lit) => do
    let l ← elabLit l
    mkAppM ``Expr.lit #[l]

  | `(high_expr| ($op:high_unop $e:high_expr)) => do
    let op ← elabUnOp op
    let e ← elabExpr e
    mkAppM ``Expr.un #[op, e]

  | `(high_expr| $e₁:high_expr $op:high_binop $e₂:high_expr) => do
    let op ← elabBinOp op
    let e₁ ← elabExpr e₁
    let e₂ ← elabExpr e₂
    mkAppM ``Expr.bin #[op, e₁, e₂]

  | `(high_expr| let $i:ident = $e₁:high_expr in $e₂:high_expr) => do
    let e₁ ← elabExpr e₁
    let τ ← mkAppM ``getTy #[e₁]
    let τ ← reduce τ
    withLocalDecl i.getId Lean.BinderInfo.default τ (fun _ => do
      let e₂ ← elabExpr e₂
      let var ← mkAppM ``Var.typed #[τ, Lean.mkStrLit i.getId.toString]
      mkAppM ``Expr.lett #[var, e₁, e₂]
    )
  | `(high_expr| $x:ident ) => do
    let lctx ←  Lean.getLCtx ;
    let some locl ← pure <| lctx.findFromUserName? x.getId
      | throwError "Variable {x.getId} not found in local context"
    let fvar := Lean.mkFVar locl.fvarId
    let τ ← inferType fvar
    let var ← mkAppM ``Var.typed #[τ, Lean.mkStrLit x.getId.toString]
    mkAppM ``Expr.var #[var]

  | `(high_expr| ($e:high_expr)) => do elabExpr e

  | _ => throwUnsupportedSyntax

def nt := Ty.nat
def n22 := Expr.nat 22

elab "test_elabExpr " e:high_expr : term => elabExpr e


-- macro "test_macroData" dat:high_data rest:high_expr : term => do
macro_rules
  | `(test_macroData $dat:high_data $rest:high_expr) =>
    match dat with
    -- |`(high_data| data $name:ident $targs:ident* { $arms:construction*} ) => do
    |`(high_data| data $name:ident $targs:ident* { $arms:construction*} ) => do

      let mut ctrsdata := #[]
      for ctr in arms do
        match ctr with
          | `(construction| #$ctrname $args*) =>
            let mut arglist := #[]
            for arg in args do
              match arg with
              | `(typed_var| $arg:ident : $ty:ident) => arglist := arglist.push (arg, ty)
              | _ => Lean.Macro.throwUnsupported
            ctrsdata := ctrsdata.push (ctrname, arglist)
          | `(construction | #$ctrname) => ctrsdata := ctrsdata.push (ctrname, #[])
          | _ => Lean.Macro.throwUnsupported

      ctrsdata := ctrsdata.insertionSort (fun (a, _) (b, _) => a.getId.toString < b.getId.toString)

      let ctrsTy : Array $ Lean.TSyntax `term ← ctrsdata.mapM (fun x => do
        let dfields ←  x.snd.mapM (fun f => if f.snd.getId.toString == "self" then `(none) else `(some $f.snd))
        let t : Lean.TSyntax `term ← `(Vec.mk $(Lean.quote x.fst.getId.toString) [$[$dfields],*] );
        return t
      )

      let fulladt:=
       ← targs.foldlM (fun (a c) => `( $a $c ))
        (← `(adt))
      let tyFn:=
      --  ← targs.foldrM (fun (c a) => `(fun ($c :Ty) => $a ))
        (← `(Ty.adt $fulladt))

      let mut adtFn :=
      ← targs.foldlM
        (fun (a c) => `(fun ($a :Ty) => $c))
        (← `(Vec.mk $(Lean.quote name.getId.toString) [$[$ctrsTy],*]))


      let mut res ← `( test_elabExpr $rest)


      for ( (ctag, cargs) , n) in ctrsdata.zipIdx do
        let fulladt ← targs.foldlM (fun (a c) => `( $a $c )) (← `(adt))
        -- let fulladt := ← `(adt)
        -- let fullTy ← targs.foldlM (fun (a c) => `( $a $c )) (← `($name))
        let fullTy := name

        let inst ← cargs.foldrM (fun (c a) => `(Instance.cons $c.fst $a) ) (← `(Instance.nil $(Lean.quote ctag.getId.toString)))
        let mut ctrFn ← `(
          let adt := $fulladt;
          let inst : Instance adt (adt.get $(Lean.Syntax.mkNatLit n)) := $inst;
          let ctr : Expr $fullTy := Expr.data adt $(Lean.Syntax.mkNatLit n) inst;
          ctr
        );

        for arg in cargs.reverse do ctrFn ← `(fun ($arg.fst : Expr $(← if arg.snd.getId.toString == "self" then `($fullTy) else `($arg.snd)) ) => $ctrFn)
        -- for arg in targs.reverse do ctrFn ← `(fun {$arg :Ty} => $ctrFn)

        res ← `( let $ctag := $ctrFn; $res)

      res ← `(
        let targs := [$[$targs],*];
        let adt := $adtFn;
        let $name := $tyFn;
        $res)

      return res

    | _ => Lean.Macro.throwUnsupported


def t := 11
def u := 22

#check test_elabExpr 22
#check test_macroData data list {#nil a:nat} 22

#check test_macroData data list t {#nil} 22


#check test_macroData data list t u {#nil} 22

#check test_elabExpr data list t u {#cons a:nat b:bool}  22



#check
  test_elabExpr data list t { #cons h:t tail:self #nil }
  unquote ( cons )

-- #eval test_elabExpr macroinvoke 45

-- -- #reduce test_elabExpr data list { #nil{} } 22

-- #reduce Expr.lett (Var.mk "a") (Expr.lit $ Lit.nat 2) (Expr.lit $ Lit.nat 3)

-- #reduce test_elabExpr let a = 2 in 2

-- #check test_elabExpr let a = 2 in let a = true in a

-- #eval test_elabExpr let a = 2 in a
