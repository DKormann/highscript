import Std.Data.HashMap
set_option linter.unusedVariables false

inductive Vec {a: Type} : (n: Nat) -> Type
  | nil: Vec 0
  | cons: a -> @Vec a s -> (@Vec a $ s + 1)


universe u

-- data field T is target R recursive field
inductive Tvar : Type
  | T: Tvar
  | R: Tvar

abbrev TT := Tvar.T
abbrev RR := Tvar.R
def Tvar.choose {a} (t:a) (r:a) : Tvar → a | Tvar.T => t | Tvar.R => r

abbrev Variant := String × List (Tvar)


structure Adt where
  name: String
  Variants : List Variant



inductive Ty
  | int
  | string
  | arrow: Ty -> Ty -> Ty
  | data : (a: Adt) → Ty → Ty


open Ty

infixl:56 "->" => arrow
macro:100 adt:term:100 " [" t:term:100 "]" : term => `(data $adt $t)

inductive Var :(t: Ty) -> Type | mk : (t:Ty) -> (name: String) -> Var t
deriving BEq, Hashable


def Var.name :(Var t) -> String | mk t n => n
def newVar (name:String) : Var ty := Var.mk ty name
def Var.ty : (v:Var t) -> Ty | mk t n => t
def Var.eq (v:Var t) (o:Var s) : Bool := v.name == o.name-- && v.num == o.num


def Var.toTypedVar (v:Var t) : TypedVar := ⟨v.name, v.ty⟩


-- def Var.dup (v:Var t) : Var t × Var t := (⟨v.name++"1"⟩, ⟨v.name ++ "2"⟩)

instance : Repr (Var t) where reprPrec v _ := s!"{v.name}"


-- inductive UnaryOp : Ty -> Ty -> Type
  -- | lam

mutual

  inductive NullaryOp : Ty -> Type
    | intlit : Nat -> NullaryOp int
    | stringlit : String -> NullaryOp string
    | var : Var t -> NullaryOp t
    | ftag : String -> (s:Ty) -> NullaryOp s

  inductive UnaryOp : Ty -> Ty -> Type
    | lam : (Var a) -> UnaryOp t (arrow a t)
    | fn : String  -> UnaryOp t t
    | as : (t:Ty) -> UnaryOp t t

  inductive BinaryOp : Ty -> Ty -> Ty -> Type
    | arith : String -> BinaryOp int int int
    | app : BinaryOp (arrow a b) a b
    | sup : Nat -> BinaryOp t t t
    | nsup : BinaryOp t t t
    | dub : Nat -> (Var u) -> (Var u) -> BinaryOp u t t

  inductive Expr : Ty → Type
    | nullary : NullaryOp b -> Expr b
    | unary : UnaryOp a b -> Expr a -> Expr b
    | binary : BinaryOp a b c -> Expr a -> Expr b -> Expr c
    | data : (adt: Adt) -> {t: Ty} -> (n:Fin a.Variants.length) -> (v: Instance a t (a.Variants[n].snd)) → Expr (adt[t])
    -- | matcher : (x: Expr (a[t])) -> (Match a a.Variants t res) -> Expr res

  inductive Instance : (a: Adt) -> (t:Ty) -> (v: List Tvar) -> Type
    | nil : Instance a t []
    -- | T : (t:Ty) -> (x: Expr t) -> (rest: Instance a t xs) -> Instance a t (Tvar.T::xs)
    -- | R : (t:Ty) -> (x: (Expr $ a[t])) -> (rest: Instance a t xs) -> Instance a t (Tvar.R::xs)
    | cons : (tv: Tvar) -> (x: Expr (tv.choose t (a [t]))) -> (Instance a t xs) -> Instance a t (tv::xs)

  -- inductive MatchCase : (r:Ty) -> (t:Ty) -> (v: List Tvar) -> (res: Ty) -> Type
  --   | nil : (e:Expr res) -> MatchCase r t [] res
  --   | T : (x: Var t) -> (rest: MatchCase r t xs res) -> MatchCase r t (Tvar.T::xs) res
  --   | R : (x: (Var r)) -> (rest: MatchCase r t xs res) -> MatchCase r t (Tvar.R::xs) res

  -- inductive Match : (a:Adt) -> (vs:List Variant) -> (t:Ty) -> (res:Ty) -> Type
  --   | nil : Match a [] t res
  --   | cons : (x: MatchCase (a[t]) t v.snd res) -> (Match a xs t res) → Match a (v::xs) t res

end

@[match_pattern] def Expr.var (vr:Var t) := Expr.nullary (NullaryOp.var vr)
@[match_pattern] def Expr.lam (vr: Var a) (e:Expr b) := Expr.unary (UnaryOp.lam vr) e
@[match_pattern] def Expr.dub n (a b: Var t) e (res:Expr u) := Expr.binary (.dub n a b ) e res

class ReplaceVar (a:Type) where replace : (v v':String) -> a -> a


abbrev EXXL (t:Ty): Type := (Expr t) × List String
abbrev to_dub := List String

mutual

  instance : ReplaceVar (Expr b) where replace :(v v':String) -> (e:Expr b) -> Expr b := Expr.replace

  def Expr.replace (v v':String): (e:Expr b) -> Expr b
    | .var vr => .var (if vr.name == v then newVar v' else vr)
    | .lam a e => .lam a (if a.name == v then e else e.replace v v')
    | .unary op e => .unary op (e.replace v v')
    | .binary op a b => .binary op (a.replace v v') (b.replace v v')
    | .data adt n i => .data adt n $ i.replace v v'
    | k => k

  def Instance.replace (v v':String): (i:Instance a t vs) -> Instance a t vs
    | .nil => Instance.nil
    | .cons tv x rest => .cons tv (x.replace v v') (rest.replace v v')


  def Expr.resolve  {s} (c: List TypedVar) (a: Expr ta) (b: Expr tb) (fn :Expr ta -> Expr tb -> Expr s) : Expr s :=
    match c with
    | [] => fn a b
    | c::cs =>
      let (c', c'') := (c.name ++ "1", c.name ++ "2")
      Expr.dub 0 (newVar c') (newVar c'') (Expr.var $ Var.mk c.ty c.name)
      $ .resolve cs (a.replace c.name c') (b.replace c.name c'') fn


  def Expr.linearize : (e:Expr b) -> Expr b × List TypedVar

    | .var vr => .mk (.var vr) [vr.toTypedVar]
    | .lam vr a =>
      let a := a.linearize
      .mk (.lam vr (a.1)) (a.2.filter ((.).name ≠ vr.name))
    | .unary op a =>
      let a := a.linearize
      .mk (.unary op a.1) a.2
    | .binary op a b =>
      let (a, as) := a.linearize
      let as := match op with
        | .dub n a b => as.filter (. ∉ [a.name, b.name])
        | _ => as
      let b := b.linearize
      let fn := fun a b => Expr.binary op a b
      .mk (.resolve (as.filter (. ∈ b.2)) a b.1 fn) $ b.2 ++ as.filter (. ∉ b.2)
    | .data adt n i =>
      let (i, xs, rtd) := i.linearize
      (rtd.foldl (fun x c =>
      (Expr.dub 0
        (newVar (c ++ "1") : Var int)
        (newVar (c ++ "2")) (.var $ newVar c) x ))
        (Expr.data adt n i)
      , xs)
    | k => .mk k []

  def Instance.linearize : (i:Instance a t vs) -> Instance a t vs × List String × to_dub
    | .nil => (.nil, .nil, .nil)
    | .cons tv x rest =>
      let (x, xs) := x.linearize
      let (r, rs, rtd) := rest.linearize
      let collisions := xs.filter (. ∈ rs)
      let alls := rs ++ xs.filter (. ∉ rs)
      let (x,r) := collisions.foldl (λ (x,r) c =>
        (x.replace c $ c ++ "1", r.replace c $ c ++ "2")) (x,r)
      (.cons tv x r, alls, rtd ++ collisions.filter (. ∉ rtd))

end

mutual
def Expr.compile : (e:Expr t) -> String
  | .nullary $ NullaryOp.intlit n => s!"{n}"
  | .nullary $ NullaryOp.stringlit s => s!"\"{s}\""
  | .nullary $ NullaryOp.var v => s!"{v.name}"
  | .nullary $ NullaryOp.ftag s t => s!"@{s}"
  | .unary (UnaryOp.lam v) e => s!"λ {v.name} {e.compile}"
  | .unary (UnaryOp.fn n) e => s!"@{n} {e.compile}"
  | .unary (UnaryOp.as t) e => s!"{e.compile}"
  | .binary op a b => match op with
    | .arith op => s!"{a.compile} {op} {b.compile}"
    | .app => s!"({a.compile} {b.compile})"
    | .sup n => s!"&{n}\{{a.compile} {b.compile}}"
    | .nsup => s!"&\{{a.compile} {b.compile}}"
    | .dub n x y => s!"{a.compile} {b.compile}"

  | .data adt n i =>
        let constructorName := (adt.Variants[n]).1
        let instanceArgsCompiled := Instance.compile i
        if instanceArgsCompiled.isEmpty then
          s!"{constructorName}"
        else
          s!"{constructorName} {instanceArgsCompiled}"

  def Instance.compile : (i:Instance adt t vs) -> String
    | .nil => ""
    | .cons tv x rest =>
        let xCompiled := Expr.compile x
        let restCompiled := Instance.compile rest
        if restCompiled.isEmpty then
          xCompiled
        else
          s!"{xCompiled} {restCompiled}"





end

def Expr.collect (m: Std.HashMap String String) : (e:Expr t) -> (Std.HashMap String String)
  | .unary (UnaryOp.fn n) e =>
    let m := e.collect m
    let n := "@" ++ n
    if m.contains n then m else m.insert n $ n ++ " = " ++ e.compile
  | .data a _ _ =>
    let show_vari := fun (v:Variant) => s!"#{v.fst}\{{ " ".intercalate $ v.snd.map (fun t => (t.choose "x" "rec"))}}"
    m.insert a.name $ s!"data {a.name} \{{" ".intercalate $ (a.Variants.map show_vari) }}"
  | .unary op e => e.collect m
  | k => m
