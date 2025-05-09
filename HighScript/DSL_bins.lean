import Std.Data.HashMap
set_option linter.unusedVariables false

inductive DataField : Type
  | T: DataField
  | R: DataField
deriving BEq, Hashable

abbrev TT := DataField.T
abbrev RR := DataField.R
def DataField.choose {a} (t:a) (r:a) : DataField → a | DataField.T => t | DataField.R => r

abbrev Variant := String × List (DataField)

structure Adt where
  name: String
  Variants : List Variant
deriving BEq, Hashable


inductive Ty
  | int
  | string
  | arrow: Ty -> Ty -> Ty
  | data : (a: Adt) → Ty → Ty
deriving BEq, Hashable

open Ty

infixl:56 "->" => arrow
macro:100 adt:term:100 " [" t:term:100 "]" : term => `(data $adt $t)

inductive Var :(t: Ty) -> Type | mk : (t:Ty) -> (name: String) -> Var t
deriving BEq, Hashable


def Var.name :(Var t) -> String | mk t n => n
def newVar (name:String) : Var ty := Var.mk ty name
def Var.ty : (v:Var t) -> Ty | mk t n => t
def Var.eq (v:Var t) (o:Var s) : Bool := v.name == o.name-- && v.num == o.num

inductive TypedVar | mk : {ty:Ty}-> (Var ty)-> TypedVar
deriving Hashable

def TypedVar.v (v:TypedVar) := match v with | TypedVar.mk v => (v.ty, v.name)
def TypedVar.var (v:TypedVar) : Var v.v.fst := Var.mk v.v.1 v.v.2
def TypedVar.name x := (TypedVar.v x ).2
def TypedVar.ty x := (TypedVar.v x ).1

instance : BEq TypedVar where beq (a b: TypedVar) := a.name == b.name
def Var.toTypedVar (v:Var t) : TypedVar := ⟨v⟩

instance : Repr (Var t) where reprPrec v _ := s!"{v.name}"

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
    | data : (adt: Adt) -> {t: Ty} -> (n:Fin adt.Variants.length) -> (v: Instance a t (adt.Variants[n].snd)) → Expr (adt[t])
    | mmatch : (x: Expr (a[t])) -> (Match a t a.Variants res) -> Expr res

  inductive Instance : (a: Adt) -> (t:Ty) -> (v: List DataField) -> Type
    | nil : Instance a t []
    | cons : (tv: DataField) -> (x: Expr (tv.choose t (a [t]))) -> (Instance a t xs) -> Instance a t (tv::xs)

  inductive MatchCase : (r:Ty) -> (t:Ty) -> (v: List DataField) -> (res: Ty) -> Type
    | nil : (e:Expr res) -> MatchCase r t [] res
    -- | T : (x: Var t) -> (rest: MatchCase r t xs res) -> MatchCase r t (DataField.T::xs) res
    -- | R : (x: (Var r)) -> (rest: MatchCase r t xs res) -> MatchCase r t (DataField.R::xs) res
    | cons : (tv: DataField) -> (vr: Var (tv.choose t r)) -> MatchCase r t vs res -> MatchCase r t (tv::vs) res

  inductive Match : (a:Adt) -> (t:Ty) -> (vs:List Variant) -> (res:Ty) -> Type
    | nil : Match a t [] res
    | cons : (x: MatchCase (a[t]) t v.snd res) -> (Match a t xs res) → Match a t (v::xs) res

end

@[match_pattern] def Expr.var (vr:Var t) := Expr.nullary (NullaryOp.var vr)
@[match_pattern] def Expr.lam (vr: Var a) (e:Expr b) := Expr.unary (UnaryOp.lam vr) e
@[match_pattern] def Expr.dub n (a b: Var t) e (res:Expr u) := Expr.binary (.dub n a b ) e res

mutual

  def Expr.replace (v v':String): (e:Expr b) -> Expr b
    | .var vr => .var (if vr.name == v then newVar v' else vr)
    | .lam a e => .lam a (if a.name == v then e else e.replace v v')
    | .unary op e => .unary op (e.replace v v')
    | .binary op a b => .binary op (a.replace v v') (b.replace v v')
    | .data adt n i => .data adt n $ i.replace v v'
    | .mmatch x m => .mmatch (x.replace v v') m
    | k => k

  def Instance.replace (v v':String): (i:Instance a t vs) -> Instance a t vs
    | .nil => Instance.nil
    | .cons tv x rest => .cons tv (x.replace v v') (rest.replace v v')

  def MatchCase.replace (v v': String) : (mc:MatchCase r t vs res) -> MatchCase r t vs res
    | .nil e => .nil e
    | .cons tv vr rest => .cons tv vr ( if vr.name == v then rest else rest.replace v v')

  def Match.replace(v v':String) : (m: Match a t vs res) -> Match a t vs res
    | .nil => .nil
    | .cons x m => .cons (x.replace v v') (m.replace v v')

  def Expr.resolve  {s} (c: List TypedVar) (a: Expr ta) (b: Expr tb) (fn :Expr ta -> Expr tb -> Expr s) : Expr s :=
    match c with
    | [] => fn a b
    | c::cs =>
      let (c', c'') := (c.v.2 ++ "1", c.v.2 ++ "2")
      Expr.dub 0 (newVar c') (newVar c'') (Expr.var $ Var.mk c.v.1 c.v.2)
      $ .resolve cs (a.replace c.v.2 c') (b.replace c.v.2 c'') fn


  def Expr.linearize : (e:Expr b) -> Expr b × List TypedVar

    | .var vr => .mk (.var vr) [vr.toTypedVar]
    | .lam vr a =>
      let (a,as) := a.linearize
      .mk (.lam vr a) (as.filter (. != (vr.toTypedVar)))
    | .unary op a =>
      let a := a.linearize
      .mk (.unary op a.1) a.2
    | .binary op a b =>
      let (a, as) := a.linearize
      let as : List TypedVar := match op with
        | .dub n a b => as.filter (fun x => x != a.toTypedVar ∧ x != b.toTypedVar)
        | _ => as
      let b := b.linearize
      let fn := fun a b => Expr.binary op a b
      .mk (.resolve (as.filter (b.2.contains .)) a b.1 fn) $ b.2 ++ as.filter (! b.2.contains .)
    | .data adt n i =>
      let (i, xs, rtd) := i.linearize
      (rtd.foldl (fun (x) (c:TypedVar) =>
      (Expr.dub 0
        (newVar (c.v.2 ++ "1"))
        (newVar (c.v.2 ++ "2")) (.var $ c.var) x ))
        (Expr.data adt n i)
      , xs)
    | .mmatch x m =>
      let (x, xs) := x.linearize
      let (m, rs, os) := m.linearize
      let collisions := xs.filter (rs.contains)
      let (x, m) := collisions.foldl (λ (x, m) c =>
        (x.replace c.name $ c.name ++ "1", m.replace c.name $ c.name ++ "2")) (x, m)
      let ex := (collisions ++ os).foldl (λ x c =>
        Expr.dub 0
          (newVar (c.v.2 ++ "1"))
          (newVar (c.v.2 ++ "2")) (.var $ c.var) x) $ Expr.mmatch x m
      (ex, xs ++ rs.filter (! xs.contains .))
    | k => .mk k []

  def MatchCase.linearize : (m:MatchCase r t vs res) -> MatchCase r t vs res × List TypedVar
    | .nil e =>
      let (e, es) := e.linearize
      (.nil e, es)
    | .cons tv vr rest =>
      let (rest, xs) := rest.linearize
      let xs := xs.filter (. != (vr.toTypedVar))
      (.cons tv vr rest, xs)

  def Match.linearize : (m:Match a t vs res) -> Match a t vs res × List TypedVar × List TypedVar
    | .nil => (.nil, [], [])
    | .cons x rest =>
      let (x, xs) := x.linearize
      let (rest, rs, os) := rest.linearize
      let collisions := xs.filter (rs.contains)
      let (x, rest) := collisions.foldl (λ (x, r) c => (x.replace c.name $ c.name ++ "1", r.replace c.name $ c.name ++ "2")) (x,rest)
      (.cons x rest, xs ++ rs.filter (! xs.contains .), collisions)

  def Instance.linearize : (i:Instance a t vs) -> Instance a t vs × List TypedVar × List TypedVar
    | .nil => (.nil, .nil, .nil)
    | .cons tv x rest =>
      let (x, xs) := x.linearize
      let (r, rs, rtd) := rest.linearize
      let collisions := xs.filter (rs.contains)
      let alls := rs ++ xs.filter (! rs.contains .)
      let (x,r) := collisions.foldl (λ (x,r) c =>
        (x.replace c.name $ c.name ++ "1", r.replace c.name $ c.name ++ "2")) (x,r)
      (.cons tv x r, alls, rtd ++ collisions.filter (! rtd.contains .))

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
  | .data adt n i => s!"#{(adt.Variants[n]).1} \{{ i.compile }}"
  | .mmatch x m => s!"~{x.compile} \{{m.compile}}"

  def MatchCase.compile : MatchCase r t vs rest -> String
    | .nil e => ": " ++ e.compile
    | .cons df vr rest => vr.name ++ ", " ++ rest.compile

  def Match.compile : Match a t vs rest -> String
    | .nil => ""
    | .cons m rest => s!"\{{m.compile}} {rest.compile}"

  def Instance.compile : (i:Instance adt t vs) -> String
    | .nil => ""
    | .cons tv x rest => s!"{x.compile}, {rest.compile}"

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
