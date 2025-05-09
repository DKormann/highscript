

import Lean
import Std.Data.HashMap

set_option linter.unusedVariables false

inductive Tvar where
  | Rec : Tvar
  | T : Tvar
deriving DecidableEq


abbrev TT := Tvar.T
abbrev RR := Tvar.Rec
abbrev Tvar.choose {a} (t:a) (r:a) : Tvar → a | Tvar.T => t | Tvar.Rec => r


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

structure Var (t: Ty) where name: String


def newVar (s:String) : Var t := { name := s}
def Var.eq (v:Var t) (o:Var s) : Bool := v.name == o.name-- && v.num == o.num
def Var.dup (v:Var t) : Var t × Var t := (⟨v.name++"1"⟩, ⟨v.name ++ "2"⟩)

instance : Repr (Var t) where reprPrec v _ := s!"{v.name}"
mutual
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
    | data : (adt: Adt) -> {t: Ty} -> (v: DataInst adt t) → Expr (adt[t])
    | matcher : (x: Expr (a[t])) -> (Match a a.Variants t res) -> Expr res

  inductive VariantInst : (a: Adt) -> (t:Ty) -> (v: List Tvar) -> Type
    | nil : VariantInst a t []
    | T : (t:Ty) -> (x: Expr t) -> (rest: VariantInst a t xs) -> VariantInst a t (Tvar.T::xs)
    | R : (t:Ty) -> (x: (Expr $ a[t])) -> (rest: VariantInst a t xs) -> VariantInst a t (Tvar.Rec::xs)

  inductive DataInst : (a : Adt) → (t:Ty) -> Type
    | k : (n:Fin a.Variants.length ) -> (data : VariantInst a t a.Variants[n].snd) -> DataInst a t

  inductive MatchCase : (r:Ty) -> (t:Ty) -> (v: List Tvar) -> (res: Ty) -> Type
    | nil : (e:Expr res) -> MatchCase r t [] res
    | T : (x: Var t) -> (rest: MatchCase r t xs res) -> MatchCase r t (Tvar.T::xs) res
    | R : (x: (Var r)) -> (rest: MatchCase r t xs res) -> MatchCase r t (Tvar.Rec::xs) res

  inductive Match : (a:Adt) -> (vs:List Variant) -> (t:Ty) -> (res:Ty) -> Type
    | nil : Match a [] t res
    | cons : (x: MatchCase (a[t]) t v.snd res) -> (Match a xs t res) → Match a (v::xs) t res

end

mutual

  def VariantInst.compile : VariantInst a t v -> String
    | VariantInst.T t x rest => Expr.compile x ++ " " ++ rest.compile
    | VariantInst.R t x rest => Expr.compile x ++ " " ++ rest.compile
    | _ => ""

  def Match.compile : Match a vs t res -> String
    | Match.nil => ""
    | Match.cons x rest => s!"#{vs[0]!.fst}\{{x.compile} {rest.compile}"

  def MatchCase.compile : MatchCase r t v res -> String
    | MatchCase.nil e => s!"}: {Expr.compile e}"
    | MatchCase.T x rest => s!"{x.name} {rest.compile}"
    | MatchCase.R x rest => s!"{x.name} {rest.compile}"

  def Expr.compile (e: Expr b) : String :=
    match e with
    | Expr.var v => v.name
    | Expr.intlit n => toString n
    | Expr.stringlit s => s
    | Expr.arith op a b => s!"({op} {Expr.compile a} {Expr.compile b})"
    | Expr.lam p b => "λ" ++ p.name ++ " " ++ Expr.compile b
    | Expr.app f x => "(" ++ Expr.compile f ++ " " ++ Expr.compile x ++ ")"
    | Expr.as t x => Expr.compile x
    | Expr.ftag n t => "@" ++ n
    | Expr.fn n x => "@" ++ n
    | Expr.sup l a b => s!"&{l}\{{Expr.compile a} {Expr.compile b}}"
    | Expr.nsup a b => s!"&\{{Expr.compile a} {Expr.compile b}}}"
    | Expr.dub l a b x y => s!"!&{l}\{{a.name} {b.name}} = {Expr.compile x} {Expr.compile y}"
    | Expr.data a v => s!"{match v with | DataInst.k n d => s!"#{(a.Variants[n].fst)}\{{d.compile}}"}"
    | Expr.matcher x m => s!"~({Expr.compile x})\{{m.compile}}"
end

mutual
  def Expr.collect {t} (e: Expr t) (m: Std.HashMap String String) : (Std.HashMap String String) :=
  match e with
    | Expr.var v => m
    | Expr.intlit n => m
    | Expr.stringlit s => m
    | Expr.ftag n t => m
    | Expr.arith op a b => Expr.collect a (Expr.collect b m)
    | Expr.fn n x =>
      let m := Expr.collect x m
      let n := "@" ++ n
      if m.contains n then m else m.insert n $ n ++ " = " ++ Expr.compile x
    | Expr.lam _ b => Expr.collect b m
    | Expr.app f x => Expr.collect x (Expr.collect f m)
    | Expr.as _ x => Expr.collect x m
    | Expr.sup _ a b => Expr.collect a (Expr.collect b m)
    | Expr.nsup a b => Expr.collect a (Expr.collect b m)
    | Expr.dub _ _ _ x y => Expr.collect x (Expr.collect y m)
    | Expr.data a v =>
      let show_vari := fun (v:Variant) => s!"#{v.fst}\{{ " ".intercalate $ v.snd.map (fun t => (t.choose "x" "rec"))}}"
      m.insert a.name $ s!"data {a.name} \{{" ".intercalate $ (a.Variants.map show_vari) }}"
    | Expr.matcher x mm => Expr.collect x m

def Expr.map {s} (e:Expr s) (f : {u:Ty} -> Expr u -> Expr u) : Expr s :=
  match e with
  | Expr.arith op a b =>  Expr.arith op (f a ) (f b )
  | Expr.lam a b =>  Expr.lam a (f b)
  | Expr.app l x =>  Expr.app (f l) (f x)
  | Expr.as t x =>  Expr.as t (f x)
  | Expr.fn n x =>  Expr.fn n (f x)
  | Expr.sup n a b =>  Expr.sup n (f a) (f b)
  | Expr.nsup a b =>  Expr.nsup (f a) (f b)
  | Expr.dub n a b x y =>  Expr.dub n a b (f x) (f y)
  | k => k

def Expr.fmap {s} (e:Expr s) (f : {u:Ty} -> Expr u -> Expr u) : Expr s :=
  match e with
  | Expr.arith op a b => f $ Expr.arith op (a.fmap f) (b.fmap f)
  | Expr.lam a b => f $ Expr.lam a (b.fmap f)
  | Expr.app ff x => f $ Expr.app (ff.fmap f) (x.fmap f)
  | Expr.as t x => f $ Expr.as t (x.fmap f)
  | Expr.fn n x => f $ Expr.fn n (x.fmap f)
  | Expr.sup n a b => f $ Expr.sup n (a.fmap f) (b.fmap f)
  | Expr.nsup a b => f $ Expr.nsup (a.fmap f) (b.fmap f)
  | Expr.dub n a b x y => f $ Expr.dub n a b (x.fmap f) (y.fmap f)
  | k => f k

end


mutual

def VariantInst.replace (v:VariantInst a t vs) (old: String) (new: String) : (VariantInst a t vs) :=
  VariantInst.fmap v (fun x => x.replace old new)

-- instance : VarContainer (VariantInst a t vs) where
--   replace v old new := VariantInst.fmap v (fun x => VarContainer.replace x old new)

def Expr.replace (e:Expr b) (v: String) (v': String) : Expr b :=
  match e with
  | .lam a b => if (a.name == v) then .lam a b else .lam a (.replace b v v')
  | .var x => if (x.name == v) then .var (Var.mk v') else .var x
  | .arith op a b => .arith op (.replace a v v') (.replace b v v')
  | .app f x => .app (.replace f v v') (.replace x v v')
  | .fn n x => .fn n (.replace x v v')
  | .sup n a b => .sup n (.replace a v v') (.replace b v v')
  | .nsup a b => .nsup (.replace a v v') (.replace b v v')
  | .dub n a b x y => .dub n a b (if a.name == v ∨ b.name == v then x else (x.replace v v')) (y.replace v v')
  | k => k

def VariantInst.linearize (v:VariantInst a t vs) : (VariantInst a t vs) × List String :=
  match v with
  | .nil => (VariantInst.nil, [])
  | .T t x rest =>
    let (x', xs) := x.linearize
    let (r', rs) := rest.linearize
    let collisions := (xs.filter (. ∈ rs))
    sorry
  | .R t x rest => sorry


  def resolve  {s} : List String -> ta -> tb -> (ta -> tb -> s) -> s := fun c a b fn =>
    match c with
    | [] => fn a b
    | c::cs =>
      let (c', c'') := (c ++ "1", c ++ "2")
      let ex := resolve cs (a.replace c c') (b.replace c c'') fn
      let ex := @Expr.dub int s 0 (newVar c') (newVar c'') (Expr.var (newVar c)) ex
      ex

  def merger {s ta tb : Ty} : ((Expr ta) × (List String)) -> ((Expr tb) × (List String)) -> (Expr ta -> Expr tb -> Expr s) -> (Expr s) × (List String) := fun (a,as) (b,bs) fn =>
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

end


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

def makelam (tag:String) (builder : (Expr a) -> Expr b) : Expr (arrow a b) :=
  let x: Var a := (newVar tag)
  Expr.lam x $ builder (Expr.var x)

def tag (n:String) : Expr s := Expr.ftag n s

def Ctr : (a:Adt) -> (t:Ty) -> (var: List Tvar) -> Type
  | a, t, [] => Expr $ a[t]
  | a, t, Tvar.T::xs => Expr t -> Ctr a t xs
  | a, t, Tvar.Rec::xs => Expr (a[t]) -> Ctr a t xs

def ctr : (a:Adt) -> (t:Ty) -> (v: List Tvar) -> ((VariantInst a t v) -> Expr (a[t])) -> (Ctr a t v)
  | _, _, [], f => (f VariantInst.nil)
  | a, t, Tvar.T::xs, f => fun x => ctr a t xs fun v => f $ VariantInst.T t x v
  | a, t, Tvar.Rec::xs, f => fun x => ctr a t xs fun v => f $ VariantInst.R t x v

def mkctr (a:Adt) (t) (n:Nat) (p:n<a.Variants.length := by decide): Ctr a t a.Variants[n].snd :=
  ctr a t a.Variants[n].snd fun v => Expr.data a $ DataInst.k ⟨n,p⟩ v

def CaseMaker (a t res: Ty) (vars : List Tvar) : (v:List Tvar) -> Type
  | [] => (Expr res) -> (MatchCase a t vars res)
  | Tvar.T::vs => (Var t) -> (CaseMaker a t res vars vs)
  | Tvar.Rec::vs => (Var a) -> (CaseMaker a t res vars vs)

def caseMaker (a t res: Ty) (vars: List Tvar) : (v: List Tvar) -> (MatchCase a t v res -> MatchCase a t vars res) -> (CaseMaker a t res vars v)
  | [], f => fun (ex:Expr res) => f (MatchCase.nil ex)
  | Tvar.T::vs, f => fun (va: Var t) => caseMaker a t res vars vs fun (cs) => f (MatchCase.T va cs)
  | Tvar.Rec::vs, f => fun (va: Var a) => caseMaker a t res vars vs fun (cs) => f (MatchCase.R va cs)

def mkcase  (a:Adt) (t res:Ty) (n:Nat) (p: n<a.Variants.length:= by decide) (vs:List Tvar := a.Variants[n].snd): (CaseMaker (a[t]) t res vs vs):=
  caseMaker (a[t]) t res vs vs (fun x => x)

def MatchMaker (a:Adt) (t res:Ty): (varis:List Variant) -> Type
  | [] => Match a (a.Variants) t res | vs::vss => (MatchCase (a[t]) t vs.snd res) -> MatchMaker a t res vss

def matchMaker (a:Adt) (t res:Ty): (varis:List Variant) -> (f: Match a varis t res → Match a a.Variants t res) -> MatchMaker a t res varis
  | [], f => (f Match.nil : Match a a.Variants t res)
  | vs::vss, f => fun (cs:MatchCase (a[t]) t vs.2 res) => matchMaker a t res vss fun m => f (Match.cons cs m)

def mkmatch (a:Adt) (t res:Ty) : MatchMaker a t res (a.Variants) := matchMaker a t res (a.Variants) fun m => m

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

def LIST := Adt.mk "list" [("CONS",[TT, RR]), ("NIL",[])]
def CONS := mkctr LIST int 0
def NIL := mkctr LIST int 1


#eval
  let main := fn "main" $ lam x -> (x) as (int -> int)
  compile main

#eval
  @main = NIL;
  compile main



#eval Expr.compile NIL

#eval
  @main = CONS (Expr.intlit 22) NIL;
  compile main

#eval
  let cc := CONS (Expr.intlit 22) NIL;
  @main =
    Expr.matcher cc ((mkmatch LIST int int)
        ((mkcase LIST int int 0) (newVar "h") (newVar "t") (Expr.var $ newVar "h"))
        ((mkcase LIST int int 1) (Expr.intlit 33))
    );
  compile main
