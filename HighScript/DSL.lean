
import Lean

import Std.Data.HashMap
set_option linter.unusedVariables false

inductive DataField : Type
  | T: DataField
  | R: DataField
deriving BEq, Hashable, Repr

abbrev TT := DataField.T
abbrev RR := DataField.R
def DataField.choose {a} (t:a) (r:a) : DataField → a | DataField.T => t | DataField.R => r

abbrev Variant := String × List (DataField)

structure Adt where
  name: String
  Variants : List Variant
deriving BEq, Hashable, Repr


inductive Ty
  | int
  | string
  | arrow: Ty -> Ty -> Ty
  | inst : (a: Adt) → Ty → Ty
deriving BEq, Hashable, Repr

open Ty

infixr:56 "->" => arrow
macro:100 adt:term:100 " [" t:term:100 "]" : term => `(inst $adt $t)

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
  deriving Repr

  inductive Instance : (a: Adt) -> (t:Ty) -> (v: List DataField) -> Type
    | nil : Instance a t []
    | cons : (tv: DataField) -> (x: Expr (tv.choose t (a [t]))) -> (Instance a t xs) -> Instance a t (tv::xs)

  inductive MatchCase : (r:Ty) -> (t:Ty) -> (v: List DataField) -> (res: Ty) -> Type
    | nil : (e:Expr res) -> MatchCase r t [] res
    | cons : (tv: DataField) -> (vr: Var (tv.choose t r)) -> MatchCase r t vs res -> MatchCase r t (tv::vs) res

  inductive Match : (a:Adt) -> (t:Ty) -> (vs:List Variant) -> (res:Ty) -> Type
    | nil : Match a t [] res
    | cons : (x: MatchCase (a[t]) t v.snd res) -> (Match a t xs res) → Match a t (v::xs) res

end

@[match_pattern] def Expr.var (vr:Var t) := Expr.nullary (NullaryOp.var vr)
@[match_pattern] def Expr.int n := Expr.nullary (.intlit n)
@[match_pattern] def Expr.string s := Expr.nullary (.stringlit s)
@[match_pattern] def Expr.lam (vr: Var a) (e:Expr b) := Expr.unary (UnaryOp.lam vr) e
@[match_pattern] def Expr.app (a: Expr (arrow ta tb)) (b:Expr ta) := Expr.binary (.app) a b
@[match_pattern] def Expr.fn name (bod:Expr t):= Expr.unary (.fn name) bod
@[match_pattern] def Expr.dub n (a b: Var t) e (res:Expr u) := Expr.binary (.dub n a b ) e res
@[match_pattern] def Expr.arith op (a b) := Expr.binary (.arith op) a b


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

  def Expr.compile (tabs: Nat := 0) (e:Expr t) : String :=
    let tt := tabs + 1
    let nl := "\n".pushn ' ' (tabs * 2)
    match e with
    | .nullary $ NullaryOp.intlit n => s!"{n}"
    | .nullary $ NullaryOp.stringlit s => s!"\"{s}\""
    | .nullary $ NullaryOp.var v => s!"{v.name}"
    | .nullary $ NullaryOp.ftag s t => s!"@{s}"
    | .unary (UnaryOp.lam v) e => s!"λ {v.name} {e.compile tt}"
    | .unary (UnaryOp.fn n) e => s!"@{n}"
    | .unary (UnaryOp.as t) e => s!"{e.compile tt}"
    | .binary op a b => match op with
      | .arith op => s!"({op} {a.compile} {b.compile tt})"
      | .app => s!"({a.compile tt} {b.compile tt})"
      | .sup n => s!"&{n}\{{a.compile tt} {b.compile tt}}"
      | .nsup => s!"&\{{a.compile tt} {b.compile tt}}"
      | .dub n x y => s!"{nl}!&{n}\{{x.name} {y.name}}={a.compile tt}{nl}{b.compile tt}"
    | .data adt n i => s!"#{(adt.Variants[n]).1} \{{ i.compile }}"
    | .mmatch x m => s!"~({x.compile}) {nl}\{{m.compile tt}{nl}}"

  def MatchCase.compile (tabs:Nat:=0): MatchCase r t vs rest -> String
    | .nil e => "} : " ++ e.compile
    | .cons df vr rest => vr.name ++ " " ++ rest.compile tabs

  def Match.compile (tabs:Nat:=0) : Match a t vs rest -> String
    | .nil => ""
    | @Match.cons a t _ _ v m rest => s!" \n{"".pushn ' ' tabs}#{v.fst} \{{m.compile $ tabs + 1 } {rest.compile tabs}"

  def Instance.compile : (i:Instance adt t vs) -> String
    | .nil => ""
    | .cons tv x rest => s!"{x.compile}, {rest.compile}"


  def Expr.collect (m: Std.HashMap String String) : (e:Expr t) -> (Std.HashMap String String)
    | .unary (UnaryOp.fn n) e =>
      let m := e.collect m
      let n := "@" ++ n
      if m.contains n then m else m.insert n $ n ++ " = " ++ e.compile
    | .unary op e => e.collect m
    | .binary op a b => a.collect $ b.collect m
    | .data a _ _ =>
      let show_vari := fun (v:Variant) => s!"#{v.fst}\{{ " ".intercalate $ v.snd.map (fun t => (t.choose "x" "rec"))}}"
      m.insert a.name $ s!"data {a.name} \{{" ".intercalate $ (a.Variants.map show_vari) }}"
    | .mmatch x mt =>  x.collect $ mt.collect m
    | k => m

  def MatchCase.collect (m: Std.HashMap String String) : MatchCase r t vs res -> Std.HashMap String String
    | .nil e => e.collect m
    | .cons tv vr rest => rest.collect m

  def Match.collect (m: Std.HashMap String String) : Match a t vs res -> Std.HashMap String String
    | .nil => m
    | .cons x rest => x.collect $ rest.collect m

end

inductive HVM_Program | mk : String -> HVM_Program

def HVM_Program.tostring : HVM_Program -> String | .mk s => s ++ "\n"

instance : Repr HVM_Program where reprPrec p _ := p.tostring

def compile {s} (e: Expr s) : HVM_Program :=
  let m := (e.linearize).fst.collect (Std.HashMap.empty)
  let all_code := m.fold (init := "") (fun acc _ v => acc ++ v ++ "\n\n")
  HVM_Program.mk all_code

def Ctr : (a:Adt) -> (t:Ty) -> (var: List DataField) -> Type
  | a, t, [] => Expr $ a[t]
  | a, t, DataField.T::xs => Expr t -> Ctr a t xs
  | a, t, DataField.R::xs => Expr (a[t]) -> Ctr a t xs

def ctr : (a:Adt) -> (t:Ty) -> (v: List DataField) -> ((Instance a t v) -> Expr (a[t])) -> (Ctr a t v)
  | _, _, [], f => (f Instance.nil)
  | a, t, DataField.T::xs, f => fun x => ctr a t xs fun v => f $ Instance.cons DataField.T x v
  | a, t, DataField.R::xs, f => fun x => ctr a t xs fun v => f $ Instance.cons DataField.R x v

def mkctr (a:Adt) (t) (n:Fin a.Variants.length): Ctr a t a.Variants[n].snd :=
  ctr a t a.Variants[n].snd fun v => Expr.data a n v

def CaseMaker (a t res: Ty) (vars : List DataField) : (v:List DataField) -> Type
  | [] => (Expr res) -> (MatchCase a t vars res)
  | DataField.T::vs => (Var t) -> (CaseMaker a t res vars vs)
  | DataField.R::vs => (Var a) -> (CaseMaker a t res vars vs)

def caseMaker (a t res: Ty) (vars: List DataField) : (v: List DataField) -> (MatchCase a t v res -> MatchCase a t vars res) -> (CaseMaker a t res vars v)
  | [], f => fun (ex:Expr res) => f (MatchCase.nil ex)
  | DataField.T::vs, f => fun (va: Var t) => caseMaker a t res vars vs fun (cs) => f (MatchCase.cons .T va cs)
  | DataField.R::vs, f => fun (va: Var a) => caseMaker a t res vars vs fun (cs) => f (MatchCase.cons .R va cs)

def mkcase  (a:Adt) (t:Ty) {res:Ty} (n:Nat) (p: n<a.Variants.length:= by decide) (vs:List DataField := a.Variants[n].snd): (CaseMaker (a[t]) t res vs vs):=
  caseMaker (a[t]) t res vs vs (fun x => x)

def fn (name:String) (e:Expr t): Expr t := Expr.fn name e

def astype  (t:Ty) (x: Expr t): Expr t := x

macro "lam" x:ident ":" t:term "=>" body:term : term => `(
  let $x := Var.mk $t $(Lean.quote (x.getId.toString));
  let binder := (Expr.lam $x)
  let $x : Expr $t := Expr.var $x;
  (binder $body)
)

macro "lam" x:ident "=>" body:term : term => `(
  let $x := newVar $(Lean.quote (x.getId.toString));
  let binder := (Expr.lam $x)
  let $x := Expr.var $x;
  (binder $body)
)

infixl:70 "**" => Expr.app
infixl:70 "⬝" => Expr.app
infixl:70 "•" => Expr.app
macro "(" a:term:70 b:term:71 ")" : term => `(Expr.app $a $b)

macro:50 "@" n:ident ":" typ:term:50 "; " body:term:50 : term=> `(let $n := Expr.ftag $(Lean.quote (n.getId.toString)) $typ; $body)
macro:50 "@" n:ident "=" val:term:50 "; " body:term:50 : term=> `(let $n := fn $(Lean.quote (n.getId.toString)) $val; $body)
macro:100 "#" n:num : term => `(Expr.int $n)
macro:100 "#" n:str : term => `(Expr.string $n)

macro:50 v:term:50 "as" t:term:51 : term => `(astype $t $v)

macro:50 "var" n:ident ":" t:term:50 ";" bod:term  : term => `(let $n :Var $t := newVar $(Lean.quote (n.getId.toString)); $bod)
macro:50 "&" l:num "{" a:term:50 "," b:term:50  "}" "=" c:term:50 ";" d:term:50 : term => `(Expr.dub $l $a $b $c $d)
macro:50 "&" l:num "{" a:term:50 "," b:term:50  "}" : term => `(Expr.sup $l $a $b)
macro:50 a:term:50 "+" b:term:51 : term => `(Expr.arith "+" $a $b)
macro:50 a:term:50 "-" b:term:51 : term => `(Expr.arith "-" $a $b)
macro:60 a:term:60 "*" b:term:61 : term => `(Expr.arith "*" $a $b)
macro:60 a:term:60 "/" b:term:61 : term => `(Expr.arith "/" $a $b)



declare_syntax_cat construction
syntax "#" ident "{" ident* "}" : construction

def ident2stringlit (x : Lean.TSyntax `ident) := Lean.Syntax.mkStrLit x.getId.toString

def construc (name:String) (xs: List (String × List String)) :Adt :=
  Adt.mk name $ xs.map (fun x => (x.1, x.2.map (fun x=> if x == "rec" then RR else TT)))


macro "data" name:ident "{" ctrs:construction* "}" rest:term : term => do
  let mut allLists := #[]
  let mut assign := ← `($rest)
  let mut c := Lean.Syntax.mkNatLit 0
  for ctr in ctrs do
    match ctr with
    | `(construction| #$ctrname { $args* }) =>
        let strLits ← args.mapM fun id => `($(ident2stringlit id))
        allLists := allLists.push ( ← `(( $(ident2stringlit ctrname) , [$strLits,*])))
        assign := ← `(
          let $ctrname := mkctr $name int ⟨$c, by decide⟩
          $assign )
        c := Lean.Syntax.mkNatLit (c.getNat + 1)
    | _ => _ := ()

  return (← `(
    let arr : List (String × ( List String)) := [$allLists,*];
    let $name := construc ($(ident2stringlit name)) arr
    $assign
  ))


declare_syntax_cat match_case
syntax "#" ident "{" ident* "}" ":" term : match_case


def extadt {a:Adt} {t:Ty} (i:Expr $ a[t]) := a
def extty {a:Adt} {t:Ty} (i:Expr $ a[t]) := t


macro "~" argument:term ":" "{" arms:match_case+ "}" : term => do

  let mut assign := ← `(Match.nil)
  let mut c := arms.size
  for arm in arms.reverse do
    match arm with
    |  `(match_case | # $variantname {$fieldvars*} : $bod) =>
      c := c - 1
      let mut arm := ← `((mkcase a t $(Lean.Syntax.mkNatLit c)))
      for fieldvar in fieldvars do
        arm := ← `( $arm (newVar $(ident2stringlit fieldvar)))
      assign :=  ← `(
        Match.cons ( ($arm) ($bod))
        $assign)
    | _ => _ := ()

  return  (<- `(
    let arg := $argument
    let a := extadt arg
    let t := extty arg
    Expr.mmatch arg $
    $assign
    ))
