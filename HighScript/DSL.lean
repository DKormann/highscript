import Lean
import Std.Data.HashMap
import Std.Tactic


set_option linter.unusedVariables false

mutual

  inductive Adt
    | nil : Adt
    | cons : String -> Variant -> Adt-> Adt
  deriving BEq, Hashable, Repr

  inductive Variant
    | nil : Variant
    | cons: Option Ty -> Variant -> Variant
  deriving BEq, Hashable, Repr

  inductive Ty
    | int
    | string
    | arrow: Ty -> Ty -> Ty
    | adt : String -> Adt -> Ty
  deriving BEq, Hashable, Repr

end

open Ty

mutual

  def Adt.repr (a:Adt) : String :=
    match a with
    | .nil => "nil"
    | .cons n v r => s!"{n} {v.repr} {r.repr}"

  def Variant.repr (v:Variant) : String :=
    match v with
    | .nil => "Variant.nil"
    | .cons df xs => s!"Variant.cons {xs.repr}"

  def Variant.size (v:Variant) : Nat :=
    match v with
    | .nil => 0
    | .cons _ xs => 1 + xs.size

  def Ty.repr (t:Ty) : String :=
    match t with
    | .int => "int"
    | .string => "string"
    | .arrow a b => s!"({a.repr} -> {b.repr})"
    | .adt n a => s!"adt {n} {a.repr}"

end

structure NamedVariant where
  name: String
  v: Variant
  deriving BEq, Hashable, Repr

def Adt.get : (n:Nat) -> (a:Adt) -> NamedVariant
  | _, Adt.nil => .mk "nil" .nil
  | 0, Adt.cons n a r => .mk n a
  | n+1, .cons _ _ r => r.get n

structure Var (t: Ty) where
  name: String
deriving BEq, Hashable, Repr, DecidableEq

structure NamedAdt where
  name: String
  adt: Adt
deriving BEq, Hashable, Repr

def NamedAdt.Ty (self:NamedAdt) : Ty :=.adt self.name self.adt

def Adt.mk: (vs: List NamedVariant) -> Adt
  | [] => .nil
  | v::vs => .cons v.name v.v $ Adt.mk vs


def mkNamedAdt (name:String) (vs: List NamedVariant) : NamedAdt := .mk name $ Adt.mk vs


def Var.ty (v:Var t) := t
def newVar (name:String) : Var t := ⟨name⟩


structure TypedVar where
  t: Ty
  name: String



instance : BEq TypedVar where
  beq a b := a.name == b.name && a.t == b.t

def TypedVar.var (x:TypedVar) := @Var.mk x.t x.name

def TypedVar.from {t:Ty} (v: Var t) := TypedVar.mk t v.name

def Adt.variants : (self:Adt) -> List NamedVariant
  | .nil => []
  | .cons n v r => (NamedVariant.mk n v) :: r.variants

mutual

  inductive NullaryOp : Ty -> Type
    | intlit : Nat -> NullaryOp int
    | stringlit : String -> NullaryOp string
    | var : Var t -> NullaryOp t
    | ftag : String -> (s:Ty) -> NullaryOp s
    | eraser : NullaryOp t

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
    | lett : (Var t) -> BinaryOp a b b

  inductive Expr : Ty → Type
    | nullary : NullaryOp b -> Expr b
    | unary : UnaryOp a b -> Expr a -> Expr b
    | iff : Expr int -> (shared:List TypedVar:= []) -> Var int -> Expr b ->  Expr b -> Expr b
    | binary : BinaryOp a b c -> Expr a -> Expr b -> Expr c
    | data : {a:NamedAdt} -> (n:Nat) -> Instance a (a.adt.get n).v -> Expr a.Ty
    | mmatch : {a:NamedAdt} -> Expr a.Ty -> (shared: List TypedVar := []) -> (css : Match a (a.adt.variants.map (NamedVariant.name)) (a.adt.variants.map (NamedVariant.v)) res) -> Expr res

  inductive Match : NamedAdt -> List String -> List Variant -> Ty -> Type
    | nil : Match a [] [] res
    | cons : (name:String) -> (c:MatchCase a v res) -> Match a ns xs res -> Match a (name::ns) (v::xs) res

  inductive Instance : NamedAdt -> Variant -> Type
    | nil : Instance a .nil
    | cons : (v:Expr $ match vo with | .none => a.Ty | .some x => x) -> Instance a xs -> Instance a (Variant.cons vo xs)

  inductive MatchCase : (arg: NamedAdt) -> (done: Variant) -> (res:Ty) -> Type
    | nil : Expr res -> MatchCase arg Variant.nil res
    | cons {df : Option Ty} : (v:Var $ match df with | .none => arg.Ty | .some x =>x ) ->
      MatchCase arg xs res -> MatchCase arg (Variant.cons df xs) res

end

inductive ListWrap : {t:Type} -> (fn: t -> Type) -> (List t) -> Type
  | nil : ListWrap fn []
  | cons : {t:Type} -> {fn :t->Type} -> {ts:List t} -> (idx:t) -> (x : fn idx ) -> (xs:ListWrap  fn ts) -> ListWrap fn (idx::ts)


section Expr_fields

  @[match_pattern] def Expr.var (vr:Var t) := Expr.nullary (NullaryOp.var vr)
  @[match_pattern] def Expr.int n := Expr.nullary (.intlit n)
  @[match_pattern] def Expr.string s := Expr.nullary (.stringlit s)
  @[match_pattern] def Expr.ftag name (t:Ty) := Expr.nullary (.ftag name t)
  @[match_pattern] def Expr.eraser : Expr t := Expr.nullary (.eraser)
  @[match_pattern] def Expr.astype (t:Ty) (e:Expr t) := Expr.unary (.as t) e
  @[match_pattern] def Expr.lam (vr: Var a) (e:Expr b) := Expr.unary (UnaryOp.lam vr) e
  @[match_pattern] def Expr.fn name (bod:Expr t):= Expr.unary (.fn name) bod
  @[match_pattern] def Expr.app (a: Expr (arrow ta tb)) (b:Expr ta) := Expr.binary (.app) a b
  @[match_pattern] def Expr.let (v: Var a) (e:Expr a) (bod:Expr b) := Expr.binary (.lett v) e bod
  @[match_pattern] def Expr.dub n (a b: Var t) e (res:Expr u) := Expr.binary (.dub n a b ) e res
  @[match_pattern] def Expr.sup n (a b:Expr t) := Expr.binary (.sup n) a b
  @[match_pattern] def Expr.nsup (a b:Expr t) := Expr.binary (.nsup) a b
  @[match_pattern] def Expr.arith op (a b) := Expr.binary (.arith op) a b


end Expr_fields


declare_syntax_cat typed_var
syntax ident ":" ident : typed_var

declare_syntax_cat construction
syntax "#" ident typed_var* : construction
-- syntax "#" ident : construction

macro "data" name:ident targs:ident* "{" arms:construction* "}" rest:term : term => do

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
      -- | `(construction| #$ctrname ) => ctrsdata := ctrsdata.push (ctrname, #[])
      | _ => Lean.Macro.throwUnsupported

  ctrsdata := ctrsdata.insertionSort (fun (a, _) (b, _) => a.getId.toString < b.getId.toString)

  let ty :=
    ← targs.foldrM
      (fun arg acc => do return ← `(fun ( $arg : Ty) => $acc))
      (← `(
        (mkNamedAdt $(Lean.quote (name.getId.toString))
        $((← ctrsdata.foldrM
          (fun (ctrname, ctrargs) acc => do
            let vinner :=
              ← ctrargs.foldrM
              (fun (a,t) acc => do return ← if t.getId.toString == "self" then `(Variant.cons .none $acc) else `(Variant.cons $t $acc))
              (← `(Variant.nil))
            return (← `((NamedVariant.mk $(Lean.quote (ctrname.getId.toString)) $vinner )::$acc)))
          (←`([]))
        ))).Ty))

  let fullty := ← targs.reverse.foldrM (fun arg acc => do return ← `($acc $arg)) (←`($name))
  let selftype ← `((Expr $fullty))

  let ctrs ← (ctrsdata.zipIdx).foldrM
    (fun ((ctrname, ctrargs), c) acc => do
      let inst := ← ctrargs.foldrM
        (fun (a, t) acc => do return (← if t.getId.toString == "self" then `( Instance.cons $a $acc) else `(Instance.cons $a $acc)))
        (← `(Instance.nil))
      let confn ← ctrargs.foldrM
        (fun (a, t) acc => do
          let ty := ← if t.getId.toString == "self" then `($selftype) else `(Expr $t)
          return ← `(
            let ty := $ty;
            fun ( $a : $ty) => $acc))
        (← `(let res : $selftype := (Expr.data $(Lean.Syntax.mkNatLit c) $inst); res))
      return ← `(
        let $ctrname := $(( ← targs.foldrM (fun arg (acc: Lean.TSyntax `term) => do return ← `(fun {$arg : Ty} => $acc)) (← `($confn))))
        $acc)
    )
    (rest)
    return ← `(let $name := ($ty); $ctrs)

declare_syntax_cat match_arm
syntax "#" ident ident* ":" term : match_arm
-- syntax "#" ident ":" term : match_arm

declare_syntax_cat braced_term
syntax ident : braced_term
syntax "(" term ")" : braced_term

def parse_braced_term (arg: Lean.TSyntax `braced_term) : Lean.MacroM (Lean.TSyntax `term) := do
  match arg with
  | `(braced_term| $x:ident) => return ← `($x)
  | `(braced_term| ($x:term)) => return x
  | _ => Lean.Macro.throwUnsupported


macro "~" arg:braced_term "{" arms:match_arm* "}" : term => do
  let mut dat := #[]
  for arm in arms do
    match arm with
    | `(match_arm| # $variantname $vars* : $bod) =>
      dat := dat.push (variantname, vars, bod)
    | _ => Lean.Macro.throwUnsupported

  dat := dat.insertionSort (fun (a, _, _) (b, _, _) => a.getId.toString < b.getId.toString)

  let matcher ← dat.foldrM
    (fun (variantname, vars, bod) acc => do
        let case := ← vars.foldrM
          (fun (var:Lean.TSyntax `ident) acc => do return ←
            `(
              let $var := Var.mk $(Lean.quote (var.getId.toString));
              MatchCase.cons $var (let $var := Expr.var $var; $acc)
              ))
          (← `(MatchCase.nil $bod))
        return ← `(Match.cons $(Lean.quote variantname.getId.toString) $case $acc)
    )
    (← `(Match.nil))

  let arg ← parse_braced_term arg
  return ← `(Expr.mmatch $arg [] $(matcher))

def eint(n):= Expr.nullary $ .intlit n


mutual
  def Expr.repr (e:Expr t) : String :=
    match e with
    | .nullary op => match op with
      | .intlit n => s!"{n}"
      | .stringlit s => s!"\"{s}\""
      | .var v => s!"{v.name}"
      | .ftag s t => s!"@{s}"
      | .eraser => "*"
    | .unary op e => match op with
      | .lam v => s!"λ {v.name} {e.repr}"
      | .fn n => s!"@{n}"
      | .as t => s!"{e.repr}"
    | .binary op a b => match op with
      | .arith op => s!"({op} {a.repr} {b.repr})"
      | .app => s!"({a.repr} {b.repr})"
      | .sup n => s!"&{n}\{{a.repr} {b.repr}}"
      | .nsup => s!"&\{{a.repr} {b.repr}}"
      | .dub n x y => s!"!&{n}\{{x.name} {y.name}}={a.repr} {b.repr}"
      | .lett v => s!"! {v.name} = {a.repr}\n{b.repr}"
    | .iff c sd p t f => s!"~({c.repr}) {" ".intercalate (sd.map ("!"++TypedVar.name .))} \{\n0: {f.repr}\n{p.name}: {t.repr}\n}"
    | @Expr.data a n i => s!"#{(a.adt.get n).name}  \{{i.repr}}"
    | .mmatch x s m => s!"~({x.repr}) {" ".intercalate (s.map ("!"++TypedVar.name . ))} \{{m.repr}}"



  def Adt.compile (a:Adt) : String :=
    match a with
    | .nil => ""
    | .cons n v r => s!"#{n}\{{v.compile}} {r.compile}"

  def Variant.compile (v:Variant) : String :=
    match v with
    | .nil => ""
    | .cons df xs => s!"x {xs.compile}"

  instance : Repr (Expr t) where reprPrec e _ := e.repr

  def Instance.repr (i:Instance a vs) : String :=
    match i with
    | .nil => ""
    | .cons e rest => s!"{e.repr} {rest.repr}"

  def MatchCase.repr (m: MatchCase a vs res) : String :=
    match m with
    | .nil e => "} : " ++ e.repr
    | .cons vr rest => s!"{vr.name} {rest.repr}"

  def Match.repr (m:Match a nms vs res) : String :=
    match m with
    | .nil => ""
    | Match.cons name x rest => s!"\n#{name}\{{x.repr} {rest.repr}"

end


mutual

  def Var.replace {t:Ty} (x:Var t) (v v': String): Var t :=
    if x.name == v then (.mk v') else x

  def TypedVar.replace (x:TypedVar) (v v':String): TypedVar :=
    if x.name == v then (.mk x.t v') else x

  def Expr.replace (v v':String): (e:Expr b) -> Expr b
    | .var vr => .var $ vr.replace v v'
    | .lam a e => .lam a (if a.name == v then e else e.replace v v')
    | .unary op e => .unary op (e.replace v v')
    | .binary op a b => .binary op (a.replace v v') (b.replace v v')
    | .iff c sd vr t f => .iff (c.replace v v') (sd.map (fun x => x.replace v v')) (vr.replace v v') (t.replace v v') (f.replace v v')
    | .data n i => .data n $ i.replace v v'
    | .mmatch x s m => .mmatch (x.replace v v') s m
    | k => k

  def Instance.replace (v v':String):
    (i:Instance a vs) -> Instance a vs
    | .nil => .nil
    | .cons x rest => .cons (x.replace v v') $ rest.replace v v'

  def MatchCase.replace (v v': String) :
    (m:MatchCase a vs res) -> MatchCase a vs res
    | .nil e => .nil (e.replace v v')
    | .cons vr rest => .cons (if vr.name == v then newVar v' else vr) $ rest.replace v v'

  def Match.replace(v v':String) :
    (m: Match a nms vs res) -> Match a nms vs res
    | .nil => .nil
    | .cons nm x rest => .cons nm (x.replace v v') $ rest.replace v v'

  def Expr.resolve  {s} (c: List TypedVar) (a: Expr ta) (b: Expr tb) (fn :Expr ta -> Expr tb -> Expr s) : Expr s :=
    match c with
    | [] => fn a b
    | c::cs =>
      let (c', c'') := (c.name ++ "1", c.name ++ "2")
      Expr.dub 0 (newVar c') (newVar c'') (Expr.var $ c.var)
      $ .resolve cs (a.replace c.name c') (b.replace c.name c'') fn

  def Expr.linearize : (e:Expr b) -> Expr b × List TypedVar
    | .var vr => (.var vr, [TypedVar.from vr])
    | .lam vr a =>
      let (a, as) := a.linearize
      (.lam vr a, as.filter (fun x => x.name != vr.name))
    | .unary op a =>
      let (a, as) := a.linearize
      (.unary op a, as)
    | .binary op a b =>
      let (a, as) := a.linearize
      let (b, bs) := b.linearize
      let fn := fun a b => Expr.binary op a b
      (.resolve (as.filter (bs.contains ·)) a b fn, bs ++ as.filter (! bs.contains ·))

    -- | .iff c sd v t f =>
    --   let (c,cs) := c.linearize
    --   let (t,ts) := t.linearize
    --   let (f,fs) := f.linearize

    --   let ts := ts.filter (fun x => .from v != x)
    --   let tfcoll := ts.filter (fs.contains)
    --   let sd := sd ++ tfcoll.filter (!sd.contains .)
    --   let tfs := (ts ++ fs).filter (!sd.contains .)
    --   let collisions := cs.filter (tfs.contains)
    --   let collisions := collisions.map (fun v => (v, TypedVar.mk v.t (v.name ++ "1"), TypedVar.mk v.t (v.name ++ "2")))
    --   let (c, sd, t, f) :=
    --     collisions.foldl
    --       (fun (c,sd,t,f) (v,v',v'') =>
    --       (
    --         c.replace v.name v'.name,
    --         sd.map (TypedVar.replace . v.name v''.name),
    --         t.replace v.name v''.name,
    --         f.replace v.name v''.name,
    --       ))
    --       (c,sd,t,f)

    --   .mk (.iff c sd v t f) $ cs ++ tfs.filter (!cs.contains .)


    | .iff c sd v t f =>
      let (c, cs) := c.linearize
      let (t, ts) := t.linearize
      let (f, fs) := f.linearize

      let sd := ts.filter (fs.contains ·)
      let tfs := ts ++ fs.filter (! ts.contains ·)

      let collisions := cs.filter (tfs.contains ·)
      let collisions := collisions.map (fun v => (v, TypedVar.mk v.t (v.name ++ "1"), TypedVar.mk v.t (v.name ++ "2")))

      let (c, sd, t, f) :=
        collisions.foldl
          (fun (c, sd, t, f) (v, v', v'') =>
            (
              c.replace v.name v'.name,
              sd.map (TypedVar.replace . v.name v''.name),
              t.replace v.name v''.name,
              f.replace v.name v''.name,
            ))
            (c, sd, t, f)

      let exp := (Expr.iff c sd v t f)

      let exp := collisions.foldl
        (fun e (v, v', v'') =>
          Expr.dub 0 (newVar v'.name) (newVar v''.name) (Expr.var $ v.var) e)
        exp

      .mk exp $ cs ++ tfs.filter (!cs.contains ·)

    | .data n i =>
      let (i, xs, rtd) := i.linearize
      let ex := rtd.foldl (fun x c =>
        Expr.dub 0
          (newVar (c.name ++ "1"))
          (newVar (c.name ++ "2")) (.var $ c.var) x) (Expr.data n i)
      (ex, xs)
    | .mmatch x s m =>
      let (x, xs) := x.linearize
      let (m, rs, os) := m.linearize
      let collisions := xs.filter rs.contains
      let (x, m) := collisions.foldl (fun (x, m) c =>
        (x.replace c.name $ c.name ++ "1", m.replace c.name $ c.name ++ "2")) (x, m)
      let ex := collisions.foldl (fun x c =>
        Expr.dub 0
          (newVar (c.name ++ "1"))
          (newVar (c.name ++ "2")) (.var $ c.var) x) $ Expr.mmatch x (s++os) m
      (ex, xs ++ rs.filter (! xs.contains ·))
    | k => (k, [])

  def Instance.linearize : (i:Instance a vs) -> Instance a vs × List TypedVar × List TypedVar
    | .nil => (.nil, .nil, .nil)
    | .cons x rest =>
      let (x, xs) := x.linearize
      let (r, rs, rtd) := rest.linearize
      let collisions := xs.filter (rs.contains ·)
      let alls := rs ++ xs.filter (! rs.contains ·)
      let (x,r) := collisions.foldl (fun (x,r) c =>
        (x.replace c.name $ c.name ++ "1", r.replace c.name $ c.name ++ "2")) (x,r)
      (.cons x r, alls, rtd ++ collisions.filter (! rtd.contains ·))

  def MatchCase.linearize : (m:MatchCase a vs res) -> MatchCase a vs res × List TypedVar
    | .nil e =>
      let (e, es) := e.linearize
      (.nil e, es)
    | .cons x rest =>
      let (rest, xs) := rest.linearize
      (.cons x rest, xs.filter (. != (.from x)))

  def Match.linearize : (m:Match a nms vs res) -> Match a nms vs res × List TypedVar × List TypedVar
    | .nil => (.nil, [], [])
    | .cons v x rest =>
      let (x, xs) := x.linearize
      let (rest, rs, os) := rest.linearize
      let collisions := xs.filter (rs.contains ·)
      -- let (x, rest) := collisions.foldl
      --   (fun (x, r) c => (x.replace c.name $ c.name ++ "1", r.replace c.name $ c.name ++ "2"))
      --   (x,rest)
      (.cons v x rest, xs ++ rs.filter (! xs.contains ·), collisions ++ os.filter (! xs.contains ·))

  def Expr.collect (m:Std.HashMap String String) : (e:Expr t) -> Std.HashMap String String
    | .fn name e => e.collect $ m.insert ("@" ++ name) ("@" ++ name ++ "=" ++ e.repr)
    | @Expr.data a n i => i.collect $ m.insert ("data " ++ a.name) (s!"data {a.name}\{ {a.adt.compile}}")
    | .mmatch x s mt => x.collect $ mt.collect m
    | .unary op e => e.collect m
    | .binary op a b => a.collect (b.collect m)
    | _ => m

  def Instance.collect (m:Std.HashMap String String) : (i:Instance a vs) -> Std.HashMap String String
    | .nil => m
    | .cons x res => x.collect $ res.collect m

  def MatchCase.collect (m:Std.HashMap String String) : (m:MatchCase a vs res) -> Std.HashMap String String
    | .nil e => e.collect m
    | .cons vr rest => rest.collect m

  def Match.collect (m:Std.HashMap String String) : (m:Match a nms vs res) -> Std.HashMap String String
    | .nil => m
    | .cons name x rest => x.collect $ rest.collect m

end


inductive HVM_programm | mk : String -> HVM_programm

instance: Repr HVM_programm where reprPrec prg _ := match prg with | .mk s => s

def compile (e:Expr t) : HVM_programm :=
  let k := e.linearize.fst
  let m := k.collect Std.HashMap.empty
  let (ds,fs) := m.values.partition (fun x => x.startsWith "data")
  .mk $ "\n\n".intercalate $ ds ++ fs

section notations


  def liststuff :=

    data list a {
      #Cons h:a tail:self
      #Nil
    }
    (list, fun a => @Cons a, fun a => @Nil a)

  def list := liststuff.1
  def Cons {a} : (Expr a) -> (Expr (list a) ) -> Expr (list a)  := liststuff.2.1 a
  def Nil {a} : Expr (list a) := liststuff.2.2 a

  infixr:56 "->" => arrow

  -- macro "@" n:ident ":" typ:term:50 "; " body:term:50 : term=> `(let $n := Expr.ftag $(Lean.quote (n.getId.toString)) $typ; $body)
  -- macro "@" n:ident "=" val:term:50 "; " body:term:50 : term=> `(let $n := Expr.fn $(Lean.quote (n.getId.toString)) $val; $body)
  macro:100 "#" n:num : term => `(Expr.int $n)
  macro:100 "#" n:str : term => `(Expr.string $n)
  macro:50 v:term:50 "as" t:term:51 : term => `(Expr.astype $t $v)
  macro:50 "var" n:ident ":" t:term:50 ";" bod:term  : term => `(let $n :Var $t := newVar $(Lean.quote (n.getId.toString)); $bod)

  macro:50 "!" "&" l:num "{" a:ident "," b:ident  "}" "=" c:term:50 ";" d:term:50 : term =>
    `(
      let $a := newVar $(Lean.quote (a.getId.toString));
      let $b := newVar $(Lean.quote (b.getId.toString));
      Expr.dub $l $a $b $c (
      let $a := Expr.var $a;
      let $b := Expr.var $b;
      $d))

  macro:50 "!" "&" "{" a:ident "," b:ident  "}" "=" c:term:50 ";" d:term:50 : term => `(!& 0{$a, $b} = $c; $d)

  macro:50 "!" vr:ident "=" val:term:50 ";" bod:term:50 : term =>
    `(
      let $vr := newVar $(Lean.quote vr.getId.toString);
      Expr.let $vr $val (
      let $vr := Expr.var $vr;
      $bod
      ))

  declare_syntax_cat binder
  syntax ident : binder
  syntax "("ident ":" term")" : binder

  macro:50 "&" l:num "{" a:term:50 "," b:term:50  "}" : term => `(Expr.sup $l $a $b)
  macro:50 "&" "{" a:term:50 "," b:term:50  "}" : term => `(Expr.nsup $a $b)
  macro:50 a:term:50 "+" b:term:51 : term => `(Expr.arith "+" $a $b)
  macro:50 a:term:50 "-" b:term:51 : term => `(Expr.arith "-" $a $b)
  macro:60 a:term:60 "*" b:term:61 : term => `(Expr.arith "*" $a $b)
  macro:60 a:term:60 "/" b:term:61 : term => `(Expr.arith "/" $a $b)
  macro:60 a:term:60 "==" b:term:61 : term => `(Expr.arith "==" $a $b)
  macro:60 a:term:60 "!=" b:term:61 : term => `(Expr.arith "!=" $a $b)
  macro:60 "**" :term => `(Expr.eraser)

  instance : OfNat (Expr int) x where
    ofNat := Expr.int x


  macro "if" c:term "then" t:term "else" f:term : term =>
  `(Expr.iff $c [] (newVar "_currentifcond") $t $f)

  macro "iff" c:term "then" t:term "else" f:term : term =>
  `(Expr.iff $c [] (newVar "_currentifcond") $t $f)

  macro "if" cond:ident ":=" c:term "then" t:term "else" f:term : term =>
  `(
    let vr := newVar $(Lean.quote (cond.getId.toString));
    Expr.iff $c vr [] (let $cond := Expr.var vr;$t) $f
  )

  macro "iff" cond:ident ":=" c:term "then" t:term "else" f:term : term =>
  `(
    let vr := newVar $(Lean.quote (cond.getId.toString));
    Expr.iff $c vr [] (let $cond := Expr.var vr;$t) $f
  )

  macro:50 "lam" xs:binder* "=>" body:term : term =>
    (do
    return ← xs.foldrM (fun x acc => do
      let mut varn : Lean.TSyntax `ident ← `(x)
      let mut varex ← `(x)
      match x with
      | `(binder| $x:ident) =>
        varn := x
        varex ← `(Var.mk $(Lean.quote (x.getId.toString)))
      | `(binder| ($x:ident : $t:term)) =>
        varn := x
        varex ← `(@Var.mk $t $(Lean.quote (x.getId.toString)))
      | _ => Lean.Macro.throwUnsupported
      return ← `(
        let $varn := $varex;
        let binder := (Expr.lam $varn)
        let $varn := Expr.var $varn;
        (binder $acc)
      )) (← `($body)
    ))

  declare_syntax_cat funterm
  syntax ":" ident : funterm


  abbrev term := Lean.TSyntax `term

  def parsebinders (args: Lean.TSyntaxArray `binder) :  Lean.MacroM $ (Array $ Lean.TSyntax `ident) × (Array term) := do
    let mut fargs := #[]
    let mut wild_args := #[]
    for arg in args do
      match arg with
      | `(binder| $x:ident) =>
          fargs := fargs.push (← `($x))
          wild_args := wild_args.push x
      | `(binder| ($x:ident : $t:term)) =>
          fargs := fargs.push t
      | _ => Lean.Macro.throwUnsupported
    return (wild_args, fargs)

  macro "@" id:ident args:binder* "=" bod:term ";" rest:term : term =>
    do
    let mut (wild_args, fargs) ← parsebinders args

    let mut ftag : Lean.TSyntax `term ← fargs.foldrM
      (fun arg acc => do return ← `($arg -> $acc))
      (← `(res))

    ftag :=  ← wild_args.foldrM
      (fun x (acc : Lean.TSyntax `term) => do return ← `( fun {$x : Ty} => $acc))
      (← `(
        fun {res:Ty} =>
        Expr.ftag $(Lean.quote (id.getId.toString)) $ftag))

    let fn := (← args.foldrM (fun arg acc => `(lam $arg => $acc)) (← `($bod)))

    return (← `(
    let $id := $ftag
    let $id := Expr.fn $(Lean.Syntax.mkStrLit id.getId.toString) ($fn)
    $rest))

  macro "@" id:ident args:binder* ":" ret:braced_term "=" bod:term ";" rest:term : term =>
    do

    let mut (wild_args, fargs) ← parsebinders args

    let mut ftag : Lean.TSyntax `term ← fargs.foldrM
      (fun arg acc => do return ← `($arg -> $acc))
      (← parse_braced_term ret)

    ftag :=  ← wild_args.foldrM
      (fun x (acc : Lean.TSyntax `term) => do return ← `( fun {$x : Ty} => $acc))
      (← `( Expr.ftag $(Lean.quote (id.getId.toString)) $ftag))

    let fn := (← args.foldrM (fun arg acc => `(lam $arg => $acc)) (← `($bod)))

    return (← `(
    let $id := $ftag
    let $id := Expr.fn $(Lean.Syntax.mkStrLit id.getId.toString) ($fn)
    $rest))

  macro "(" a:ident b:ident ")" : term => `(Expr.app $a $b)
  macro "(" a:term b:term ")" : term => `(Expr.app $a $b)


  infixl:56 "•" => Expr.app

  macro "[" a:term,* "]" : term => do return ← a.getElems.foldrM (fun x acc => `(Cons $x $acc)) (← `(Nil))

end notations

#eval

  let n : Expr int := .var $ Var.mk "n";
  (
    if 1 == 22
    then n
    else (n + (1 as int))
  ).linearize.fst



def extractinfo{t} : (e:Expr t) -> String
  | Expr.mmatch a b c => "p"
  | _ => "nop"


#eval
  data p { #P x:int }

  let s : Expr p := .var $ Var.mk "s";

  let mm :=

  ! s = P 22;

  ~ s {
    #P x: s
  };

  mm.linearize.fst




#check

  let f := lam (x:int) => x;

  @len (l :  int) k = (len • k • (#0));

  @len (l:int) k : (int) = (len • k • (#0));

  len



#eval

  data List a {
    #Cons h:a tail:self
    #Nil
  }

  let a := .int 1;
  let b := .int 2;
  let c := .int 3;


  let abc := (Cons a (Cons b (Cons c Nil))) as (List int)

  @len (l : List int)  =
    ~l {
      #Cons h tail : #1 + (len • tail)
      #Nil : #0
    };

  compile len

#eval

  let fn := fun (x:Nat) => x + 1
  let lm := lam (x:int) => x + #1
  (lm #22)


#eval

  let nil :Expr $ list int := Nil

  let mm : Expr int := ~ nil {
    #Nil  : .int 22
    #Cons x tail : .int 33
  }

  let mm : Expr int := ~ (Nil as list int) {
    #Nil : .int 22
    #Cons x tail : .int 33
  }

  mm


#eval
  ! x = Cons (#22) Nil;
  x

#check
  let a : Expr int := #22

  let r := a + a

  @fn = lam a => a + a;

  @fnn = lam (a:int) => a;

  22


#eval

  data union a b {
    #A v:a
    #B v:b
  }

  data listorint {
    #orint v: int
    #orstr v: string
  }

  let a : Expr $ union int string := A (.int 22)
  let b := B (.string "hello")

  let ffn := fun x => x ++ "ok"
  let x := "okok"
  let res := (ffn) x

  (b : (Expr (union int string)))


#eval
  data namedtuple a b {
    #Named x:a y:b
  }

  data list a b {
    #Nil
    #Cons x:a tail:self
  }

  let a := (Named (#22) (#"hello"))

  a
