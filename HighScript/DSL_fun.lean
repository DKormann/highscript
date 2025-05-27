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
    -- | Rcons : Variant -> Variant
    -- | cons : Ty -> Variant -> Variant
    | cons: Option Ty -> Variant -> Variant
  deriving BEq, Hashable, Repr

  inductive Ty
    | int
    | string
    | arrow: Ty -> Ty -> Ty
    | adt : String -> Adt -> Ty
  deriving BEq, Hashable, DecidableEq, Repr

end

open Ty


structure NamedVariant where
  name: String
  v: Variant
  deriving BEq, Hashable, Repr, DecidableEq

def Adt.contains  (a:Adt) (v:NamedVariant) : Bool :=
  match a with
  | .nil => false
  | .cons n v' a =>  (v = .mk n v') || a.contains v

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
  deriving BEq, Hashable, Repr, DecidableEq

def NamedAdt.Ty (self:NamedAdt) : Ty :=.adt self.name self.adt

def Adt.mk: (vs: List NamedVariant) -> Adt
  | [] => .nil
  | v::vs => .cons v.name v.v $ Adt.mk vs

def mkNamedAdt (name:String) (vs: List NamedVariant) : NamedAdt := .mk name $ Adt.mk vs


def Var.ty (v:Var t) := t
def newVar (name:String) : Var t := ⟨name⟩


def Option.Ty (self: Ty) : (v:Option Ty) -> Ty
  | .none => self
  | .some x => x

def Option.Variant (v: Variant): (Option _root_.Ty) -> Variant
  | .none => Variant.Rcons v
  | .some x => Variant.cons x v

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
    | binary : BinaryOp a b c -> Expr a -> Expr b -> Expr c
    | data : {a:NamedAdt} -> (n:Nat) -> Instance a (a.adt.get n).v -> Expr a.Ty
    | mmatch {a:NamedAdt}: Expr a.Ty -> Match a a.adt res -> Expr res

  inductive Instance : (NamedAdt) -> Variant -> Type
    | nil : Instance a .nil
    | self : (e: Expr $ a.Ty) -> Instance a v -> Instance a (.Rcons v)
    | cons : (e: Expr t) -> Instance a v -> Instance a (.cons t v)

  inductive Match : (a:NamedAdt) -> (done: Adt) -> (res:Ty) -> Type
    | nil : Match arg Adt.nil res
    | cons : (name:String) -> MatchCase a v res -> Match a xs res -> Match arg (Adt.cons name v xs) res

  inductive MatchCase : (arg: NamedAdt) -> (done: Variant) -> (res:Ty) -> Type
    | nil : Expr res -> MatchCase arg done res
    -- | self : (v:Var arg.Ty) -> MatchCase arg xs res -> MatchCase arg (Variant.Rcons xs) res
    -- | cons : (v:Var vt) -> MatchCase arg xs res -> MatchCase arg (Variant.cons vt xs) res
    | cons {df : Option Ty} : (v:Var $ df.Ty arg.Ty) -> MatchCase arg xs res -> MatchCase arg (df.Variant xs) res


end




def nil : NamedVariant := .mk "nil" .nil
def cons : NamedVariant := .mk "cons" $ .cons int $ .Rcons .nil
def leaf : NamedVariant := .mk "leaf" $ .cons string $ .Rcons .nil
def sleaf : NamedVariant := .mk "sleaf" $ .cons string $ .Rcons .nil

def list : NamedAdt := mkNamedAdt "list" [cons, nil]

example : list.adt.contains nil := by decide


declare_syntax_cat typed_var
syntax ident ":" ident : typed_var

declare_syntax_cat construction
syntax "#" ident "{" typed_var* "}" : construction

macro "data" name:ident "(" targs:ident* ")" "{" arms:construction* "}" rest:term : term => do

  let mut ctrsdata := #[]
  for ctr in arms do
    match ctr with
      | `(construction| #$ctrname { $args* }) =>
        let mut arglist := #[]
        for arg in args do
          match arg with
          | `(typed_var| $arg:ident : $ty:ident) => arglist := arglist.push (arg, ty)
          | _ => Lean.Macro.throwUnsupported
        ctrsdata := ctrsdata.push (ctrname, arglist)
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
              (fun (a,t) acc => do return ← if t.getId.toString == "self" then `(Variant.Rcons $acc) else `(Variant.cons $t $acc))
              (← `(Variant.nil))
            return (← `((NamedVariant.mk $(Lean.quote (ctrname.getId.toString)) $vinner )::$acc)))
          (←`([]))
        ))).Ty))

  let fullty := ← targs.foldrM (fun arg acc => do return ← `($acc $arg)) (←`($name))
  let selftype ← `((Expr $fullty))

  let ctrs ← (ctrsdata.zipIdx).foldrM
    (fun ((ctrname, ctrargs), c) acc => do
      let inst := ← ctrargs.foldrM
        (fun (a, t) acc => do return (← if t.getId.toString == "self" then `( Instance.self $a $acc) else `(Instance.cons $a $acc)))
        (← `(Instance.nil))
      let confn ← ctrargs.foldrM
        (fun (a, t) acc => do
          let ty := ← if t.getId.toString == "self" then `($selftype) else `(Expr $t)
          return ← `(fun ( $a : $ty) => $acc))
        (← `(let res : $selftype := (Expr.data $(Lean.Syntax.mkNatLit c) $inst); res))
      return ← `(
        let $ctrname := $(( ← targs.foldrM (fun arg (acc: Lean.TSyntax `term) => do return ← `(fun {$arg : Ty} => $acc)) (← `($confn))))
        $acc)
    )
    (rest)
    return ← `(let $name := ($ty); $ctrs)


declare_syntax_cat match_arm
syntax "#" ident "{" ident* "}" ":" term : match_arm

macro "~" arg:term ":" "{" arms:match_arm,* "}" : term => do
  let matcher ← arms.getElems.foldrM
    (fun arm acc => do
      return ← match arm with
      | `(match_arm| #$variantname { $vars* } : $bod) => do
        let case := ← vars.foldrM
          (fun var acc => do return ←

            `($var))
          (← `(MatchCase.nil $bod))
        return ← `(Match.cons $(Lean.quote variantname.getId.toString) (MatchCase.nil $bod) $acc)
      | _ => Lean.Macro.throwUnsupported
    )
    (← `(Match.nil))

  return ← `( $(matcher))





-- #eval
#check
  data list (a) {
    #nil {}
    #cons {x:a tail:self }
  }

  let listty : Ty := list int

  let eint(n):= Expr.nullary $ .intlit n

  let ex : Expr listty := nil
  -- let cex : Expr listty := cons (eint 22) ex
  -- let cex : Expr listty := cons (eint 22) ex

  let m0 := Expr.mmatch nil
    $ Match.cons "cons"
      (MatchCase.cons (.mk "x") $ MatchCase.cons (.mk "tail") $ MatchCase.nil $ eint 22)
      $ Match.cons "nil"
        (MatchCase.nil $ eint 44)
        $ Match.nil



  let mm := ~ ex : {
    #cons {x tail} : .int 22
    -- #nil {} : .int 33
  }

  listty



section Expr_fields

  @[match_pattern] def Expr.var (vr:Var t) := Expr.nullary (NullaryOp.var vr)
  @[match_pattern] def Expr.int n := Expr.nullary (.intlit n)
  @[match_pattern] def Expr.string s := Expr.nullary (.stringlit s)
  @[match_pattern] def Expr.ftag name (t:Ty) := Expr.nullary (.ftag name t)
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
      | .fn n => s!"@{n} {e.repr}"
      | .as t => s!"{e.repr}"
    | .binary op a b => match op with
      | .arith op => s!"({op} {a.repr} {b.repr})"
      | .app => s!"({a.repr} {b.repr})"
      | .sup n => s!"&{n}\{{a.repr} {b.repr}}"
      | .nsup => s!"&\{{a.repr} {b.repr}}"
      | .dub n x y => s!"!&{n}\{{x.name} {y.name}}={a.repr} {b.repr}"
      | .lett v => s!"! {v.name} = {a.repr} {b.repr}"
    | @Expr.data a n i => s!"#{(a.adt.get n).name} {n} \{{i.repr}}"
    | .mmatch x m => s!"~({x.repr})\{{m.repr}}"


  instance : Repr (Expr t) where reprPrec e _ := e.repr

  def Instance.repr (i:Instance a vs) : String :=
    match i with
    | .nil => ""
    | .cons _ x rest => s!"{x.repr} {rest.repr}"

  def Match.Case.repr (m: Match.Case a vs res) : String :=
    match m with
    | .nil e => "} : " ++ e.repr
    | .cons vr rest => s!"{vr.name} {rest.repr}"

  def Match.repr (m:Match a vs res) : String :=
    match m with
    | .nil => ""
    | @Match.cons a res xs v s rest => s!"\n#{v.name}\{{s.repr} {rest.repr}"

end



-- declare_syntax_cat match_case
-- syntax "#" ident "{" ident* "}" ":" term : match_case


-- macro "~" argument:term  ":" "{" arms:match_case+ "}" : term => do

--   let mut matcher ← `(Match.nil)
--   for arm in arms.reverse do
--     match arm with
--     |  `(match_case | # $variantname { $vars*  } : $bod) =>
--       matcher ← `(Match.named.cons
--         $(ident2stringlit variantname)
--         (by decide)
--         $(← vars.foldrM (fun (var: (Lean.TSyntax `ident)) acc => do

--         let ss := var.getId.toString

--         return ← `(
--           let $var := newVar $(ident2stringlit var);
--           Match.Case.cons $var
--           (let $var := Expr.var $var;
--           $acc))) ((← `(Match.Case.nil $bod))))
--         $matcher)
--     | _ => Lean.Macro.throwUnsupported

--   return ← `(Expr.mmatch $argument $matcher)


mutual

  def Expr.replace (v v':String): (e:Expr b) -> Expr b
    | .var vr => .var (if vr.name == v then newVar v' else vr)
    | .lam a e => .lam a (if a.name == v then e else e.replace v v')
    | .unary op e => .unary op (e.replace v v')
    | .binary op a b => .binary op (a.replace v v') (b.replace v v')
    | .data ad n i => .data ad n $ i.replace v v'
    | .mmatch x m => .mmatch (x.replace v v') m
    | k => k

  def Instance.replace (v v':String):
    (i:Instance a vs) -> Instance a vs
    | .nil => .nil
    | .cons tv x rest => .cons tv (x.replace v v') $ rest.replace v v'

  def Match.Case.replace (v v': String) :
    (m:Match.Case a vs res) -> Match.Case a vs res
    | .nil e => .nil (e.replace v v')
    | .cons vr rest => .cons (if vr.name == v then newVar v' else vr) $ rest.replace v v'

  def Match.replace(v v':String) :
    (m:Match a vs res) -> Match a vs res
    | .nil => .nil
    | .cons x rest => .cons (x.replace v v') $ rest.replace v v'

  def Expr.resolve  {s} (c: List TypedVar) (a: Expr ta) (b: Expr tb) (fn :Expr ta -> Expr tb -> Expr s) : Expr s :=
    match c with
    | [] => fn a b
    | c::cs =>
      let (c', c'') := (c.v.2 ++ "1", c.v.2 ++ "2")
      Expr.dub 0 (newVar c') (newVar c'') (Expr.var $ @Var.mk c.v.1 c.v.2)
      $ .resolve cs (a.replace c.v.2 c') (b.replace c.v.2 c'') fn


  def Expr.linearize : (e:Expr b) -> Expr b × List TypedVar
    | .var vr => (.var vr, [TypedVar.mk vr])
    | .lam vr a =>
      let (a, as) := a.linearize
      (.lam vr a, as.filter (. != (TypedVar.mk vr)))
    | .unary op a =>
      let (a, as) := a.linearize
      (.unary op a, as)
    | .binary op a b =>
      let (a, as) := a.linearize
      let (b, bs) := b.linearize
      let fn := fun a b => Expr.binary op a b
      (.resolve (as.filter (bs.contains ·)) a b fn, bs ++ as.filter (! bs.contains ·))
    | .data ad n i =>
      let (i, xs, rtd) := i.linearize
      let ex := rtd.foldl (fun x c =>
        Expr.dub 0
          (newVar (c.v.2 ++ "1"))
          (newVar (c.v.2 ++ "2")) (.var $ c.var) x) (Expr.data ad n i)
      (ex, xs)
    | .mmatch x m =>
      let (x, xs) := x.linearize
      let (m, rs, os) := m.linearize
      let collisions := xs.filter (rs.contains ·)
      let (x, m) := collisions.foldl (fun (x, m) c =>
        (x.replace c.name $ c.name ++ "1", m.replace c.name $ c.name ++ "2")) (x, m)
      let ex := (collisions ++ os).foldl (fun x c =>
        Expr.dub 0
          (newVar (c.v.2 ++ "1"))
          (newVar (c.v.2 ++ "2")) (.var $ c.var) x) $ Expr.mmatch x m
      (ex, xs ++ rs.filter (! xs.contains ·))
    | k => (k, [])

  def Instance.linearize : (i:Instance a vs) -> Instance a vs × List TypedVar × List TypedVar
    | .nil => (.nil, .nil, .nil)
    | .cons tv x rest =>
      let (x, xs) := x.linearize
      let (r, rs, rtd) := rest.linearize
      let collisions := xs.filter (rs.contains ·)
      let alls := rs ++ xs.filter (! rs.contains ·)
      let (x,r) := collisions.foldl (fun (x,r) c =>
        (x.replace c.name $ c.name ++ "1", r.replace c.name $ c.name ++ "2")) (x,r)
      (.cons tv x r, alls, rtd ++ collisions.filter (! rtd.contains ·))

  def Match.Case.linearize : (m:Match.Case a vs res) -> Match.Case a vs res × List TypedVar
    | .nil e =>
      let (e, es) := e.linearize
      (.nil e, es)
    | .cons x rest =>
      let (rest, xs) := rest.linearize
      (.cons x rest, xs.filter (. != (.mk x)))

  def Match.linearize : (m:Match a vs res) -> Match a vs res × List TypedVar × List TypedVar
    | .nil => (.nil, [], [])
    | .cons x rest =>
      let (x, xs) := x.linearize
      let (rest, rs, os) := rest.linearize
      let collisions := xs.filter (rs.contains ·)
      let (x, rest) := collisions.foldl
        (fun (x, r) c => (x.replace c.name $ c.name ++ "1", r.replace c.name $ c.name ++ "2"))
        (x,rest)
      (.cons x rest, xs ++ rs.filter (! xs.contains ·), collisions ++ os.filter (! xs.contains ·))

  def Expr.collect (m:Std.HashMap String String) : (e:Expr t) -> Std.HashMap String String
    | .fn name e => e.collect $ m.insert ("@" ++ name)  ("@" ++ name ++ "=" ++ e.repr)
    | .data ad n i => i.collect $ m.insert ("data " ++ ad.name) (ad.repr)
    | .mmatch x mt => x.collect $ mt.collect m
    | .unary op e => e.collect m
    | .binary op a b => a.collect (b.collect m)
    | _ => m

  def Instance.collect (m:Std.HashMap String String) : (i:Instance a vs) -> Std.HashMap String String
    | .nil => m
    | .cons df x res => x.collect $ res.collect m

  def Match.Case.collect (m:Std.HashMap String String) : (m:Match.Case a vs res) -> Std.HashMap String String
    | .nil e => e.collect m
    | .cons vr rest => rest.collect m

  def Match.collect (m:Std.HashMap String String) : (m:Match a vs res) -> Std.HashMap String String
    | .nil => m
    | .cons x rest => x.collect $ rest.collect m

end


inductive HVM_programm | mk : String -> HVM_programm

instance: Repr HVM_programm where reprPrec prg _ := match prg with | .mk s => s

def compile (e:Expr t) : HVM_programm :=
  let k := e.linearize.fst
  let m := k.collect Std.HashMap.empty
  .mk $ "\n\n".intercalate m.values



section notations


  def liststuff :=

    data list (a) {
      #Cons{h:a tail:self}
      #Nil{}
    }
    (list, fun a => @Cons a, fun a => @Nil a)

  def list := liststuff.1
  def Cons {a} : (Expr a) -> (Expr (list a) ) -> Expr (list a)  := liststuff.2.1 a
  def Nil {a} : Expr (list a) := liststuff.2.2 a

  infixr:56 "->" => arrow

  macro "@" n:ident ":" typ:term:50 "; " body:term:50 : term=> `(let $n := Expr.ftag $(Lean.quote (n.getId.toString)) $typ; $body)
  macro "@" n:ident "=" val:term:50 "; " body:term:50 : term=> `(let $n := Expr.fn $(Lean.quote (n.getId.toString)) $val; $body)
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

  macro:50 "!" vr:ident "=" val:term:50 ";" bod:term:50 : term =>
    `(
      let $vr := newVar $(ident2stringlit vr);
      Expr.let $vr $val (
      let $vr := Expr.var $vr;
      $bod
      ))

  declare_syntax_cat binder
  syntax ident : binder
  syntax "("ident ":" term")" : binder

  -- macro "(binder| " x:binder ")" : term =>  match x with
  --   | `(binder| $x:ident) => `(
  --     let vr := newVar $(Lean.quote (x.getId.toString));
  --     (vr, Expr.var vr))
  --   | `(binder| $x:ident : $t:term) => `(
  --     let vr := @Var.mk $t $(Lean.quote (x.getId.toString));
  --     (vr, Expr.var vr))
  --   | _ => Lean.Macro.throwUnsupported


  macro:50 "&" l:num "{" a:term:50 "," b:term:50  "}" : term => `(Expr.sup $l $a $b)
  macro:50 "&" "{" a:term:50 "," b:term:50  "}" : term => `(Expr.nsup $a $b)
  macro:50 a:term:50 "+" b:term:51 : term => `(Expr.arith "+" $a $b)
  macro:50 a:term:50 "-" b:term:51 : term => `(Expr.arith "-" $a $b)
  macro:60 a:term:60 "*" b:term:61 : term => `(Expr.arith "*" $a $b)
  macro:60 a:term:60 "/" b:term:61 : term => `(Expr.arith "/" $a $b)
  macro:60 "**" :term => `(Expr.eraser)

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



  -- macro:50 "lam" xs:binder+ "=>" body:term : term => do return ← xs.foldrM (fun x acc => `(lam $x => $acc)) (← `($body))

  macro "@" id:ident "(" args:binder* ")" "=" bod:term ";" rest:term : term =>
    do
    let fn := (← args.foldrM (fun arg acc => `(lam $arg => $acc)) (← `($bod)))
    return (← `(
    let $id := Expr.fn $(Lean.Syntax.mkStrLit id.getId.toString) ($fn)
    $rest))

  macro "(" a:ident b:ident ")" : term => `(Expr.app $a $b)
  -- macro "(" a:ident b:term ")" : term => `(Expr.app $a $b)
  -- macro "(" a:term b:ident ")" : term => `(Expr.app $a $b)
  -- macro "(" a:term "(" b:term ")"")" : term => `(Expr.app $a $b)
  -- macro "(" "(" a:term ")" b:term ")" : term => `(Expr.app $a $b)

  infixl:56 "•" => Expr.app

  macro "[" a:term,* "]" : term => do return ← a.getElems.foldrM (fun x acc => `(Cons $x $acc)) (← `(Nil))



end notations



#eval !x = #22; x


#check
  data list () {
    #CONS{h:int tail:self}
    #NIL{}
  }

  let e : Expr int :=
    .mmatch NIL
    $ .cons (.cons (.mk "h") $ .cons (.mk "t") $ .nil $ .int 22)
    $ .cons (.nil $ .int 33)
    Match.nil

  e



#eval
  data list () {
    #CONS{h:int tail:self}
    #NIL{}
  }

  let matcher := Match.named.cons "CONS" (by decide) (Match.Case.cons (.mk "h") $ .cons (.mk "t") $ .nil $ .int 22)
    $ Match.named.cons "NIL" (by decide) (.nil $ .int 33)
    Match.nil


  let getVariNames {a}{vs}{r} (m : Match a vs r) := vs.map (fun v => v.name)

  let h : getVariNames matcher = ["CONS", "NIL"] := by decide

  let e : Expr int :=
    .mmatch NIL matcher

  e



#eval

  data list (a) {
    #CONS{h:a tail:self}
    #NIL{}
  }

  -- let a{t}
  --   : Ty.adt t
  --   := list

  let getadt {a:Adt} : Expr (adt a) -> Adt := fun e => a
  let ad := getadt (@NIL int)
  22




#eval

  data list (a) {
    #CONS{h:a tail:self}
    #NIL{}
  }

  let mm : Expr (int) :=
    Expr.mmatch (@NIL int)
    $ Match.cons
      (Match.Case.cons (.mk "h") $ Match.Case.cons (.mk "t") $ Match.Case.nil $ .int 22)
    $ Match.cons
      (Match.Case.nil $ .int 33)
    Match.nil

  let getadt {a:Adt} : Expr (Ty.adt a) -> Adt := fun e => a
  let listadt := getadt (@NIL int)
  let cvari : Variant := listadt.variants[@Fin.mk 2 0 (by decide)]
  let nvari : Variant := listadt.variants[@Fin.mk 2 1 (by decide)]

  let matcher
    : Match (listadt) [nvari, cvari] int
    :=
    Match.cons
      (Match.Case.nil $ .int 33)
    $ Match.cons
      (Match.Case.cons (.mk "h") $ Match.Case.cons (.mk "t") $ Match.Case.nil $ .int 22)
    Match.nil

  let um : Expr (int) :=
    Expr.umatch (@NIL int)
    $ matcher

  mm


#check

  data list (a) {
    #CONS{h:a tail:self}
    #NIL{}
  }

  let ls:= CONS (Expr.int 22) NIL

  let mt := ~ ls : {
    #CONS{h tail} :
      !&0 {a b} = h as int;
      a
    #NIL{} : .int 33
  }

  compile $ .fn "main" mt




#check
  let a : Expr int := #22

  let r := a + a

  @fn = lam a => a + a;

  @fnn = lam a : int => a;

  22


#eval

  data union (a) {
    #A{v:a}
    #B{v:string}
  }

  data listorint () {
    #orint{v: int}
    #orstr{v: string}
  }

  let a := A (.int 22)
  let b := B (.string "hello")

  let ffn := fun x => x ++ "ok"
  let x := "okok"
  let res := (ffn) x

  (b : (Expr (union int)))




#eval
  data namedtuple (a b) {
    #NAMED{x:a y:b}
  }
  let a := (NAMED (.int 22) (.string "hello"))

  a
