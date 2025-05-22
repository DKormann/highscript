import Lean
import Std.Data.HashMap

set_option linter.unusedVariables false


mutual

  inductive DataField
    | R: DataField
    | T: Ty -> DataField
  deriving BEq, Hashable, Repr

  structure Variant where
    name: String
    fields: List DataField
  deriving BEq, Hashable

  structure Adt where
    name: String
    variants: List Variant
  deriving BEq, Hashable, Repr

  inductive Ty
    | int
    | string
    | arrow: Ty -> Ty -> Ty
    | adt : Adt -> Ty
  deriving BEq, Hashable, Repr

end

mutual
  def Adt.decEq (adt1 adt2 : Adt) : Decidable (adt1 = adt2) :=
    match adt1, adt2 with
    | ⟨name1, ls1⟩, ⟨name2, ls2⟩ =>
      match decEq name1 name2 with
      | isFalse h =>
        let p := by intro heq; cases heq; contradiction
        isFalse (p)
      | isTrue h1 =>
        match Variant.List.decEq ls1 ls2 with
        | isFalse h => isFalse (by intro heq; cases heq; contradiction)
        | isTrue h2 => isTrue (by rw [h1, h2])

  def Ty.decEq (t1 t2 : Ty) : Decidable (t1 = t2) :=
    match t1, t2 with
    | .string, .string => isTrue (by rfl)
    | .arrow a1 b1, x =>
    match x with
      | .arrow a2 b2 =>
        match Ty.decEq a1 a2 with
        | isFalse h => isFalse (by intro heq; cases heq; contradiction)
        | isTrue h1 =>
          match Ty.decEq b1 b2 with
          | isFalse h => isFalse (by intro heq; cases heq; contradiction)
          | isTrue h2 => isTrue (by rw [h1, h2])
      | .int | .string | .adt _ => isFalse (by intro heq; contradiction)
    | .adt a1, x =>
      match x with
      |.adt a2 =>
        match Adt.decEq a1 a2 with
        | isFalse h => isFalse (by intro heq; cases heq; contradiction)
        | isTrue h => isTrue (by rw [h])
      | .int | .string | .arrow _ _ => isFalse (by intro heq; contradiction)
    | .int, x => match x with | .int => isTrue (by rfl) | .string | .arrow _ _ | .adt _ => isFalse (by intro heq; contradiction)
    | .string, x => match x with | .string => isTrue (by rfl) | .int | .arrow _ _ | .adt _ => isFalse (by intro heq; contradiction)

  def Variant.List.decEq (l1 l2: List Variant) : Decidable (l1 = l2) :=
    match l1, l2 with
    | [], [] => isTrue (by rfl)
    | x::xs, y::ys =>
      match Variant.decEq x y with
      | isFalse h => isFalse (by intro heq; cases heq; contradiction)
      | isTrue h1 =>
        match Variant.List.decEq xs ys with
        | isFalse h => isFalse (by intro heq; cases heq; contradiction)
        | isTrue h2 => isTrue (by rw [h1, h2])
    | [], x::xs | x::xs, [] => isFalse (by intro heq; cases heq)

  def Variant.decEq (v1 v2: Variant) : Decidable (v1 = v2) :=
    match v1, v2 with
    | ⟨name1, ls1⟩, ⟨name2, ls2⟩ =>
      match decEq name1 name2 with
      | isFalse h => isFalse (by intro heq; cases heq; contradiction)
      | isTrue h1 =>
        match DataField.List.decEq ls1 ls2 with
        | isFalse h => isFalse (by intro heq; cases heq; contradiction)
        | isTrue h2 => isTrue (by rw [h1, h2])

  def DataField.List.decEq (l1 l2: List DataField) : Decidable (l1 = l2) :=
    match l1, l2 with
    | [], [] => isTrue (by rfl)
    | x::xs, y::ys =>
      match DataField.decEq x y with
      | isFalse h => isFalse (by intro heq; cases heq; contradiction)
      | isTrue h1 =>
        match DataField.List.decEq xs ys with
        | isFalse h => isFalse (by intro heq; cases heq; contradiction)
        | isTrue h2 => isTrue (by rw [h1, h2])
    | [], x::xs | x::xs, [] => isFalse (by intro heq; cases heq)

  def DataField.decEq (df1 df2: DataField) : Decidable (df1 = df2) :=
    match df1, df2 with
    | .R, .R => isTrue (by rfl)
    | .T t1, .T t2 =>
      match Ty.decEq t1 t2 with
      | isFalse h => isFalse (by intro heq; cases heq; contradiction)
      | isTrue h => isTrue (by rw [h])
    | .R, .T _ | .T _, .R => isFalse (by intro heq; cases heq)

end

instance : DecidableEq Adt := Adt.decEq
instance : DecidableEq Ty := Ty.decEq
instance : DecidableEq (Variant) := Variant.decEq
instance : DecidableEq (List Variant) := Variant.List.decEq

instance : Repr  Variant where reprPrec v _ := s!"{v.name} \{{" ".intercalate $ v.fields.map (fun x => match x with | DataField.R => "self" | DataField.T t => "x")}}"

open Ty

def DataField.Ty (adt:Adt) : DataField → Ty
  | .T t => t
  | .R => .adt adt

def Ty.repr : Ty -> String
  | .int => "int"
  | .string => "string"
  | .arrow a b => s!"{a.repr} -> {b.repr}"
  | adt a => a.name

instance : Repr Ty where reprPrec t _ := t.repr

structure Var (t: Ty) where
  name: String
  deriving BEq, Hashable, Repr

def Var.ty (v:Var t) := t

def newVar (name:String) : Var t := ⟨name⟩

inductive TypedVar | mk : {ty:Ty} -> (Var ty) -> TypedVar deriving Hashable

def TypedVar.v (v:TypedVar) := match v with | TypedVar.mk v => (v.ty, v.name)
def TypedVar.var (v:TypedVar) : Var v.v.fst := @Var.mk v.v.1 v.v.2
def TypedVar.name x := (TypedVar.v x ).2
def TypedVar.ty x := (TypedVar.v x ).1


instance : BEq TypedVar where beq (a b: TypedVar) := a.name == b.name && a.ty == b.ty

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
    | lett : (Var t) -> BinaryOp a b b

  inductive Expr : Ty → Type
    | nullary : NullaryOp b -> Expr b
    | unary : UnaryOp a b -> Expr a -> Expr b
    | binary : BinaryOp a b c -> Expr a -> Expr b -> Expr c
    | data : (a:Adt) -> (n:Fin a.variants.length) -> (v: Instance a (a.variants[n].fields)) → Expr (.adt a)

    | mmatch: (x: Expr (adt a)) -> (Match a a.variants res) -> Expr res
    | umatch: (x: Expr (adt a)) ->
      (Match a vs res) ->
      (p: (a.variants.map (Variant.name)).all ((vs.map (Variant.name)).contains) := by decide) ->
      Expr res

  inductive Instance : (a: Adt) -> (v: List DataField) -> Type
    | nil : Instance a []
    | cons : (tv: DataField) -> (x: Expr (tv.Ty a)) -> (Instance a xs) -> Instance a (tv::xs)
  deriving Repr

  inductive Match : (a: Adt) -> (vs: List Variant) -> (res:Ty) -> Type
    | nil : Match a [] res
    | cons : {v:Variant} -> Match.Case a v.fields res -> Match a xs res -> Match a (v::xs) res

  inductive Match.Case : (a: Adt) -> (vs: List DataField) -> (res:Ty) -> Type
    | nil : (e:Expr res) -> Match.Case a [] res
    | cons {df} : Var (df.Ty a) -> Match.Case a xs res -> Match.Case a (df::xs) res

end


def Match.named.cons  {v:Variant} (name:String) (p: name = v.name := by decide) (x:Match.Case a v.fields res) (rest: Match a xs res):= Match.cons x rest

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
    | .nullary $ NullaryOp.intlit n => s!"{n}"
    | .nullary $ NullaryOp.stringlit s => s!"\"{s}\""
    | .nullary $ NullaryOp.var v => s!"{v.name}"
    | .nullary $ NullaryOp.ftag s t => s!"@{s}"
    | .unary (UnaryOp.lam v) e => s!"λ {v.name} {e.repr}"
    | .unary (UnaryOp.fn n) e => s!"@{n}"
    | .unary (UnaryOp.as t) e => s!"{e.repr}"
    | .binary op a b => match op with
      | .arith op => s!"({op} {a.repr} {b.repr})"
      | .app => s!"({a.repr} {b.repr})"
      | .sup n => s!"&{n}\{{a.repr} {b.repr}}"
      | .nsup => s!"&\{{a.repr} {b.repr}}"
      | .dub n x y => s!"!&{n}\{{x.name} {y.name}}={a.repr} f{b.repr}"
      | .lett v => s!"! {v.name} = {a.repr} {b.repr}"
    -- | .data c i => s!"#{(c.adt.variants[c.idx]).name} \{{i.repr}}"
    | .mmatch x m => s!"~({x.repr})\{{m.repr}}"
    | _ => s!"repr undefined"


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


def Adt.repr (adt: Adt) : String := s!"data {adt.name} \{{" ".intercalate $ adt.variants.map (fun v => s!"#{v.name}\{{" ".intercalate $ v.fields.map (fun x => match x with | DataField.R => "self" | DataField.T t => "x")}}")}}"
instance : Repr Adt where reprPrec adt _ := adt.repr

declare_syntax_cat typed_arg
syntax ident ":" ident : typed_arg

declare_syntax_cat construction
syntax "#" ident "{" typed_arg* "}" : construction

def ident2stringlit (x : Lean.TSyntax `ident) := Lean.Syntax.mkStrLit x.getId.toString

def ConstructorFn (adt: Adt) (ds : List DataField) : Type :=
  match ds with
  | [] => Expr (Ty.adt adt)
  | x::xs => (Expr $ x.Ty adt) -> ConstructorFn adt xs

structure Constructor where
  adt: Adt
  n: Fin adt.variants.length
  con: ConstructorFn adt adt.variants[n].fields

instance : Repr  Constructor  where reprPrec c _ := s!"CON {c.adt.name}.{c.n}"

def anyval {x:Type} (s:x) := (x, s)


#eval
  let fn := anyval fun x => x ++ "hee"
  fn.snd "ok"

macro "data" name:ident "(" typeargs:ident* ")" "{" ctrs:construction* "}" rest:term : term => do
  let mut ctrsdata := #[]
  for ctr in ctrs do
    match ctr with
    | `(construction| #$ctrname { $args* }) =>
      let mut arglist := #[]
      for arg in args do
        match arg with
        | `(typed_arg| $arg:ident : $ty:ident) => arglist := arglist.push (arg, ty)
        | _ => Lean.Macro.throwUnsupported
      ctrsdata := ctrsdata.push (ctrname, arglist)
    | _ => Lean.Macro.throwUnsupported

  let dattype := ←
  `($(← `(Adt.mk $(ident2stringlit name) $(← ctrsdata.foldrM
      (fun (ctrname, ctrargs) (acc:Lean.TSyntax `term) => do
        return ← `((Variant.mk $(ident2stringlit ctrname) $(← (ctrargs.foldrM
          (fun (arg, ty) acc => do return (<- `($(← if (ty.getId.toString) == "self" then `(DataField.R) else `(DataField.T $ty)) :: $acc)))
          (← `([]))
      ))) :: $acc))
      (← `([]))))));

  return ←
    `(
    let $name := $((← typeargs.foldrM (fun arg acc => `(fun $arg => $acc)) ((← `(Ty.adt $dattype)))));
    $(← ctrsdata.zipIdx.foldrM (fun ((ctrname, vargs), c) acc =>
      do
      let dattrep ← typeargs.reverse.foldrM (fun arg acc => do return ← `($acc $arg)) name;
      return ← `(
        let $ctrname := $((← typeargs.foldrM
          (fun (arg: Lean.TSyntax `ident) acc => do return ← if (arg.getId.toString) == "self" then `($acc) else `(fun {$arg : Ty} => $acc))
          (← ( do
            let n ← `(Fin.mk $(Lean.Syntax.mkNatLit c) (by decide)
            )
            let confn := (← vargs.foldrM
              (fun (arg, ty) acc => do return ← `(fun ($arg : Expr $((← if (ty.getId.toString) == "self" then `($dattrep) else `($ty)))) => $acc))
              (← `(
                let exp :Expr $ $dattrep :=
                  (Expr.data $dattype
                    $n
                    $(← vargs.foldrM
                      (fun (arg, ty) acc => do return ← `(Instance.cons $((← if (ty.getId.toString) == "self" then `(DataField.R) else `(DataField.T $ty))) $arg $acc))
                      (← `(Instance.nil))))
                exp
                )))
            let zuf ← `(Constructor.mk $dattype $n $confn)
            return zuf
          ))
        )); $acc )) (← `(
          $rest
        ))))




#eval
  data list () {
    #CONS{h:int tail:self}
    #NIL{}
  }

  let nl : Expr list := NIL.con

  let ls : Expr list := (CONS.con (.int 22) NIL.con)
  let ls : Expr list := (CONS.con (.int 22) ls)
  let ls : Expr list := (CONS.con (.int 22) ls)
  let ls : Expr list := (CONS.con (.int 22) ls)

  ls


macro "#" ctr:ident : term =>`(($ctr).con)

#check
  data list () {
    #CONS{h:int r:string }
    #NIL{}
  }

  (#CONS $ .int 22)



macro "#" ctr:ident "{" args:term,* "}" : term => do
  return ← (args.getElems).foldrM
    (fun arg acc => `($acc $arg))
    (←`($(ctr).con))
    -- (← `([]))


#check
  data list () {
    #CONS{h:int r:int }
    #NIL{}
  }

  let nl : Expr $ .adt CONS.adt := NIL.con

  let ls : Expr $ .adt CONS.adt := ( #CONS { (Expr.int 11), (Expr.int 22) } )

  ls



declare_syntax_cat match_case
syntax "#" ident "{" ident* "}" ":" term : match_case


macro "~" argument:term  ":" "{" arms:match_case+ "}" : term => do

  let mut matcher ← `(Match.nil)
  for arm in arms.reverse do
    match arm with
    |  `(match_case | # $variantname { $vars*  } : $bod) =>
      matcher ← `(Match.named.cons
        $(ident2stringlit variantname)
        (by decide)
        $(← vars.foldrM (fun (var: (Lean.TSyntax `ident)) acc => do

        let ss := var.getId.toString

        return ← `(
          let $var := newVar $(ident2stringlit var);
          Match.Case.cons $var
          (let $var := Expr.var $var;
          $acc))) ((← `(Match.Case.nil $bod))))
        $matcher)
    | _ => Lean.Macro.throwUnsupported

  return ← `(Expr.mmatch $argument $matcher)


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
    -- | .mmatch x m =>
      -- let (x, xs) := x.linearize
      -- let (m, rs, os) := m.linearize
      -- let collisions := xs.filter (rs.contains ·)
      -- let (x, m) := collisions.foldl (fun (x, m) c =>
      --   (x.replace c.name $ c.name ++ "1", m.replace c.name $ c.name ++ "2")) (x, m)
      -- let ex := (collisions ++ os).foldl (fun x c =>
      --   Expr.dub 0
      --     (newVar (c.v.2 ++ "1"))
      --     (newVar (c.v.2 ++ "2")) (.var $ c.var) x) $ Expr.mmatch x m
      -- (ex, xs ++ rs.filter (! xs.contains ·))
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
  let m := e.collect Std.HashMap.empty
  .mk $ "\n\n".intercalate m.values


section notations

  infixr:56 "->" => arrow

  macro "@" n:ident ":" typ:term:50 "; " body:term:50 : term=> `(let $n := Expr.ftag $(Lean.quote (n.getId.toString)) $typ; $body)
  macro "@" n:ident "=" val:term:50 "; " body:term:50 : term=> `(let $n := Expr.fn $(Lean.quote (n.getId.toString)) $val; $body)
  macro:100 "#" n:num : term => `(Expr.int $n)
  macro:100 "#" n:str : term => `(Expr.string $n)
  macro:50 v:term:50 "as" t:term:51 : term => `(Expr.astype $t $v)
  macro:50 "var" n:ident ":" t:term:50 ";" bod:term  : term => `(let $n :Var $t := newVar $(Lean.quote (n.getId.toString)); $bod)

  macro:50 "!" "&" l:num "{" a:ident b:ident  "}" "=" c:term:50 ";" d:term:50 : term =>
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

  macro:50 "&" l:num "{" a:term:50 b:term:50  "}" : term => `(Expr.sup $l $a $b)
  macro:50 "&" "{" a:term:50 b:term:50  "}" : term => `(Expr.nsup $a $b)
  macro:50 a:term:50 "+" b:term:51 : term => `(Expr.arith "+" $a $b)
  macro:50 a:term:50 "-" b:term:51 : term => `(Expr.arith "-" $a $b)
  macro:60 a:term:60 "*" b:term:61 : term => `(Expr.arith "*" $a $b)
  macro:60 a:term:60 "/" b:term:61 : term => `(Expr.arith "/" $a $b)




  macro:50 "lam" x:ident ":" t:term "=>" body:term : term => `(
    let $x := @Var.mk $t $(Lean.quote (x.getId.toString));
    let binder := (Expr.lam $x)
    let $x : Expr $t := Expr.var $x;
    (binder $body)
  )
  macro:50 "lam" x:ident "=>" body:term : term => `(
    let $x := newVar $(Lean.quote (x.getId.toString));
    let binder := (Expr.lam $x)
    let $x := Expr.var $x;
    (binder $body)
  )


  macro "(" a:ident b:ident ")" : term => `(Expr.app $a $b)
  -- macro "(" a:ident b:term ")" : term => `(Expr.app $a $b)
  -- macro "(" a:term b:ident ")" : term => `(Expr.app $a $b)
  -- macro "(" a:term "(" b:term ")"")" : term => `(Expr.app $a $b)
  -- macro "(" "(" a:term ")" b:term ")" : term => `(Expr.app $a $b)

  infixl:56 "•" => Expr.app


end notations




-- #check
--   data list () {
--     #CONS{h:int tail:self}
--     #NIL{}
--   }

--   let e : Expr int :=
--     .mmatch NIL
--     $ .cons (.cons (.mk "h") $ .cons (.mk "t") $ .nil $ .int 22)
--     $ .cons (.nil $ .int 33)
--     Match.nil

--   e



-- #eval
--   data list () {
--     #CONS{h:int tail:self}
--     #NIL{}
--   }

--   let matcher := Match.named.cons "CONS" (by decide) (Match.Case.cons (.mk "h") $ .cons (.mk "t") $ .nil $ .int 22)
--     $ Match.named.cons "NIL" (by decide) (.nil $ .int 33)
--     Match.nil


--   let getVariNames {a}{vs}{r} (m : Match a vs r) := vs.map (fun v => v.name)

--   let h : getVariNames matcher = ["CONS", "NIL"] := by decide

--   let e : Expr int :=
--     .mmatch NIL matcher

--   e



-- #eval

--   data list (a) {
--     #CONS{h:a tail:self}
--     #NIL{}
--   }

--   -- let a{t}
--   --   : Ty.adt t
--   --   := list

--   let getadt {a:Adt} : Expr (adt a) -> Adt := fun e => a
--   let ad := getadt (@NIL int)
--   22




-- #eval

--   data list (a) {
--     #CONS{h:a tail:self}
--     #NIL{}
--   }

--   let mm : Expr (int) :=
--     Expr.mmatch (@NIL int)
--     $ Match.cons
--       (Match.Case.cons (.mk "h") $ Match.Case.cons (.mk "t") $ Match.Case.nil $ .int 22)
--     $ Match.cons
--       (Match.Case.nil $ .int 33)
--     Match.nil

--   let getadt {a:Adt} : Expr (Ty.adt a) -> Adt := fun e => a
--   let listadt := getadt (@NIL int)
--   let cvari : Variant := listadt.variants[@Fin.mk 2 0 (by decide)]
--   let nvari : Variant := listadt.variants[@Fin.mk 2 1 (by decide)]

--   let matcher
--     : Match (listadt) [nvari, cvari] int
--     :=
--     Match.cons
--       (Match.Case.nil $ .int 33)
--     $ Match.cons
--       (Match.Case.cons (.mk "h") $ Match.Case.cons (.mk "t") $ Match.Case.nil $ .int 22)
--     Match.nil

--   let um : Expr (int) :=
--     Expr.umatch (@NIL int)
--     $ matcher

--   mm


-- #check

--   data list (a) {
--     #CONS{h:a tail:self}
--     #NIL{}
--   }

--   let ls:= CONS (Expr.int 22) NIL

--   let mt := ~ ls : {
--     #CONS{h tail} :
--       !&0 {a b} = h as int;
--       a
--     #NIL{} : .int 33
--   }

--   compile $ .fn "main" mt




-- #check
--   let a : Expr int := #22

--   let r := a + a

--   @fn = lam a => a + a;

--   @fnn = lam a : int => a;

--   22


-- #eval

--   data union (a) {
--     #A{v:a}
--     #B{v:string}
--   }

--   data listorint () {
--     #orint{v: int}
--     #orstr{v: string}
--   }

--   let a := A (.int 22)

--   let b := B (.string "hello")


--   let ffn := fun x => x ++ "ok"
--   let x := "okok"
--   let res := (ffn) x

--   (b : (Expr (union int)))




-- #eval
--   data namedtuple (a b) {
--     #NAMED{x:a y:b}
--   }
--   let a := (NAMED (.int 22) (.string "hello"))

--   a
