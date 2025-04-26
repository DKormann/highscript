
-- experiments with dependently typed pattern match generators


inductive Vec : (k : Nat) → Type where
  | nil : Vec 0
  | cons : Nat -> (Vec n) → Vec (n + 1)

def vpr : (x : Vec n) → String | Vec.nil => "" | Vec.cons x xs => s!"{x} {vpr xs}"
instance : Repr (Vec n) where reprPrec x _ := s!"[ {vpr x}]"

def Vmk : (x : List Nat) → Vec x.length
  | [] => Vec.nil
  | x::xs => Vec.cons x (Vmk xs)

inductive Vecs :  (d : Vec n) → Type where
  | nil : Vecs  (Vec.nil)
  | cons : (xs : Vec x) → (rs: Vecs k) → Vecs (Vec.cons x k)
  deriving Repr

def vx : (x:List (List Nat)) → List ((n:Nat) × Vec n )
  | [] => []
  | x::xs => ⟨x.length,Vmk x⟩ :: (vx xs)

def vxs : (x: List ((n:Nat) × Vec n)) → Vecs (Vmk (x.map (λ p => p.1)))
  | [] => Vecs.nil
  | ⟨_, x⟩::xs => Vecs.cons x (vxs xs)

def Vxs (x:List (List Nat)) := (vxs (vx x))




#eval
  let x : Vecs (Vmk [2, 2, 3]) := Vxs [[2, 3], [2, 5], [2, 5, 7]]
  x

#eval (44 : Nat)




def langt : (Vec (2 * 2)) := Vmk [1, 2, 3, 4]

def langtt := (Vecs (Vmk ([2, 2, 3].map (λ x => x * 2))))


-- structure Nwrap {t:Type} (n: t) where val := n

inductive Tvar where
  | Rec : Tvar
  | T : Type -> Tvar

structure Vari where
  name : String
  fields: List ((String) × Tvar)

structure Dat where
  name : String
  fields : List Tvar


def acceptor (a b: Type) : Type := ∀ (_: a), b

def sacceptor : (a : (List Type)) -> (b: Type) -> Type
  | [], b => b
  | a::as, b => sacceptor as (∀ (_: a), b)

def arith := sacceptor [Nat, Nat] Nat

def fn : arith := λx y => x + y

structure Arm (v: Vari) where
