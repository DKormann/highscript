
inductive Notin :Nat -> Type
  | nil : Notin x
  | cons : (n: Nat) -> (n ≠ x) -> (Notin x) -> Notin x


def push (l:Notin x) (n:Nat) : Notin x :=
  if h : n ≠ x then Notin.cons n h l
  else l


#eval
  let g : Notin 3 := Notin.cons 1 (by decide) Notin.nil
  g

def ListNotContains (x : Nat) := { l : List Nat // x ∉ l }

open List

def ex : ListNotContains 3 :=
  ⟨[1, 2, 4], by decide⟩

def ListNoDup := { l : List Nat // l.Nodup}

def ex2 : ListNoDup := ⟨[1, 2, 4], by decide⟩

def ListNoDup.push (l:ListNoDup) (x:Nat) : ListNoDup :=
  if h : x ∉ l.val then ⟨x :: l.val, by simp [h, l.property]⟩
  else l


#eval ex2.push 3

inductive TreeNoDup : List Nat -> Type
  | leaf : (x:Nat) -> TreeNoDup [x]
  | node : (a: TreeNoDup as) -> (b: TreeNoDup bs)
    -> (¬ ∃ (x:Nat), x ∈ as ∧ x ∈ bs)
    -> TreeNoDup (as ++ bs)
open TreeNoDup



def TreeNoDup.push  (a:TreeNoDup as)  (n: Nat) : (as':List Nat) × TreeNoDup as' :=

  if h: n ∉ as then ⟨as ++ [n], TreeNoDup.node a (TreeNoDup.leaf n) (by simp [h])⟩

  else ⟨as, a⟩


-- def TreeNoDup.forcepush (a:TreeNoDup as) (n: Nat) : (as':List Nat) × TreeNoDup as' :=



def TreeNoDup.trymerge (a:TreeNoDup as) (b: TreeNoDup bs) : (cs : List Nat) × TreeNoDup cs :=
  if h: ∃ (x:Nat), x ∈ as ∧ x ∈ bs then ⟨as, a⟩
  else ⟨as ++ bs, TreeNoDup.node a b (by simp [h])⟩


def reprTree {as : List Nat} : TreeNoDup as → String
  | TreeNoDup.leaf x => toString x
  | TreeNoDup.node a b _ => "(" ++ reprTree a ++ "," ++ reprTree b ++ ")"

instance {as : List Nat} : Repr (TreeNoDup as) where reprPrec t _ := reprTree t

#eval TreeNoDup.node (TreeNoDup.leaf 1) (node (leaf 2) (leaf 3) (by decide)) (by decide)
