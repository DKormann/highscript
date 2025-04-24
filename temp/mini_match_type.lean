

inductive VecList : List Nat -> Type
| nil : VecList []
| cons {n: Nat} {ns: List Nat} (x: Fin n) (xs: VecList ns) : VecList (n::ns)


def eval := 22


inductive Ty
| int
| string
| arrow: Ty-> Ty -> Ty
| adt: String -> List Ty -> Ty
open Ty


structure Var (t: Ty) where
name: String

inductive Expr: Ty -> Type
| var: (v : Var t) -> Expr t
| intlit : Nat -> Expr int
| stringlit : String -> Expr string
| lam {a b : Ty} (param: Var a) (body: Expr b) : Expr (arrow a b)
| app {a b : Ty} (f: Expr (arrow a b)) (x: Expr a) : Expr b
open Expr



inductive Ma: (List Ty) -> (o:Ty) -> Type
| nil {o}: Ma [] o
| cons {o} {as: List Ty} {i} (x: Expr (arrow i o)) (vs: Ma as o) : Ma (i::as) o


#eval
  let xi: Var int := ⟨"x"⟩
  let xs: Var string := ⟨"y"⟩

  let ma: Ma [int, string] int :=
    Ma.cons (lam xi (var xi))
    (Ma.cons (lam xs (intlit 33))
    Ma.nil)
  22
