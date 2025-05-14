import HighScript


-- macro "(" a:term:70 "(" b:term:71 ")" ")" : term => `(Expr.app $a $b)



declare_syntax_cat expr
syntax "okok" ident "endd" : expr

syntax "exp::" expr : term

syntax expr : term

macro_rules
  | `(expr| okok $x endd) => `(fun $x => $x)
  | `(exp:: $x) => `(expr| $x)


def k: Nat -> Nat := exp:: okok ff endd

def main :=

  let f : Expr (int -> int) := lam x -> (x * #2);
  let add : Expr (int -> int -> int) := lam x -> lam y  -> x + y;


  runmain (add • (f • #10) • #50)
