import HighScript


-- macro "(" a:term:70 "(" b:term:71 ")" ")" : term => `(Expr.app $a $b)


def main :=

  let f : Expr (int -> int) := lam x -> (x * #2);
  let add : Expr (int -> int -> int) := lam x -> lam y  -> x + y;


  runmain (add • (f • #10) • #50)
