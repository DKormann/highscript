
import HighScript


-- macro "@" id:ident "(" args:ident* ")" "=" bod:term ";" rest:term : term =>
--   do
--   let fn := (← args.foldrM (fun arg acc => `(lam $arg => $acc)) (← `($bod)))
--   return (← `(
--   let $id := Expr.fn $(Lean.Syntax.mkStrLit id.getId.toString) ($fn)
--   $rest))


-- #check
--   @nand(a b) = (a + b);
--   -- let f := lam a => a + a;
--   -- let nn := Expr.fn "nand" $ lam a => a + a;
--   nand


def main :=


  @nand = (lam a => lam b => (#1 - (a * b)));

  @nand (a b) = Cons a $ Cons b $ Nil as list int;

  @nand (a b) = [a, b as int];

  @sup = &{#22, #33};

  @l2sup : (list int) -> int;
  @l2sup (ls) =
    ~(ls as list int):{
      #Cons{h t}: &{(h as int), (l2sup t)}
      #Nil{}: **
    };

  runmain (l2sup • (nand • #1 • #2))
