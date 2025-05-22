
-- this is work in progress of a simple enumerator

import HighScript


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


  data myterm () { #Term {term:int id:int}}

  @rootTerm(n) =
    -- ! &0{n1, n2} = n;
    (Term n n);
    -- (n + n);

  -- @lin(a b rest) =


  -- runmain (l2sup • (nand • #1 • #2))
  runmain (rootTerm • #22)
