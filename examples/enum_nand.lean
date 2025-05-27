
-- this is work in progress of a simple enumerator
import HighScript

set_option linter.unusedVariables false


def main :=

  data bool {#True #False}

  data myterm  { #Term {term:int id:int}}

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


  @rootTerm(n) = (Term n n);

  @lin ((a:int) b rest) =
    -- let a := (a as int);
   ~(b as list int):{
    #Nil{} : rest
    #Cons{h t} : #22
  }as int;


  runmain (~False:{
    #False : (Term (#33) (#0))
    #True : rootTerm • #22
  })
