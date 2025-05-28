
-- this is work in progress of a simple enumerator
import HighScript

set_option linter.unusedVariables false


def main :=

  data bool{
    #True
    #False
  }

  data term {
    #Term bod:int id:int
  }

  @nand = (lam a => lam b => (#1 - (a * b)));

  @nand a b = Cons a $ Cons b $ Nil as list int;

  @nand a b = [a, b as int];

  @sup = &{#22, #33};

  @l2sup : (list int) -> int;
  @l2sup ls =
    ~(ls as list int) {
      #Cons h t: &{(h as int), l2sup • t}
      #Nil: **
    };



  @rootTerm n = (Term n n);

  @lin (a:int) (b: list int) rest =

   ~b{
    #Nil : rest
    #Cons h t : #22
  }as int;


  let iff {u:Ty} t (a:Expr u) (b:Expr u) :=
    ~ (t as bool) {
      #True : a
      #False : b
    };


  runmain $ iff False (rootTerm #10) (rootTerm #20)
