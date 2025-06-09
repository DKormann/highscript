import HighScript


def main : IO Unit :=

  @add x y = x + y;

  @fn x = add • x • x;

  runmain (fn • (#10))
