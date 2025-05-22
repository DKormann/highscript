import HighScript



def main :=

  -- declaring a lambda
  let f := lam (x : int) => x; -- use type annotations when needed

  -- declaring a function
  @add(x y) = x + y;

  runmain (add • (f • #10) • #50)                   -- use • for explicit application (often not needed)
