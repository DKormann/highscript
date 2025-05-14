import HighScript



def main :=

  let f := (lam x : int => x as int) as int -> int; -- use type annotations when needed

  let add := lam x => lam y => x + y;

  runmain (add • (f • #10) • #50)                   -- use • for explicit application (often not needed)
