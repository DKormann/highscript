import HighScript


def main  : IO Unit := do

  @main = lam x -> x as (int -> int);

  runHVM main
