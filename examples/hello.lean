import HighScript


def main :=
  @main = lam x -> x as (int -> int);
  runHVM main
