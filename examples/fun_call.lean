import HighScript


def main : IO Unit := do
  @add = lam x -> lam y -> (x + y); -- lean's powerfull type inference helps us out here
  @fn = lam x -> ((@add (x)) (x));  -- compiler will duplicate x here for us
  @main = (fn (#10));               -- literals need to be wrapped with #
  runHVM main
