import Lean

open Lean Elab Term

macro "$$" x:ident : term =>
  `( $(quote (x.getId.toString) ))

-- Example usage:
#eval $$hello  -- outputs: "hello"
def name := $$world
#eval name    -- outputs: "world"
