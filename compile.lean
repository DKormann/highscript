


inductive AST
| num: Nat -> AST
| add: AST -> AST -> AST
deriving Repr

open AST


-- class ToAST (α : Type) where
--   toAST : α → AST

-- instance : ToAST AST where
--   toAST a := a

-- instance : ToAST Nat where
--   toAST n := num n

-- instance [ToAST α] [ToAST β] : HAdd α β AST where
--   hAdd a b := add (ToAST.toAST a) (ToAST.toAST b)

-- #eval add (1 + 2) ((num 0) + (num 3)) -- OK: uses your instance, output: add (num 1) (num 2) (add (num 0) (num 3))

-- instance : HAdd AST AST AST where
--   hAdd a b := add a b


notation "{" x "}" => num x
notation "&{" x "}" => 22

infixl:65 " + " => add

#eval {&{5}}

def main : IO Unit := do
  (← IO.FS.Handle.mk "script.hvm" IO.FS.Mode.write).putStr ("@main = " ++ eval prog ++ "\n")
  IO.print (← IO.Process.output {cmd := "hvm", args := #["run", "script.hvm", "-C1"], }).stdout
