import HighScript.DSL
import HighScript.Out

export Ty (int string arrow)


-- macro "@hvm" "=" e:term : command =>
--   `(def main : IO Unit :=
--     runHVM (Expr.fn "main" ($e))
--   )


macro "@@" fn:ident e:term : command =>
  `(
    def $fn : IO Unit :=
    runHVM (Expr.fn "main" ($e))
  )


def runmain (e:Expr t) := runHVM $ Expr.fn "main" e
