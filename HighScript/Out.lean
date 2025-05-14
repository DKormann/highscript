
import HighScript.DSL

def writeHVM (fn:String) (e: Expr s) :IO Unit := do

  (← IO.FS.Handle.mk fn IO.FS.Mode.write).putStr $ match (compile e) with | .mk s => s

def runHVM (e:Expr s) : IO Unit := do
  writeHVM "out.hvm" e
  IO.print (← IO.Process.output {cmd := "hvm", args := #["run", "out.hvm", "-C10"], }).stdout
