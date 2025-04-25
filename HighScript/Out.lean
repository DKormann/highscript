
import HighScript.DSP

def writeHVM (fn:String) (e: Expr s) :IO Unit := do
  (← IO.FS.Handle.mk fn IO.FS.Mode.write).putStr (compile e ++ "\n")

def runHVM (e:Expr s) : IO Unit := do
  writeHVM "temp/script.hvm" e
  IO.print (← IO.Process.output {cmd := "hvm", args := #["run", "script.hvm", "-C1"], }).stdout
