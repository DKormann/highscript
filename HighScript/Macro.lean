import Lean
import HighScript.DSL

open Lean Elab Command Term Meta




declare_syntax_cat high_script

syntax num : high_script
syntax ident : high_script
syntax "lett" ident " = " high_script "in" high_script  : high_script

macro "[hh|" ex:high_script "]" :term =>
  match ex with
  | `(high_script| $n:num) => `($n)

  | `(high_script| lett $vr:ident = $val:high_script in $body:high_script) =>
    `((22+33))

  | _ => Lean.Macro.throwUnsupported



-- #eval [hh| lett x = 20 in x]





@[command_elab Lean.Parser.Command.check] def mySpecialCheck : CommandElab := fun stx => do
  if let some str := stx[1].isStrLit? then
    logInfo s!"Specially elaborated string literal!: {str} : String"

  else
    throwUnsupportedSyntax


#check "heeey"
