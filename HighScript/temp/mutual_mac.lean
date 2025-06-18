

import Lean

open Lean Elab Term Macro

declare_syntax_cat core
syntax num ":" core : core
syntax num : core


-- STEP 1: define syntax term
syntax "#mac " core : term

-- STEP 2: define elab emitting syntax
elab "myElab" c:core : term => do
  elabTerm (← `(#mac $c)) none

-- STEP 3: define macro for syntax
macro_rules
  | `(#mac $c:core) =>
    match c with
      | `(core| $n:num ) => do `([$n + 1])
      | `(core| $n:num : $rest:core ) => do
        let res ←  `(($n+2) :: myElab $rest)
        return res
      | _ => throwUnsupported




#eval myElab 22 : 2 : 2
