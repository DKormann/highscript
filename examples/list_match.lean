import HighScript

def main :=

  data list {
    #CONS{h rec}    -- create mark recursive field with rec
    #NIL{}
  }

  let a := #1;
  let b := #2;
  let c := #3;

  let nil := NIL;

  let abc := (CONS a (CONS b (CONS c NIL))) as list [int]

  let list_match : Expr $ (list [int]) -> int :=

    lam l =>
      ~ l : {
        #CONS{h tail} : Expr.var $ newVar "h"
        #NIL{} : #0
      }

  let res := (list_match • abc)

  runmain res
