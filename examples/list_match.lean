import HighScript




def list: Adt :=
  data list {
    #CONS{h tail}    -- create mark recursive field with rec
    #NIL{}
  }
  list

#eval list

#eval Repr.reprPrec (arrow int Ty.int) 0




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

  @len : (list[int]) -> int;        -- to use recursion we need to declare the function first sadly
  @len = lam l : list[int] =>
    ~ l : {
      #CONS{h tail} : #1 + len • tail
      #NIL{} : #0
    };

  let list_match : Expr $ (list [int]) -> int :=

    lam l =>
      ~ l : {
        #CONS{h tail} : h
        #NIL{} : #0
      }

  let matched := (list_match • abc)

  let lens := (len • abc)

  runmain $ lens + (len • NIL)
