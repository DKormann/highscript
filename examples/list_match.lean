import HighScript




def list: Adt :=
  data list (a) {
    #CONS{h:a tail:self}    -- create mark recursive field with rec
    #NIL{}
  }
  list int


def main :=

  data list (a) {
    #CONS{h:a tail:self}    -- create mark recursive field with rec
    #NIL{}
  }

  let a := #1;
  let b := #2;
  let c := #3;


  let abc := (CONS a (CONS b (CONS c NIL))) as (adt $ list int)

  @len : (adt (list int)) -> int;        -- to use recursion we need to declare the function first sadly
  @len = lam l : adt (list int) =>
    ~ l : {
      #CONS{h tail} : #1 + len • tail
      #NIL{} : #0
    };

  let list_match : Expr $ adt (list int) -> int :=

    lam l =>
      ~ l : {
        #CONS{h tail} : h
        #NIL{} : #0
      }

  let matched := (list_match • abc)

  let lens := (len • abc)

  -- runmain $ lens + (len • NIL)
  runmain abc
