import HighScript



#eval
  data List (a) {
    #Cons{h:a tail:self}
    #Nil{}
  }

  List

def main :=

  data List (a) {
    #Cons{h:a tail:self}    -- mark recursive field with self
    #Nil{}
  }

  let a := #1;
  let b := #2;
  let c := #3;


  let abc := (Cons a (Cons b (Cons c Nil))) as (List int)

  @len : (List int) -> int;        -- to use recursion we need to declare the function first sadly
  @len = lam (l : (List int)) =>
    ~ l : {
      #Cons{h tail} : (#1 + (len • tail ))
      #Nil{} : #0
    };

  let list_match : Expr $ (List int) -> int :=
    lam l =>
      ~ l : {
        #Cons{h tail} : h
        #Nil{} : #0
      }

  let matched := (list_match abc)

  let lens := (len • abc)

  runmain (len abc)
