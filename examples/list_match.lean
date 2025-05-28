import HighScript

def create (a:Ty):=
  data List {
    #Cons h:a tail:self
    #Nil
  }

  List

def main :=

data List a{
  #Cons h:a tail:self
  #Nil
}

  let a := #1;
  let b := #2;
  let c := #3;

  runmain $

  ! x = Cons (#22) Nil;
  ! abc = (Cons a (Cons b (Cons c Nil)));

  @gethead lst = ~(lst as List int) {
    #Cons h tail : h
    #Nil : #0
  };

  @len (lst : List int) =
  ~(lst) {
    #Cons h tail : (#1 + (len  tail))
    #Nil : #0
  };

  (len abc) + (gethead abc)
