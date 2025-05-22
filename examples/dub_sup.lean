import HighScript

-- dub and sup nodes dont interact with the type system

def main :=

  @x = &0{#1, #2};

  @y =
    !&0{a, b} = @x;
    b;

  runmain y
