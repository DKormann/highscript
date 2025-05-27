import HighScript


def main :=

  @x = &0{#1, #2};

  @y =
    !&0{a, b} = x;
    b;

  runmain y
