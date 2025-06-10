
-- // run this with -C1 doesnt terminate otherwise
-- // search over circuits to replicate a given truth function with nand gates only
-- // generate all circuits (nets) as superposition with label 77
-- // generate all possible arguments as superposition with label 78

-- data list{#Nil #Cons{a b}}

-- @and(a b) = ~a{0:0 p:b }
-- @nand(a b) = (- 1 @and(a b))
-- @or(a b) = ~a !b{ 0: b p: 1 }
-- @not(a) = (- 1 a)
-- @xor(a b) = (!= a b)

-- @leaf(x) = λnode λleaf (leaf x)
-- @node(a b) = λnode λleaf
--   !&{n1 node} = node
--   !&{n2 node} = node
--   !&{l1 l2} = leaf
--   (node (a n1 l1) (b n2 l2))

-- @sublayer(head secondary rest) = ~secondary !rest{
--   #Nil: rest
--   #Cons{h t}:
--     ! &{h1 h2} = head
--     #Cons{
--       @node(h h1)
--       @sublayer(h2 t rest)}
-- }

-- // generate list of new nodes given last nodes
-- @layer(srcs) =
--   !&{s1 s2} = srcs
--   ~s1 {
--     #Nil: []
--     #Cons{h tail}:
--       @sublayer(h s2 @layer(tail))
--   }


-- // generate list of all nets
-- @makenets(srcs) = !&{n1 n2} = @layer(srcs) @concat(n1 @makenets(n2))

-- // generate superposition of all nets
-- @allnets = λa λb λc
--   !srcs = @map(λx @leaf(x) [a b c])
--   @roll(77 @makenets(srcs))


-- @map(fn ls) = ~ls{ #Nil:[] #Cons{h t}: ! &{f1 f2} = fn #Cons{(f1 h) @map(f2 t)}}

-- @when(c t) = ~ c {0: * p: t}

-- @concat(a b) = ~a !b{#Nil: b #Cons{h t}: #Cons{h @concat(t b)}}
-- @slice(n x) = ~n{
--   0: [] p: ~x{
--     #Nil: []
--     #Cons{h t}: #Cons{h @slice(p t)}
--   }
-- }

-- data maybe{#Some{x} #None}


-- // generate all permutations of truth values
-- @permute(n) = ~n{
--   0: [[]]
--   p:
--     !&0 {p1 p2} = @map(λx #Cons{&0{0 1} x} @permute(p))
--     @concat(p1 p2)
-- }

-- @do_permute(n) = @roll(78 @concat(@map(λx #Some{x} @permute(n)) [#None]))

-- @roll(&L ls) = ~ls{#Nil: * #Cons{h t}: &L{h @roll(&L t)}}
-- @supslice(&L n sup) = ~n{0: * p: !&L{a b} = sup &L{a @supslice(&L b p)}}
-- @unroll(&L sup) = !&L{a b} = sup #Cons{a @unroll(&L b)}


-- @apply(fn args) = ~args !fn{
--   #Nil: fn
--   #Cons{h t}: @apply((fn h) t)
-- }

-- @maybe_map(fn mb) = ~mb{
--   #None: #None
--   #Some{v}: #Some{(fn v)}
-- }

-- @allcollapse(x) =
--   ! &78{head tail} = x
--   ~head{
--     #Some{h}: ~h{
--       0: 0
--       p: @allcollapse(tail)
--     }
--     #None: 1
--   }

-- @nandnet(net) = (net
--   (λa λb @nand(a b))
--   λleaf leaf)

-- data show{#Nand{a b}}


-- @join(slist) = ~slist{
--   #Nil: ""
--   #Cons{h t}: @concat(h @join(t))}

-- @show_net(net) =
--   ((net "a" "b" "c")
--   (λa λb @join(["nand(" a ", " b ")"] ))
--   λleaf leaf)


-- // try different truth functions
-- @t = λa λb λc  @nand(a c)
-- @t = λa λb λc  @or(a c)
-- @t = λa λb λc  @and(a b)
-- @t = λa λb λc  @and(a @or(b c))
-- // @t = λa λb λc  @xor(a b)



-- @main =
--   !x = @do_permute(3)

--   @show_net(
--     λa λb λc
--     @when(
--       @allcollapse(@maybe_map(
--         λe
--           !&{e1 e2} = e
--           (== @nandnet(@apply(@allnets e1))
--           @apply(@t e2)) x))
--       (@allnets a b c)
--   ))



-- this is work in progress of a simple enumerator

import HighScript

set_option linter.unusedVariables false

def map {a b} :Expr ((a->b) -> list a -> list b ) :=
  let map := Expr.ftag "map" ((a->b) -> list a -> list b);
  Expr.fn "map"
  (lam f l => ~l {
    #Nil: []
    #Cons h t: Cons (f • h) (map • f • t)
  })

def main :=

  @not a = (#1 - a);
  @and a b = if a then b else #0;
  @nand a b = not • (and • a • b);
  @or a b = if a then #1 else b;
  @xor a b = (a != b);


  data term {
    #Leaf x:int
    #Node a:self b:self
  }

  data maybe t {
    #Some x:t
    #None
  }

  let terms := list term;

  @sublayer (head: term) (secondary: list term) (rest : list term) =
  ~secondary {
    #Nil: rest
    #Cons h t : Cons (Node h head) (sublayer • h • t • rest)
  };

  @layer (srcs: list term) =
    ~srcs {
      #Nil: []
      #Cons h tail: sublayer • h • srcs • (layer • tail)
    };

  @concat (a:terms) (b:terms) =
    ~ a {
      #Nil: b
      #Cons h t: Cons h (concat • t • b)
    };

  @makenets srcs : terms =
    ! n = layer • srcs;
    concat • n • (makenets n);

  @rollterm (ls : list term) : term =
    ~ls{ #Nil: ** #Cons h t: &77 {h, rollterm • t} };

  @rollargs (ls : list term) =
    ~ ls { #Nil: ** #Cons h t: &78 {h, rollargs • t} };

  @allnets : term =
    ! srcs = map • (lam x => Leaf x) • [0, 1, 2];
    rollterm • (makenets • srcs);

  @get (l: list int) (n: int) : int =
    ~l{
      #Nil: #0
      #Cons h t:
        if n == 0
        then h
        else get • t • (n - (1 as int))
    };

  @app (net : term) (args: list int) : int = ~net{
    #Leaf x: get • args • x
    #Node a b: nand • (app • a • args) • (app • b • args)
  };



  @t a (b:int) c : int = nand • a • c;


  -- runmain $ and • #0 • #1
  -- runmain $ app • allnets • [1, 0, 0]

  let x := allnets

  runmain $ allnets
