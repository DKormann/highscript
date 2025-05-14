

[work in progress]

highscript is a LEAN DSL that compiles to [HVM](https://github.com/HigherOrderCo/hvm3) code

## features:

  - [x] generate HVM
  - [x] standart lambda syntax
  - [x] simple type system
  - [x] linearize variables
  - [x] run HVM output
  - [x] support for custom ADT's
  - [x] Pattern matching
  - [ ] stronger type guarantees


## installation

  - install [L∃∀N](https://leanprover-community.github.io/install/macos.html)

  - clone this repo

  - run `setup.sh`

## usage

see examples folder

after successfull installation it should be possible to import HighScript in lean file and run script on HVM backend with runHVM command

To run example which generates and runs HVM code
```
lean --run examples/fun_call.lean
```

