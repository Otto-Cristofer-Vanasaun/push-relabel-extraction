#### Optimisations made (use built-in OCaml types)
* `ExtrOcamlBasic` library
  - Truth values (also `sumbool`)
  - `option` (also `sumor`)
  - `unit`
  - `list`
  - `prod`
  - `andb`
  - `orb`
* `ExtrOcamlZInt` library
  - `positive` to OCaml `int`
  - `Z` to OCaml `int`
* `ExtrOcamlNatInt` library
  - `nat` to OCaml `int`
  - `add` to OCaml `(+)`
  - `mult` to OCaml `(*)`

`Q` to OCaml `(int * int)`
`length` to OCaml `List.length`
`map` to OCaml `List.map`
`VMap` and `EMap` to OCaml `Hashtbl` (along with all of the functions defined for `VMap` and `EMap`).

#### Description of files
* Rocq \
`PR.v` includes all changes until `Q` to `(int * int)` (included). Outdated, will be changed or removed. \
`PR_nat.v` is the up-to-date file. It also includes the code to extract `VMap` and `EMap` to OCaml `Map` objects (commented out). Also includes the code to extract `VSet` and `ESet` to OCaml `Set` (commented out), as well as definitions and lemmas to generalise `VSet` and `ESet` to use type `T` instead of `list V` (in `SetSpec` and `MkSet`, also commented out). Finally, the definition of `Graph` through `VSet.t` and `ESet.t` (commented out). \
* OCaml \
The folder `push-relabel` is an OCaml project, in which is the `bin` folder. The `bin` folder includes the file `main.ml`, where the result of the extraction can be found. \
At the beginning of the `main.ml` file (up until the "Extracted from the push-relabel..." comment) is a line to ignore some warnings as well as the manually written definitions for `NatH`, `EdgeH` and `Hashtbl` structures. The definitions for `EdgeT`, `VerticeSet'` and `EdgeSet'` are unused. The code includes definitions to make the program use `Map` instead of `Hashtbl`, but is commented out. \
At the end of the `main.ml` file are functions for displaying the answer and time after running the program, with additional flow networks in the comments. \
* Python (flow network generation) \
  The folder `gen_flow` includes some flow networks and the Python script for generating them.

#### Executing the OCaml code
With dune:
* Run `dune exec push-relabel` from inside the `push-relabel` folder \
Without dune:
* Run `ocaml` from inside the `push-relabel` folder
* Run `#use "main.ml";;`
* If that does not work, try `#use "topfind";;` and `#require "zarith";;` before running `#use "main.ml";;`
