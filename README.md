## Extraction of the Push-relabel algorithm from Rocq to OCaml
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

* Other changes
- `Q` to OCaml `(int * int)`
- `length` to OCaml `List.length`
- `map` to OCaml `List.map`
- `VertexMap` and `EdgeMap` to OCaml `Hashtbl` (along with all of the functions defined for `VertexMap` and `EdgeMap`).
- Added `ExcessMap` for caching the results of the `excess` function.
- `VertexSet` and `EdgeSet` to OCaml `Set` (along with all of the functions; most use the functions defined for the `Set` type, except for `VertexSet.find_first`, which uses the `find` function defined in `Seq`).

#### Description of files
* Rocq \
`PR_extract.v` is the main file. Includes the push-relabel algorithm and its extraction to OCaml along with example networks FN1, FN2, FN3, FN4 and FN5.
* OCaml \
The folder `push-relabel` is the OCaml project, in which is the `bin` folder. The `bin` folder includes the file `main.ml`, where the result of the extraction can be found. \
At the beginning of the `main.ml` file (up until the "Extracted from the push-relabel..." comment) is a line to ignore some warnings as well as the manually written definitions for `NatH`, `EdgeH` and `EdgeT` structures. \
At the end of the `main.ml` file are functions for displaying the time, and a pretty-printer that is used to output the flows of edges, excesses and labels of vertices. Also includes the extracted versions of the example networks fN1 through fN5.
* Python (flow network generation) \
  The folder `gen_flow` includes some flow networks and the Python script for generating them.

#### Executing the OCaml code
With dune: \
Run `dune exec push-relabel` from inside the `push-relabel` folder \
\
Without dune: \
Run `ocaml` from inside the `push-relabel` folder \
Run `#use "main.ml";;` \
If that does not work, try `#use "topfind";;` and `#require "zarith";;` before running `#use "main.ml";;` 
