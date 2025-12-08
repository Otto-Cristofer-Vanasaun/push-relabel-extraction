#!/usr/bin/env python3
"""
Random flow-network generator for push-relabel testing.

- Nodes are 0..n-1 (nat-friendly).
- Ensures at least one s→…→t path (a "backbone" path).
- Capacities are positive integers -> printed as `%Q` in the Rocq snippet.
- Outputs:
    1) <out_prefix>.dot  (Graphviz)
    2) <out_prefix>.v    (Rocq/Coq definition matching your (list nat * list (nat*nat) * (nat->nat->Q) * nat * nat)%type)

Examples
--------
# 12 nodes, ~30% density, source=0 sink=11, reproducible seed:
python gen_flow.py -n 12 -p 0.30 --seed 7 --out-prefix FN_rand --def-name FN_rand

# 8 nodes, exactly 14 edges, DAG (no cycles), larger capacities:
python gen_flow.py -n 8 -m 14 --acyclic --min-cap 5 --max-cap 40 --out-prefix FN8 --def-name FN8

# Render the DOT file (requires Graphviz):
dot -Tpng FN_rand.dot -o FN_rand.png
"""

from __future__ import annotations
import argparse
import random
from typing import Dict, Iterable, List, Optional, Set, Tuple

Edge = Tuple[int, int]

def build_backbone_path(nodes: List[int], s: int, t: int, rng: random.Random) -> List[int]:
    """Create a random permutation from s to t that passes through all other nodes once."""
    middle = [v for v in nodes if v not in (s, t)]
    rng.shuffle(middle)
    return [s] + middle + [t]

def allowed_pairs(
    nodes: List[int],
    s: int,
    t: int,
    forbid_into_s: bool,
    forbid_out_of_t: bool,
    acyclic: bool,
) -> List[Edge]:
    """All candidate directed edges respecting constraints."""
    pairs: List[Edge] = []
    for u in nodes:
        for v in nodes:
            if u == v:
                continue
            if forbid_out_of_t and u == t:
                continue
            if forbid_into_s and v == s:
                continue
            pairs.append((u, v))
    return pairs

def choose_edges(
    nodes: List[int],
    s: int,
    t: int,
    m: Optional[int],
    p: Optional[float],
    rng: random.Random,
    acyclic: bool,
    forbid_into_s: bool,
    forbid_out_of_t: bool,
) -> List[Edge]:
    """Pick an edge set that includes a backbone path and extra random edges."""
    # Backbone
    #path = build_backbone_path(nodes, s, t, rng)
    #pos = {v: i for i, v in enumerate(path)}
    #edges: Set[Edge] = set((path[i], path[i + 1]) for i in range(len(path) - 1))
    edges = set()
    # All allowed pairs
    all_pairs = allowed_pairs(nodes, s, t, forbid_into_s, forbid_out_of_t, acyclic)
    #candidates = [e for e in all_pairs if e not in edges]
    candidates = all_pairs

    # Target number of edges
    if m is not None and p is not None:
        raise ValueError("Use either -m/--edges or -p/--density, not both.")
    if m is None and p is None:
        # default density ≈ 0.30
        target = int(round(0.30 * len(all_pairs)))
    elif m is not None:
        # at least the backbone size
        #target = max(len(edges), min(m, len(all_pairs)))
        target = m
    else:
        # p given
        target = max(0, min(len(all_pairs), int(round(p * len(all_pairs)))))

    # Add random extras
    rng.shuffle(candidates)
    extras_needed = max(0, target - len(edges))
    for e in candidates[:extras_needed]:
        edges.add(e)

    return sorted(edges)

def assign_capacities(edges: Iterable[Edge], cap_min: int, cap_max: int, rng: random.Random) -> Dict[Edge, int]:
    if cap_min < 1 or cap_min > cap_max:
        raise ValueError("Invalid capacity bounds: require 1 <= min_cap <= max_cap.")
    return {e: rng.randint(cap_min, cap_max) for e in edges}

def to_coq_list(xs: Iterable[int]) -> str:
    return "[" + ";".join(str(x) for x in xs) + "]"

def to_coq_edge_list(es: Iterable[Edge]) -> str:
    return "[" + ";".join(f"({u},{v})" for (u, v) in es) + "]"

def write_coq_file(
    filename: str,
    def_name: str,
    nodes: List[int],
    edges: List[Edge],
    caps: Dict[Edge, int],
    s: int,
    t: int,
) -> None:
    with open(filename, "w", encoding="utf-8") as f:
        f.write("(* Auto-generated random flow network. *)\n")
        f.write("From Coq Require Import QArith List.\n")
        f.write("Import ListNotations.\n")
        f.write("Local Open Scope Q_scope.\n\n")
        f.write(f"Definition {def_name} : (list nat * list (nat * nat) * (nat -> nat -> Q) * nat * nat)%type :=\n")
        f.write("  let c := fun (x y : nat) =>\n")
        f.write("    match x, y with\n")
        for (u, v) in edges:
            f.write(f"    | {u}, {v} => {caps[(u, v)]}%Q\n")
        f.write("    | _, _ => 0%Q\n")
        f.write("    end\n")
        f.write("  in\n")
        f.write(f"  (({to_coq_list(nodes)},{to_coq_edge_list(edges)}), c, {s}, {t}).\n")

def write_dot_file(
    filename: str,
    nodes: List[int],
    edges: List[Edge],
    caps: Dict[Edge, int],
    s: int,
    t: int,
    label: str,
) -> None:
    with open(filename, "w", encoding="utf-8") as f:
        f.write("digraph Flow {\n")
        f.write("  rankdir=LR;\n")
        f.write('  node [shape=circle];\n')
        # Highlight source and sink
        f.write(f'  {s} [shape=doublecircle, style=filled, fillcolor=lightgray, label="{s} (s)"];\n')
        f.write(f'  {t} [shape=doublecircle, style=filled, fillcolor=lightgray, label="{t} (t)"];\n')
        for v in nodes:
            if v not in (s, t):
                f.write(f"  {v};\n")
        f.write(f'  labelloc="t"; label="{label}";\n')
        for (u, v) in edges:
            f.write(f'  {u} -> {v} [label="{caps[(u, v)]}"];\n')
        f.write("}\n")

def main() -> None:
    ap = argparse.ArgumentParser(description="Generate a random flow network and emit Graphviz (.dot) + Rocq (.v).")
    ap.add_argument("-n", "--nodes", type=int, required=True, help="Number of nodes (must be ≥ 2).")
    ap.add_argument("-m", "--edges", type=int, help="Total number of edges to aim for (≥ n-1).")
    ap.add_argument("-p", "--density", type=float, help="Approximate density in [0,1] (alternative to --edges).")
    ap.add_argument("--source", type=int, default=0, help="Source node id (default: 0).")
    ap.add_argument("--sink", type=int, help="Sink node id (default: n-1).")
    ap.add_argument("--min-cap", type=int, default=1, help="Minimum capacity (default: 1).")
    ap.add_argument("--max-cap", type=int, default=100, help="Maximum capacity (default: 20).")
    ap.add_argument("--seed", type=int, default=None, help="Seed for reproducibility (default: random).")
    ap.add_argument("--acyclic", action="store_true", help="Force a DAG (edges go forward along a random topological order).")
    ap.add_argument("--allow-into-source", action="store_true", help="Allow edges that end at the source (v == s).")
    ap.add_argument("--allow-out-of-sink", action="store_true", help="Allow edges that start from the sink (u == t).")
    ap.add_argument("--out-prefix", type=str, default="FN_rand", help="Output prefix for files (default: FN_rand).")
    ap.add_argument("--def-name", type=str, default="FN_rand", help="Coq/Rocq definition name (default: FN_rand).")

    args = ap.parse_args()

    if args.nodes < 2:
        raise SystemExit("nodes must be ≥ 2.")

    n = args.nodes
    s = args.source
    t = args.sink if args.sink is not None else (n - 1)
    if not (0 <= s < n and 0 <= t < n) or s == t:
        raise SystemExit("source/sink must be distinct and within 0..n-1.")

    if args.density is not None and not (0.0 <= args.density <= 1.0):
        raise SystemExit("--density must be in [0,1].")
    #if args.edges is not None and args.edges < (n - 1):
        # backbone requires at least n-1 edges
        #args.edges = n - 1

    rng = random.Random(args.seed)
    nodes = list(range(n))

    edges = choose_edges(
        nodes=nodes,
        s=s,
        t=t,
        m=args.edges,
        p=args.density,
        rng=rng,
        acyclic=args.acyclic,
        forbid_into_s=not args.allow_into_source,
        forbid_out_of_t=not args.allow_out_of_sink,
    )
    caps = assign_capacities(edges, args.min_cap, args.max_cap, rng)

    dot_file = f"{args.out_prefix}.dot"
    coq_file = f"{args.out_prefix}.v"

    label = f"Random flow | n={n}, m={len(edges)}, s={s}, t={t}, cap∈[{args.min_cap},{args.max_cap}], seed={args.seed}"
    write_dot_file(dot_file, nodes, edges, caps, s, t, label)
    write_coq_file(coq_file, args.def_name, nodes, edges, caps, s, t)

    print(f"Wrote: {dot_file}")
    print(f"Wrote: {coq_file}")
    print(f"Summary: n={n}, m={len(edges)}, s={s}, t={t}, acyclic={args.acyclic}, seed={args.seed}")
    print("Tip: 'dot -Tpng {0} -o {0}.png' to render the graph.".format(dot_file))

if __name__ == "__main__":
    main()