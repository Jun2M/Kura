# ToDo - Kura

## Tasks - Goals with a clear plan

- Take a Minimal Graph? [Prop721]

- GraphVertexFunction/GraphEdgeFunction [Isom]

- Update commented-out lemma\theorems in Minor.lean [priMinor]

- Sorry-free Menger [Menger]

## Topics - Goals without a plan

- [Prop721] : Prove Prop 7.2.1 from the Diestel book

  - [priMinor] : Expand IspMinor/IsrMinor/IsiMinor
  
  - [CMinor] : Expand Clique Minor

- [Isom] : Expand Hom/Emb/Isom

- [Menger] : Prove Menger's theorem

  - [PathEnsemble] Make PathEnsemble.lean usable

  - [IsEdgeSetSep] Develop IsEdgeSetSep

## Options - Actionables without a clear goal

## Thoughts - Abstract thoughts

- Distance function as a metric


## Prompt

You are tasked to prove a lemma related to contraction of a graph.
The precise lemma is this:
If `G` is a simple graph and `xy` is an edge in `G`, then `G/xy`, (the graph obtained by contracting the edge `xy` in `G` and removing the parallel edges and loops) has the number of edge equal to the number of edges in `G` minus the common neighbors of `x` and `y`.

For this, you would need to create several lemmas before hand. Here is a possible break down of the proof:
- Let `f` be a function on the vertices of `G`, then for each vertex `v` in `G.vxMap f` has the `incFun` equal to the sum of `incFun` of all vertices that are mapped to `v` under `f` for each edge in `G`. As the sum of `incFun` defines the `degree` of a vertex, this means that the `degree` of `v` in `G.vxMap f` is equal to the sum of the `degree` values of all vertices that are mapped to `v` under `f`.
- Let `e` be an edge in `G` incident to `x` and `y`. (`x` and `y` may be the same vertex in the case where `e` is a loop) Then, `x` has `degree` value in `G \ e` equal to the `degree` value of `x` in `G` minus `G.incFun e x`. As a corollary, if `e` is not a loop, `(G \ e).degree x = G.degree x - 1` and otherwise `G.degree x -2`. Similarly, for `y`. This should be fairly easy as `degree` is defined as the sum of `incFun` values of all edges incident to the vertex.
- Let `xy` is an edge in `G`. Then the supervertex (which is vertices `x` and `y` merged together) in `G/xy` has the `G.incFun` function value equal to the sum of the `G.incFun` values of `x` and `y` minus 2. 
This is because the edge contraction is defined as `vxMap` then `edgeDelete`.
By the previous point, the `incFun` value of the supervertex is the sum of the `incFun` values of `x` and `y`. But `edgeDelete` removes the `xy` edge we are contracting on. This causes the `-2`.
- Contraction of a single edge on simple graph does not create a loop.
  For the proof, 