# ToDo - Kura

## Tasks

- [ ] Feat: Define `LocallyFinite` instance and use that was an assumption necessary for degrees
- [ ] Feat: `PathGraph` and etc. are `LocallyFinite`
- [ ] Chore: Prove or remove `sorry`s
- [ ] Feat: Seamless interconnection between `Walk` and `PathGraph` Emb
- [ ] Feat: `acyclic` decomposed by 1 `Separation`
- [ ] Feat: Cycle to 2 paths by removing 2 edges
- [ ] Feat: Cycle by a path and an edge between the end points

## Thoughts
- [ ] `glue`?
  - [ ] Feat: `union` is `Isom` with `glue` on `inter`
  - [ ] Feat: `glue` between end points of two `PathGraph`s is `Isom` with a longer `PathGraph`
- [ ] What to do with `Add` file?
- [ ] Does `Examples` folder worthy of being a folder rather than a file?
- [ ] Clean up `.Ignore` folder?
- [ ] Where is `pmap` for `Set`?

## Done

- [x] `Subgraph` type implemented
- [x] Chore: Have `Isom` lemmas so that `simp` solves forwards and backwards applications canceling each other out
