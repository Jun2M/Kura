# ToDo - Kura

## Tasks

- [ ] Feat: Define `LocallyFinite` instance and use that was an assumption necessary for degrees
- [ ] Feat: `union` is `Isom` with `glue` on `inter`
- [ ] Feat: `glue` between end points of two `PathGraph`s is `Isom` with a longer `PathGraph`
- [ ] Feat: `PathGraph` and etc. are `LocallyFinite`
- [ ] Chore: Prove or remove `sorry`s

## Thoughts

- [ ] `Subgraph` type?
- [ ] What to do with `Add` and `Remove` files?
- [ ] Does `Examples` folder worthy of being a folder rather than a file?
- [ ] How to represent a `Walk`: `Walk` object or `PathGraph ⊆ᴳ ·`?
- [ ] Clean up `.Ignore` folder?
- [ ] Where is `pmap` for `Set`?

## Done

- [x] Chore: Have `Isom` lemmas so that `simp` solves forwards and backwards applications canceling each other out
