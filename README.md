# interactor-spatial-oracle

The predictive spatial-oracle hexagon (formerly `PredictiveBvh`): ghost-expansion + SAH proofs (core), emitting `predictive_bvh.h` via the AmoLean codegen adapter (`lake exe bvh-codegen`).

> Split out of the [`lean-predictive-bvh`](https://github.com/v-sekai-multiplayer-fabric/lean-predictive-bvh) monorepo (now archived). Each hexagon cluster is its own repo following the `core/ports/adapters` convention; cross-cluster wiring is via Lake `require ... from git`.

## Dependencies

- [`entities-lean-shared`](https://github.com/v-sekai-multiplayer-fabric/entities-lean-shared) — common primitive types
- [`entities-lean-rebac`](https://github.com/v-sekai-multiplayer-fabric/entities-lean-rebac) — Formulas reference Relativistic (known core->core leak; TODO invert via a port)
- [`truth_research_zk`](https://github.com/V-Sekai-fire/truth_research_zk) — AmoLean E-graph optimizer + E-node/E-class storage

## Build

```sh
lake build         # production gate: typecheck the  cluster
lake build Research  # research-tier (non-gating; may fail)
```

## Hexagon layout

- `core/` — dependency-free domain logic + proofs
- `ports/` — narrow driving (source) / driven (sink) contracts
- `adapters/` — concrete I/O at the edges
