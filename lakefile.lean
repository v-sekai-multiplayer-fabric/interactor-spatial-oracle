-- SPDX-License-Identifier: MIT
-- Copyright (c) 2026-present K. S. Ernest (iFire) Lee

import Lake
open System Lake DSL

package «lean-spatial-oracle» where

-- Shared primitive types (common vocabulary).
require «lean-shared-core» from git
  "https://github.com/v-sekai-multiplayer-fabric/lean-shared-core.git" @ "main"

-- ReBAC authorization core. Formulas reference Relativistic; known core->core
-- leak tracked in PredictiveBvh/ports/sibling-repos.txt (TODO invert via a port).
require «lean-rebac-core» from git
  "https://github.com/v-sekai-multiplayer-fabric/lean-rebac-core.git" @ "main"

-- AmoLean E-graph optimizer + flat ECS-style E-node/E-class storage.
require «truth_research_zk» from git
  "https://github.com/V-Sekai-fire/truth_research_zk.git" @ "main"

-- The predictive spatial-oracle hexagon (ghost expansion + SAH + broadphase).
lean_lib PredictiveBvh where
  roots := #[`PredictiveBvh]
  globs := #[.one `PredictiveBvh]

-- Research-tier optimal-partition proofs (NOT on the CI production gate).
lean_lib Research where
  roots := #[`Research]
  globs := #[.one `Research]

-- AmoLean C code generator: writes predictive_bvh.h, consumed by the
-- multiplayer_fabric C++ module. Lives in the predictive-bvh adapters layer.
@[default_target]
lean_exe «bvh-codegen» where
  root := `PredictiveBvh.adapters.CodeGen
  supportInterpreter := true
