-- SPDX-License-Identifier: MIT
-- Copyright (c) 2026-present K. S. Ernest (iFire) Lee

import PlausibleWitnessDag
import PredictiveBvh.core.HilbertBroadphase

-- ============================================================================
-- ZONE CONCURRENCY HILL-CLIMB
--
-- Uses plausible-witness-dag to find the maximum concurrent players per zone
-- that stays within a total-work budget (BroadphaseResult.totalWork).
--
-- Work is averaged over `numSeeds` deterministic random configurations per N
-- to smooth out stochastic variance.  `readback` scans linearly for the true
-- maximum (not binary search, since averaged work is not strictly monotone).
--
-- Parameters:
--   zoneSize   — zone side length (= 2 × AOI_RADIUS = 120 in production)
--   ghostHalf  — entity AABB half-extent in integer scene units
--   workBudget — max avgWork per zone per tick
--   numSeeds   — configurations averaged per N (higher = less variance)
-- ============================================================================

namespace ZoneConcurrency

open PlausibleWitnessDag

-- ── Scene parameters ──────────────────────────────────────────────────────────

def zoneSize  : Int := 120
def ghostHalf : Int := 1

/-- Work budget: max avg totalWork per zone per tick.
    50 000 ops ≈ 13.5 × N_opt → N_opt ≈ 3700 purely from overhead.
    k-pairs dominate at density; the hill-climb finds the empirical ceiling. -/
def workBudget : Nat := 50000

/-- Number of random seeds averaged per candidate N to reduce variance. -/
def numSeeds : Nat := 4

-- ── Deterministic player generation ──────────────────────────────────────────

private def lcgStep (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % (2 ^ 64)

private def playerBox (seed : Nat) : BoundingBox :=
  let s1 := lcgStep seed
  let s2 := lcgStep s1
  let cx : Int := (Int.ofNat (s1 % zoneSize.toNat)) - zoneSize / 2
  let cz : Int := (Int.ofNat (s2 % zoneSize.toNat)) - zoneSize / 2
  { minX := cx - ghostHalf, maxX := cx + ghostHalf,
    minY := -ghostHalf,     maxY := ghostHalf,
    minZ := cz - ghostHalf, maxZ := cz + ghostHalf }

def generatePlayers (n : Nat) (baseSeed : Nat := 0xDEADBEEF) : Array BoundingBox := Id.run do
  let mut boxes : Array BoundingBox := #[]
  let mut seed  : Nat := baseSeed
  for _ in List.range n do
    boxes := boxes.push (playerBox seed)
    seed  := lcgStep seed
  return boxes

-- ── Broadphase work oracle (averaged over multiple seeds) ─────────────────────

private def seeds : List Nat :=
  [0xDEADBEEF, 0xCAFEBABE, 0x12345678, 0xABCDEF01]

/-- Average broadphase work for N players over `numSeeds` configurations.
    Averaging smooths variance; using the max would give a tighter safety margin. -/
def zoneWork (n : Nat) : Nat :=
  let total := seeds.take numSeeds |>.foldl (fun acc s =>
    acc + (hilbertBroadphase (generatePlayers n s)).totalWork) 0
  total / numSeeds

-- ── Candidate predicate ───────────────────────────────────────────────────────

/-- True when N players fit within budget on average. -/
def withinBudget (n : Nat) : Bool := zoneWork n ≤ workBudget

-- ── Witness ladder ────────────────────────────────────────────────────────────

def concurrentLadder : Array Level := #[
  { idx := 0, walkSteps := 256,  finBound := 256,  numInst := 300  },
  { idx := 1, walkSteps := 1024, finBound := 1024, numInst := 600  },
  { idx := 2, walkSteps := 4096, finBound := 4096, numInst := 1200 } ]

-- ── Readback: linear scan for max feasible N ─────────────────────────────────

/-- Linear scan in [1, steps] for the highest N with withinBudget N = true.
    Linear (not binary) because avgWork is not strictly monotone in N. -/
def readback (steps : Nat) : Readback Nat := Id.run do
  let mut best : Nat := 0
  for n in List.range (steps + 1) do
    if n > 0 && withinBudget n then best := n
  -- budgetHit = true when all scanned N fit (true max may be above this window)
  let budgetHit := best == steps
  -- found = true only when we hit the ceiling *inside* the window, not at its edge
  let found := best > 0 && !budgetHit
  return { value := best, found, witnessIdx := best, budgetHit }

-- ── Hill-climb entry point ────────────────────────────────────────────────────

def hillClimb : IO Nat := do
  let (best, lvl, trace) ← resolve "max zone concurrents"
    (fun _lvl k => k > 0 && withinBudget k) readback concurrentLadder
  IO.println s!"ZoneConcurrency: max={best}  level=L{lvl}  outcome={repr trace.outcome}"
  return best

-- ── Fabric-wide concurrent capacity ──────────────────────────────────────────

/-- Scene dimensions (must match server.gd SCENE_MIN/MAX and ZONE_CELL_SIZE). -/
def sceneWidth  : Nat := 400
def sceneDepth  : Nat := 400
def zoneCellSize : Nat := 60  -- = AOI_RADIUS in server.gd

/-- Number of zone columns and rows in the scene grid. -/
def zoneCols : Nat := (sceneWidth  + zoneCellSize - 1) / zoneCellSize + 1  -- = 8
def zoneRows : Nat := (sceneDepth  + zoneCellSize - 1) / zoneCellSize + 1  -- = 8

/-- Total zones in the scene. -/
def totalZones : Nat := zoneCols * zoneRows  -- = 64

/-- Fabric total = max-per-zone × total zones.
    Each zone handles its own N_max players independently; zones are either
    single-threaded (one core) or sharded (one server per zone). -/
def fabricMax (nPerZone : Nat) : Nat := nPerZone * totalZones

end ZoneConcurrency

def main (_args : List String) : IO Unit := do
  let nPerZone ← ZoneConcurrency.hillClimb
  let total := ZoneConcurrency.fabricMax nPerZone
  IO.println s!"Max concurrent players per zone:  {nPerZone}"
  IO.println s!"Zones in scene ({ZoneConcurrency.zoneCols}×{ZoneConcurrency.zoneRows}): {ZoneConcurrency.totalZones}"
  IO.println s!"Fabric total concurrent players:   {total}"
