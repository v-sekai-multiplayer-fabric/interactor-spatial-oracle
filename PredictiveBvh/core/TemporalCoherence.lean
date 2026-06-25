-- SPDX-License-Identifier: MIT
-- Copyright (c) 2026-present K. S. Ernest (iFire) Lee

import PredictiveBvh.core.HilbertBroadphase

-- ============================================================================
-- TEMPORAL COHERENCE SPEC  (research tier — NOT on CI production gate)
--
-- Formalizes the two temporal-coherence optimizations from research.md:
--
-- Item 3 — QuinticHermite prediction → skip-if-correct:
--   An entity whose Hilbert code and ghost AABB are identical between ticks
--   contributes identical pairs in both ticks.  If all entities in a group
--   are stable, the full broadphase output on those entities is unchanged.
--
-- Item 1 — Dirty-bit incremental tick:
--   TemporalBroadphaseState caches the previous sorted array and group
--   assignments.  tickBroadphase only re-evaluates when any group is dirty
--   (changed code or ghost), mirroring the touched_bits / touched_meta_bits
--   pattern in TreeC.lean.  Proof of equivalence with hilbertBroadphase is
--   admitted (sorry) pending a white-box lemma from HilbertBroadphase.
-- ============================================================================

-- ── Item 3: codeStable predicate and pairsUnchanged theorem ──────────────────

/-- An entry is stable across ticks when both its Hilbert code and ghost AABB
    are unchanged.  Code stability means no group reassignment; ghost stability
    means pair outcomes are identical. -/
def codeStable (prev curr : HilbertEntry) : Prop :=
  prev.code = curr.code ∧ prev.ghost = curr.ghost

/-- If every entry in group g is stable, a fresh hilbertBroadphase run on
    those entries produces the same result in both ticks.
    Stated in terms of the public `hilbertBroadphase` API so the proof does
    not depend on the private `checkIntraGroup` body.
    Proof admitted: requires `codeStable → ghost equality → same broadphase`
    via congruence on `sortByHilbert` + `formGroups` + the sweep functions
    (follow-on task once a white-box export lemma exists). -/
theorem pairsUnchanged (g : HilbertGroup)
    (prev curr : Array HilbertEntry)
    (stable : ∀ i, g.first ≤ i ∧ i ≤ g.last → codeStable prev[i]! curr[i]!) :
    hilbertBroadphase
        ((Array.range (g.last - g.first + 1)).map
          fun k => prev[g.first + k]!.ghost) =
    hilbertBroadphase
        ((Array.range (g.last - g.first + 1)).map
          fun k => curr[g.first + k]!.ghost) := by
  -- Proof sketch: codeStable → ghost equality for each k → map extensionality
  -- → hilbertBroadphase congruence.  Admitted pending Array.ext + omega on
  -- Nat subtraction bounds (g.first + k ≤ g.last from k < g.last - g.first + 1
  -- holds when g.first ≤ g.last, which is an invariant of formGroups).
  sorry

-- ── Item 1: Temporal broadphase state and incremental tick ───────────────────

/-- Cached state between broadphase ticks.  dirtyGroups[gi] is true when any
    entry in group gi changed its Hilbert code or ghost AABB since last tick. -/
structure TemporalBroadphaseState where
  prevSorted : Array HilbertEntry
  prevGroups : Array HilbertGroup
  dirtyGroups : Array Bool

/-- Mark a group dirty if any of its entries changed code or ghost since the
    previous tick.  Uses decidable field comparisons (Nat / BoundingBox both
    derive DecidableEq). -/
private def computeDirtyGroups (prevSorted currSorted : Array HilbertEntry)
    (groups : Array HilbertGroup) : Array Bool :=
  groups.map fun g =>
    (List.range (g.last - g.first + 1)).any fun k =>
      let i := g.first + k
      if i < prevSorted.size && i < currSorted.size then
        prevSorted[i]!.code  != currSorted[i]!.code  ||
        prevSorted[i]!.ghost != currSorted[i]!.ghost
      else true

/-- Incremental broadphase tick: re-evaluates when any group is dirty;
    returns prevResult unchanged on a fully-stable tick.
    Return type: `(BroadphaseResult, TemporalBroadphaseState)`. -/
def tickBroadphase (state : TemporalBroadphaseState)
    (currSorted : Array HilbertEntry) (prevResult : BroadphaseResult)
    : BroadphaseResult × TemporalBroadphaseState :=
  let currGroups := formGroups currSorted
  let dirty := computeDirtyGroups state.prevSorted currSorted currGroups
  let result :=
    if dirty.any id then hilbertBroadphase (currSorted.map (·.ghost))
    else prevResult
  (result, { prevSorted := currSorted, prevGroups := currGroups, dirtyGroups := dirty })

/-- Goal: tickBroadphase always produces the same pairs as a full
    hilbertBroadphase on currSorted.
    Dirty-tick case: result is hilbertBroadphase by definition → rfl.
    Stable-tick case: admitted — requires showing ghost equality for all
    entries via `pairsUnchanged` + group structure invariant (follow-on). -/
theorem tickBroadphase_sound (state : TemporalBroadphaseState)
    (currSorted : Array HilbertEntry) (prevResult : BroadphaseResult)
    (hprev : prevResult.pairs =
        (hilbertBroadphase (state.prevSorted.map (·.ghost))).pairs) :
    (tickBroadphase state currSorted prevResult).1.pairs =
    (hilbertBroadphase (currSorted.map (·.ghost))).pairs := by
  simp only [tickBroadphase]
  split
  · rfl
  · sorry
