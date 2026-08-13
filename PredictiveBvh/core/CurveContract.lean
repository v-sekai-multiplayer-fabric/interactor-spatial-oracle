-- SPDX-License-Identifier: MIT
-- Copyright (c) 2026-present K. S. Ernest (iFire) Lee

import Shared.Types

-- ============================================================================
-- WHAT THIS REPOSITORY REQUIRES OF THE CURVE IT IS PINNED TO
--
-- `lean-shared-core` gates `hilbert3D` on its own side, and that gate is correct
-- and did its job. It also runs nowhere near the failure this file exists for.
--
-- `lake-manifest.json` pins `lean-shared-core` by REV, not by branch. `inputRev`
-- reads `main`, but `rev` is a fixed commit and Lake moves it only on `lake
-- update`. So an upstream fix can merge and change nothing here, and an upstream
-- rewrite can change the curve under this repository without any diff in it.
--
-- That is not hypothetical. The forward fix and the matching inverse merged
-- eleven seconds apart, in the right order, both landing every commit — and this
-- repository stayed broken afterwards, holding the corrected inverse against the
-- old forward, because the pin had not moved. Both round trips still closed. They
-- closed on the wrong cell, which is the same way the original defect survived.
--
-- So the contract is asserted HERE, against whatever encoder is actually pinned,
-- rather than trusted because a dependency asserts it about itself. A stale or
-- rolled-back pin now fails this build instead of silently changing the curve.
--
-- Kept deliberately cheap. The exhaustive version lives upstream where the
-- implementation does; this is a tripwire, and a tripwire that costs a second is
-- one nobody deletes.
-- ============================================================================

namespace CurveContract

/-- Every cell of an `n`-cube. -/
def cells (n : Nat) : List (Nat × Nat × Nat) :=
  (List.range n).flatMap fun x => (List.range n).flatMap fun y => (List.range n).map fun z => (x, y, z)

/-- Codes whose `3*d`-bit prefix does not name their own octree cell at depth `d`.
    This is the property a zone span IS, so it is the one worth pinning. -/
def prefixDefects (n d : Nat) : Nat :=
  let shift := if d ≤ 10 then 10 - d else 0
  ((cells n).filter (fun c =>
    let code := morton3D c.1 c.2.1 c.2.2
    let origin := morton3D ((c.1 >>> shift) <<< shift) ((c.2.1 >>> shift) <<< shift)
      ((c.2.2 >>> shift) <<< shift)
    ¬ (code >>> (3 * shift) = origin >>> (3 * shift)))).length

/-- THE TRIPWIRE. Not "is the dependency's test green" -- that test is not run by this
    build -- but "does the curve we are compiled against still partition the way this
    repository's spans assume". -/
theorem pinned_curve_prefix_is_the_octree_cell :
    prefixDefects 8 6 = 0 ∧ prefixDefects 8 8 = 0 ∧ prefixDefects 8 10 = 0 := by native_decide

/-- Round-trip, which is necessary and by itself proves nothing -- kept deliberately, since
    a passing round-trip is exactly what let a broken curve through here twice. -/
theorem pinned_curve_roundtrips :
    ((cells 8).filter (fun c =>
      ¬ (morton3DInverse (morton3D c.1 c.2.1 c.2.2) = (c.1, c.2.1, c.2.2)))).length = 0 := by
  native_decide

/-- A canary on exact values, because the properties above hold for more than one curve.
    Any change to the encoder -- orientation, bit order, order parameter -- moves these, and
    moving them silently is the failure mode.

    These are Morton values. The previous three were a corrected Hilbert's, and the three
    before that a broken Hilbert's; each time the change was invisible from here until this
    theorem started failing, which is the whole reason it exists. -/
theorem pinned_curve_values :
    morton3D 0 0 0 = 0 ∧
    morton3D 512 0 0 = 536870912 ∧
    morton3D 1023 1023 1023 = 1073741823 := by native_decide

end CurveContract
