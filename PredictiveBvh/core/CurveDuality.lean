-- SPDX-License-Identifier: MIT
-- Copyright (c) 2026-present K. S. Ernest (iFire) Lee

-- ============================================================================
-- WHY THIS REPOSITORY CARRIES TWO SPACE-FILLING CURVES
--
-- `HilbertCell`/`HilbertBroadphase` sort, partition and address by Hilbert code.
-- A butterfly routing overlay (log-depth propagation between zones) cannot use
-- Hilbert and needs Morton. That is not a preference between two similar things;
-- the two curves have different algebra and each is load-bearing where it sits.
--
-- Morton is a bit permutation, so it is GF(2)-LINEAR: morton(a XOR b) =
-- morton(a) XOR morton(b). A butterfly network is the Cayley graph of (Z/2)^n
-- under XOR, so its stages are exactly XOR by a basis vector. Linearity is what
-- makes stage k a spatial translation instead of an arbitrary jump.
--
-- Hilbert is NOT linear. Each level applies a rotation chosen by the prefix, so
-- bit k has no fixed spatial meaning. What it buys instead is contiguity: h and
-- h+1 are always adjacent cells, which is what makes a Hilbert code PREFIX a
-- compact region — the property zone partitioning and bucket ranges are built on.
--
-- Neither is the other's dual. (Z/2)^n is Pontryagin SELF-dual, so the linear
-- structure Morton lives in is its own dual — which is why a butterfly can be
-- transposed and run in reverse at all. Hilbert has no characters to dualise.
--
-- The theorems below are the evidence for each half, so a later reader can see
-- that dropping one curve costs something measured rather than something felt.
-- ============================================================================

namespace CurveDuality

/-- Morton (Z-order) code, 2D, `order` bits per axis. A pure interleave of the
    coordinate bits, hence a permutation matrix over GF(2). -/
def morton2 (order x y : Nat) : Nat :=
  (List.range order).foldl
    (fun acc i => acc ||| (((x >>> i) &&& 1) <<< (2 * i)) ||| (((y >>> i) &&& 1) <<< (2 * i + 1)))
    0

/-- One level of the Hilbert rotation. `n` is the FULL grid width, not the current
    step: reflecting about the sub-square would be a different (and wrong) curve,
    and in `Nat` it also truncates at zero rather than failing loudly. -/
private def hilbertRot (n rx ry x y : Nat) : Nat × Nat :=
  if ry == 0 then
    let (x, y) := if rx == 1 then (n - 1 - x, n - 1 - y) else (x, y)
    (y, x)
  else (x, y)

private def hilbert2Go : Nat → Nat → Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _, _, d => d
  | fuel + 1, n, s, x, y, d =>
    if s == 0 then d
    else
      let rx := if x &&& s != 0 then 1 else 0
      let ry := if y &&& s != 0 then 1 else 0
      let d := d + s * s * ((3 * rx) ^^^ ry)
      let (x, y) := hilbertRot n rx ry x y
      hilbert2Go fuel n (s / 2) x y d

/-- Hilbert index of `(x, y)` on a `2^order` square (Skilling / the standard xy2d). -/
def hilbert2 (order x y : Nat) : Nat :=
  let n := 1 <<< order
  hilbert2Go (order + 1) n (n / 2) x y 0

-- ============================================================================
-- HALF ONE: MORTON IS LINEAR, HILBERT IS NOT
-- ============================================================================

/-- Every cell of a `2^order` square, as `(x, y)`. -/
def cells (order : Nat) : List (Nat × Nat) :=
  let n := 1 <<< order
  (List.range n).flatMap fun x => (List.range n).map fun y => (x, y)

/-- How many `(a, b)` pairs satisfy `f (a XOR b) = f a XOR f b`, out of how many tried.
    Linearity is exactly this holding everywhere. -/
def linearityScore (f : Nat → Nat → Nat) (order : Nat) : Nat × Nat :=
  let cs := cells order
  let ps := cs.flatMap fun a => cs.map fun b => (a, b)
  (ps.countP (fun (a, b) => f (a.1 ^^^ b.1) (a.2 ^^^ b.2) == (f a.1 a.2) ^^^ (f b.1 b.2)),
   ps.length)

/-- Morton is GF(2)-linear: the identity holds for every pair on a 8x8 square. -/
theorem morton_is_linear : linearityScore (morton2 3) 3 = (4096, 4096) := by native_decide

/-- Hilbert is not. It holds for 1600 of 4096 pairs — a large minority, which is
    the trap: sampling a few pairs can make Hilbert look linear. It is not, and a
    butterfly stage needs the identity to hold for EVERY pair, not most. -/
theorem hilbert_is_not_linear : linearityScore (hilbert2 3) 3 = (1600, 4096) := by native_decide

/-- Both are bijections onto `[0, 4^order)`, so the difference above is about
    algebra and not about one of them being a worse addressing scheme. -/
theorem both_are_bijections :
    ((cells 3).map (fun c => morton2 3 c.1 c.2)).eraseDups.length = 64 ∧
    ((cells 3).map (fun c => hilbert2 3 c.1 c.2)).eraseDups.length = 64 := by native_decide

-- ============================================================================
-- HALF TWO: HILBERT IS CONTIGUOUS, MORTON IS NOT
--
-- The metric is CLUSTER COUNT (Moon et al. 2001): given a query rectangle, sort
-- its cells by curve code and count maximal runs of consecutive codes. That is
-- the number of disjoint code RANGES the region costs — which is precisely what
-- a zone span, a bucket range, or an authority prefix has to enumerate.
-- ============================================================================

/-- Cells of the `w` x `w` window whose corner is `(x0, y0)`. -/
def window (w x0 y0 : Nat) : List (Nat × Nat) :=
  (List.range w).flatMap fun dx => (List.range w).map fun dy => (x0 + dx, y0 + dy)

/-- Maximal runs of consecutive values in a sorted list. -/
private def runs : List Nat → Nat
  | [] => 0
  | c :: cs => cs.foldl (fun (acc : Nat × Nat) v =>
      (if v == acc.2 + 1 then acc.1 else acc.1 + 1, v)) (1, c) |>.1

/-- Disjoint code ranges a `w` x `w` query costs under curve `f`. -/
def clusters (f : Nat → Nat → Nat) (w x0 y0 : Nat) : Nat :=
  runs ((window w x0 y0).map (fun c => f c.1 c.2)).mergeSort

/-- Total clusters over every 3x3 window of a 16x16 grid: the whole-grid figure,
    so no window choice is doing the work. -/
def totalClusters (f : Nat → Nat → Nat) : Nat :=
  ((List.range 14).flatMap fun x0 => (List.range 14).map fun y0 => clusters f 3 x0 y0).sum

/-- Hilbert costs strictly fewer ranges than Morton over every window. This is
    the whole reason partitioning, bucket directories and geometric authority are
    keyed on Hilbert: a prefix stays compact. -/
theorem hilbert_clusters_better : totalClusters (hilbert2 4) < totalClusters (morton2 4) := by
  native_decide

/-- Concretely, and this is the number worth quoting when someone proposes
    dropping one of the two curves. -/
theorem cluster_counts : totalClusters (hilbert2 4) = 568 ∧ totalClusters (morton2 4) = 868 := by
  native_decide

/-- The worst single window is where it bites: Morton's Z jump crosses a quadrant
    boundary and shatters a 9-cell query into many ranges. -/
def worstWindow (f : Nat → Nat → Nat) : Nat :=
  ((List.range 14).flatMap fun x0 => (List.range 14).map fun y0 => clusters f 3 x0 y0).foldl max 0

theorem worst_window_counts : worstWindow (hilbert2 4) = 4 ∧ worstWindow (morton2 4) = 5 := by
  native_decide

-- ============================================================================
-- CONCLUSION, AS A PAIR OF FACTS RATHER THAN A PREFERENCE
-- ============================================================================

/-- Neither curve dominates: Morton wins the algebra, Hilbert wins the locality.
    A design that keeps only one gives up whichever column it dropped. -/
theorem neither_curve_dominates :
    (linearityScore (morton2 3) 3).1 > (linearityScore (hilbert2 3) 3).1 ∧
    totalClusters (hilbert2 4) < totalClusters (morton2 4) := by native_decide

def printCurveComparison : IO Unit := do
  let (ml, mt) := linearityScore (morton2 3) 3
  let (hl, _) := linearityScore (hilbert2 3) 3
  IO.println "── Why both curves are kept ──"
  IO.println s!"  linear f(a^b)=f(a)^f(b)   Morton {ml}/{mt}   Hilbert {hl}/{mt}"
  IO.println s!"  query ranges (3x3, 16x16) Morton {totalClusters (morton2 4)}      Hilbert {totalClusters (hilbert2 4)}"
  IO.println s!"  worst single window       Morton {worstWindow (morton2 4)}        Hilbert {worstWindow (hilbert2 4)}"
  IO.println "  Morton -> butterfly routing (needs GF(2) structure)"
  IO.println "  Hilbert -> zone spans, bucket ranges, geometric authority (needs contiguity)"

end CurveDuality
