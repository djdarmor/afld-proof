/-
  Verification Bridge — 15D Super Theorem Engine → Lean 4

  Instantiates the generic AFLD theorems at specific dimensions relevant
  to the Super Theorem Engine (n=8 for 15D→8D folding, n=15 for full space).

  This module provides concrete, machine-checked witnesses that the
  Super Theorem Engine can reference. Each theorem below is a direct
  specialization of a generic result — no sorry, no axiom.

  Kilpatrick, AFLD formalization, 2026
-/

import AfldProof.PairwiseAverage
import AfldProof.InformationLoss
import AfldProof.FermatBridge
import AfldProof.CyclicPreservation
import AfldProof.SignedFoldingCeiling
import AfldProof.DimensionalSeparation
import AfldProof.CompressionPipeline

namespace AFLD.Bridge

-- ============================================================
-- § 1. Fold linearity at engine-relevant dimensions
-- ============================================================

/-- The 15D→8D pairwise fold is linear (engine uses k=7 fold, closest even: 2×8=16→8) -/
theorem fold_linear_8 : IsLinearMap ℝ (AFLD.pairwiseFold 8) :=
  AFLD.pairwiseFold_linear 8

/-- The 30D→15D pairwise fold is linear (full 15D space: 2×15=30→15) -/
theorem fold_linear_15 : IsLinearMap ℝ (AFLD.pairwiseFold 15) :=
  AFLD.pairwiseFold_linear 15

-- ============================================================
-- § 2. Rank-nullity at engine dimensions
-- ============================================================

/-- 30→15 fold: rank = 15 (preserves exactly 15 dimensions of information) -/
theorem fold_rank_15 : Module.finrank ℝ (LinearMap.range (InfoLoss.foldMap 15)) = 15 :=
  InfoLoss.foldMap_rank 15 (by omega)

/-- 30→15 fold: nullity = 15 (destroys exactly 15 dimensions) -/
theorem fold_nullity_15 : Module.finrank ℝ (LinearMap.ker (InfoLoss.foldMap 15)) = 15 :=
  InfoLoss.foldMap_nullity 15 (by omega)

/-- 16→8 fold: rank = 8 -/
theorem fold_rank_8 : Module.finrank ℝ (LinearMap.range (InfoLoss.foldMap 8)) = 8 :=
  InfoLoss.foldMap_rank 8 (by omega)

/-- 16→8 fold: nullity = 8 -/
theorem fold_nullity_8 : Module.finrank ℝ (LinearMap.ker (InfoLoss.foldMap 8)) = 8 :=
  InfoLoss.foldMap_nullity 8 (by omega)

-- ============================================================
-- § 3. Fermat bridge at small primes (engine test values)
-- ============================================================

/-- For any prime p ≥ 2, (ℤ/pℤ)ˣ is cyclic — the foundation of the engine's
    symmetry group dimension (D7). -/
theorem cyclic_group_any_prime (p : ℕ) [hp : Fact (Nat.Prime p)] :
    IsCyclic (ZMod p)ˣ :=
  inferInstance

-- ============================================================
-- § 4. Engine dimension coverage
-- ============================================================

/-- D2 (algebraic closure): fold is a linear map → closed under addition and scaling.
    Verified for ANY n. -/
theorem d2_algebraic_closure (n : ℕ) : IsLinearMap ℝ (AFLD.pairwiseFold n) :=
  AFLD.pairwiseFold_linear n

/-- D8 (conservation laws): rank + nullity = input dimension.
    Information conserved (just redistributed between preserved and destroyed). -/
theorem d8_conservation (n : ℕ) :
    Module.finrank ℝ (LinearMap.range (InfoLoss.foldMap n))
    + Module.finrank ℝ (LinearMap.ker (InfoLoss.foldMap n))
    = 2 * n :=
  InfoLoss.foldMap_rank_nullity n

/-- D10 (information): raw fold preserves exactly n out of 2n dimensions = 50%.
    Claims above 50% require cyclic encoding (D7 + D15). -/
theorem d10_raw_preservation (n : ℕ) (hn : 0 < n) :
    Module.finrank ℝ (LinearMap.range (InfoLoss.foldMap n)) = n :=
  InfoLoss.foldMap_rank n hn

/-- D10 + D7 + D15 (information + symmetry + self-reference):
    with cyclic encoding, the pipeline is exactly lossless.
    The Fermat bridge round-trip is the identity. -/
theorem d10_d7_d15_cyclic_lossless (p : ℕ) [hp : Fact (Nat.Prime p)] [_hp2 : Fact (2 < p)]
    (g : (ZMod p)ˣ) (hg : ∀ a, a ∈ Subgroup.zpowers g)
    (k : Fin (p - 1)) :
    (FermatBridge.bridgeEquiv p g hg).symm
      ((FermatBridge.bridgeEquiv p g hg) k) = k :=
  (FermatBridge.bridgeEquiv p g hg).symm_apply_apply k

end AFLD.Bridge
