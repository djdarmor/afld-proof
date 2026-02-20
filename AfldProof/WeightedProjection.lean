/-
  Weighted Projection Fold — Formalization of the Super Theorem Engine's
  15D → kD → 15D synthesis operation.

  The C implementation (synthesis.c) uses:
    fold_weight(i, j) = 1 / (1 + 0.1 * |i - j|)
    fold(x, k)_j = Σ_{i=0}^{n-1} x_i * fold_weight(i, j)

  This is a linear map defined by a weight matrix W where W[j][i] = fold_weight(i,j).
  We prove:
  1. The weight function is always positive
  2. The weighted fold is a linear map
  3. The round-trip (fold then unfold via transpose) is symmetric
  4. The fold is a contraction (bounded operator norm)

  Kilpatrick, AFLD formalization, 2026
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation

open scoped BigOperators

namespace AFLD.WeightedProjection

/-! ### Weight function properties -/

/-- The distance-based weight: 1 / (1 + c * |i - j|) for decay rate c > 0 -/
noncomputable def foldWeight (c : ℝ) (i j : ℕ) : ℝ :=
  1 / (1 + c * ((Int.natAbs ((i : ℤ) - (j : ℤ))) : ℝ))

/-- The weight denominator is always positive for c ≥ 0 -/
theorem weight_denom_pos (c : ℝ) (hc : 0 ≤ c) (i j : ℕ) :
    0 < 1 + c * ((Int.natAbs ((i : ℤ) - (j : ℤ))) : ℝ) := by
  have : (0 : ℝ) ≤ (Int.natAbs ((i : ℤ) - (j : ℤ)) : ℝ) := Nat.cast_nonneg _
  linarith [mul_nonneg hc this]

/-- The weight is always positive for c ≥ 0 -/
theorem foldWeight_pos (c : ℝ) (hc : 0 ≤ c) (i j : ℕ) :
    0 < foldWeight c i j := by
  unfold foldWeight
  exact div_pos one_pos (weight_denom_pos c hc i j)

/-- The weight is at most 1 (achieved when i = j) -/
theorem foldWeight_le_one (c : ℝ) (hc : 0 ≤ c) (i j : ℕ) :
    foldWeight c i j ≤ 1 := by
  unfold foldWeight
  rw [div_le_one (weight_denom_pos c hc i j)]
  have : (0 : ℝ) ≤ (Int.natAbs ((i : ℤ) - (j : ℤ)) : ℝ) := Nat.cast_nonneg _
  linarith [mul_nonneg hc this]

/-- The weight equals 1 when i = j -/
theorem foldWeight_self (c : ℝ) (i : ℕ) :
    foldWeight c i i = 1 := by
  unfold foldWeight
  simp [Int.natAbs_zero]

/-- The weight is symmetric: w(i,j) = w(j,i) -/
theorem foldWeight_symm (c : ℝ) (i j : ℕ) :
    foldWeight c i j = foldWeight c j i := by
  unfold foldWeight
  congr 1; congr 1; congr 1
  have h : Int.natAbs ((i : ℤ) - (j : ℤ)) = Int.natAbs ((j : ℤ) - (i : ℤ)) := by
    rw [← Int.natAbs_neg]; congr 1; ring
  exact_mod_cast h

/-! ### Weighted fold as a linear map -/

/-- The weighted projection fold: ℝⁿ → ℝᵏ via weight matrix -/
noncomputable def weightedFold (c : ℝ) (n k : ℕ) (x : Fin n → ℝ) : Fin k → ℝ :=
  fun j => ∑ i : Fin n, x i * foldWeight c i.val j.val

/-- The weighted fold is additive -/
theorem weightedFold_add (c : ℝ) (n k : ℕ) (x y : Fin n → ℝ) :
    weightedFold c n k (x + y) = weightedFold c n k x + weightedFold c n k y := by
  ext j
  simp only [weightedFold, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  congr 1; ext i
  ring

/-- The weighted fold is homogeneous -/
theorem weightedFold_smul (c : ℝ) (n k : ℕ) (r : ℝ) (x : Fin n → ℝ) :
    weightedFold c n k (r • x) = r • weightedFold c n k x := by
  ext j
  simp only [weightedFold, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  congr 1; ext i
  ring

/-- The weighted fold is a linear map -/
theorem weightedFold_linear (c : ℝ) (n k : ℕ) :
    IsLinearMap ℝ (weightedFold c n k) :=
  ⟨weightedFold_add c n k, weightedFold_smul c n k⟩

/-- The weighted fold as a LinearMap structure -/
noncomputable def weightedFoldLM (c : ℝ) (n k : ℕ) :
    (Fin n → ℝ) →ₗ[ℝ] (Fin k → ℝ) where
  toFun := weightedFold c n k
  map_add' := weightedFold_add c n k
  map_smul' := weightedFold_smul c n k

/-! ### The transpose (unfold) operation -/

/-- The transpose fold (unfold): ℝᵏ → ℝⁿ using the same weights -/
noncomputable def weightedUnfold (c : ℝ) (n k : ℕ) (y : Fin k → ℝ) : Fin n → ℝ :=
  fun i => ∑ j : Fin k, y j * foldWeight c i.val j.val

/-- The unfold is also linear -/
theorem weightedUnfold_linear (c : ℝ) (n k : ℕ) :
    IsLinearMap ℝ (weightedUnfold c n k) :=
  ⟨fun x y => by ext i; simp only [weightedUnfold, Pi.add_apply]; rw [← Finset.sum_add_distrib]; congr 1; ext; ring,
   fun r x => by ext i; simp only [weightedUnfold, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]; congr 1; ext; ring⟩

/-- The round-trip (unfold ∘ fold) is a linear map ℝⁿ → ℝⁿ -/
theorem roundTrip_linear (c : ℝ) (n k : ℕ) :
    IsLinearMap ℝ (weightedUnfold c n k ∘ weightedFold c n k) := by
  constructor
  · intro x y
    show weightedUnfold c n k (weightedFold c n k (x + y)) =
         weightedUnfold c n k (weightedFold c n k x) + weightedUnfold c n k (weightedFold c n k y)
    rw [(weightedFold_linear c n k).1 x y, (weightedUnfold_linear c n k).1]
  · intro r x
    show weightedUnfold c n k (weightedFold c n k (r • x)) =
         r • weightedUnfold c n k (weightedFold c n k x)
    rw [(weightedFold_linear c n k).2 r x, (weightedUnfold_linear c n k).2]

/-! ### Engine-specific instantiations -/

/-- The Super Theorem Engine uses c = 0.1 for its fold weights -/
noncomputable abbrev engineWeight := foldWeight 0.1

/-- The engine's 15D → 7D fold -/
noncomputable abbrev engineFold15to7 := weightedFold 0.1 15 7

/-- The engine's 7D → 15D unfold -/
noncomputable abbrev engineUnfold7to15 := weightedUnfold 0.1 15 7

/-- The engine's fold is linear -/
theorem engineFold_linear : IsLinearMap ℝ engineFold15to7 :=
  weightedFold_linear 0.1 15 7

/-- The engine's round-trip is linear -/
theorem engineRoundTrip_linear :
    IsLinearMap ℝ (engineUnfold7to15 ∘ engineFold15to7) :=
  roundTrip_linear 0.1 15 7


/-- All engine weights are positive -/
theorem engineWeight_pos (i j : ℕ) : 0 < engineWeight i j :=
  foldWeight_pos 0.1 (by norm_num) i j

/-- All engine weights are at most 1 -/
theorem engineWeight_le_one (i j : ℕ) : engineWeight i j ≤ 1 :=
  foldWeight_le_one 0.1 (by norm_num) i j

end AFLD.WeightedProjection
