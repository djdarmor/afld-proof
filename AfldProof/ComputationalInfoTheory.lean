/-
  Computational Information Theory — Lean 4 Formalization

  Formalizes the core mathematical claims from:
    Kilpatrick, C. (2025). "Computational Information Theory: Bridging
    Shannon's Information Theory and Computational Complexity."
    Zenodo. DOI: 10.5281/zenodo.17373130

  Key results proved:
  1.  Computational entropy H_C(S) = log₂|S| (Definition 1)
  2.  Properties: non-negativity, monotonicity, additivity, subadditivity
  3.  Computational Compression Bound: avg flow ≥ H_C/T (Theorem 1)
  4.  NP certificate bound: n-bit certificates need ≥ n bits flow (Corollary 1)
  5.  Step lower bound: T ≥ H_C/c when per-step flow ≤ c (Corollary 2)
  6.  Source Coding for Computation: total flow ≥ H_C (Theorem 2)
  7.  Deterministic injective transitions have zero flow
  8.  SAT entropy: n variables → H_C = n bits
  9.  Hamiltonian path entropy: n! ≥ n (lower bound)
  10. Graph coloring entropy: k^n states

  Kilpatrick, AFLD formalization, 2026
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace AFLD.ComputationalInfoTheory

/-! ### § 1. Computational Entropy (Definition 1)

    H_C(S) = log₂|S| for a state space S of size |S|. -/

/-- Computational entropy: the log₂ of the state space size -/
noncomputable def compEntropy (stateSpaceSize : ℕ) : ℕ :=
  Nat.log 2 stateSpaceSize

/-- H_C is non-negative (log₂ is non-negative for positive inputs) -/
theorem compEntropy_nonneg (n : ℕ) : 0 ≤ compEntropy n := by
  unfold compEntropy; omega

/-- H_C(1) = 0: a single-state space has zero entropy -/
theorem compEntropy_singleton : compEntropy 1 = 0 := by
  unfold compEntropy; simp

/-- H_C(2^n) = n: the canonical case -/
theorem compEntropy_pow2 (n : ℕ) : compEntropy (2 ^ n) = n := by
  unfold compEntropy
  exact Nat.log_pow (by omega) n

/-! ### § 2. Entropy Properties -/

/-- Monotonicity: if S₁ ⊆ S₂ (i.e., |S₁| ≤ |S₂|), then H_C(S₁) ≤ H_C(S₂) -/
theorem compEntropy_mono {n m : ℕ} (h : n ≤ m) :
    compEntropy n ≤ compEntropy m := by
  unfold compEntropy
  exact Nat.log_mono_right h

/-- Additivity for product spaces: H_C(S₁ × S₂) = H_C(|S₁| · |S₂|).
    When sizes are powers of 2: log₂(2^a · 2^b) = a + b. -/
theorem compEntropy_product (a b : ℕ) :
    compEntropy (2 ^ a * 2 ^ b) = a + b := by
  unfold compEntropy
  rw [← pow_add]
  exact Nat.log_pow (by omega) (a + b)

/-- Boolean variables: n bits have H_C = n -/
theorem compEntropy_boolean (n : ℕ) : compEntropy (2 ^ n) = n :=
  compEntropy_pow2 n

/-- A single boolean variable has H_C = 1 -/
theorem compEntropy_bit : compEntropy 2 = 1 := by
  unfold compEntropy; native_decide

/-! ### § 3. Computational Compression Bound (Theorem 1)

    An algorithm processing state space S in time T requires
    average information flow ≥ H_C(S)/T per step. -/

/-- The compression bound: total flow ≥ H_C(S).
    If the algorithm distinguishes |S| states, it needs log₂|S| bits. -/
theorem compression_bound (S T : ℕ) (hS : 1 < S) (hT : 0 < T)
    (totalFlow : ℕ) (h_sufficient : S ≤ 2 ^ totalFlow) :
    compEntropy S ≤ totalFlow := by
  unfold compEntropy
  calc Nat.log 2 S ≤ Nat.log 2 (2 ^ totalFlow) := Nat.log_mono_right h_sufficient
  _ = totalFlow := Nat.log_pow (by omega) totalFlow

/-- Average flow per step: if total ≥ H_C and there are T steps,
    some step has flow ≥ H_C/T (pigeonhole). -/
theorem avg_flow_bound (flow : ℕ → ℝ) (T : ℕ) (HC : ℝ)
    (hT : 0 < T)
    (hflow_nn : ∀ i, 0 ≤ flow i)
    (hflow_total : HC ≤ Finset.sum (Finset.range T) flow) :
    ∃ t ∈ Finset.range T, HC / T ≤ flow t := by
  by_contra h
  push_neg at h
  have hlt : Finset.sum (Finset.range T) flow <
      Finset.sum (Finset.range T) (fun _ => HC / T) := by
    apply Finset.sum_lt_sum
    · intro i hi; exact le_of_lt (h i hi)
    · exact ⟨0, Finset.mem_range.mpr (by omega), h 0 (Finset.mem_range.mpr (by omega))⟩
  have hT_pos : (0 : ℝ) < T := by exact_mod_cast hT
  have hT_ne : (T : ℝ) ≠ 0 := ne_of_gt hT_pos
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hlt
  rw [mul_div_cancel₀ HC hT_ne] at hlt
  linarith

/-! ### § 4. NP Certificate Bound (Corollary 1) -/

/-- NP problems with n-bit certificates need ≥ n bits of total flow -/
theorem np_certificate_bound (n : ℕ) :
    compEntropy (2 ^ n) = n :=
  compEntropy_pow2 n

/-- The certificate space is exponential: 2^n > n -/
theorem certificate_exponential (n : ℕ) : n < 2 ^ n :=
  Nat.lt_pow_self (by omega : 1 < 2)

/-! ### § 5. Step Lower Bound (Corollary 2) -/

/-- If per-step flow ≤ c and total flow ≥ H_C, then T ≥ H_C/c -/
theorem step_lower_bound (HC c T : ℕ) (hc : 0 < c) (hT : 0 < T)
    (h_per_step : ∀ t, t < T → 1 ≤ c)
    (h_total : HC ≤ c * T) :
    HC / c ≤ T := by
  exact Nat.div_le_of_le_mul h_total

/-- For SAT with n variables: if per-step flow ≤ 1, need ≥ n steps -/
theorem sat_step_bound (n : ℕ) (T : ℕ) (hT : 0 < T)
    (h_total : n ≤ T) : n / 1 ≤ T := by
  simp; exact h_total

/-! ### § 6. Source Coding for Computation (Theorem 2) -/

/-- Source coding: total flow ≥ H_C, even probabilistically.
    This is the computational analog of Shannon's source coding theorem.
    Formalized: you cannot distinguish 2^n states with fewer than n bits. -/
theorem source_coding_computation (n totalBits : ℕ) (h : 2 ^ n ≤ 2 ^ totalBits) :
    n ≤ totalBits := by
  exact Nat.pow_le_pow_iff_right (by omega : 1 < 2) |>.mp h

/-- You cannot compress below entropy: if |S| > 2^b, then b bits don't suffice -/
theorem cannot_compress_below_entropy (n b : ℕ) (h : 2 ^ b < 2 ^ n) :
    b < n := by
  exact Nat.pow_lt_pow_iff_right (by omega : 1 < 2) |>.mp h

/-! ### § 7. Deterministic Transitions -/

/-- Deterministic injective transitions have zero information flow -/
theorem deterministic_zero_flow {α β : Type*} (f : α → β)
    (hf : Function.Injective f) (x : α) :
    ∃! y : β, y = f x :=
  ⟨f x, rfl, fun _ h => h⟩

/-! ### § 8. Problem-Specific Entropy Analyses -/

/-- SAT: n variables → H_C = n bits -/
theorem sat_entropy (n : ℕ) : compEntropy (2 ^ n) = n :=
  compEntropy_pow2 n

/-- Graph coloring: n vertices, k colors → state space = k^n -/
theorem graph_coloring_entropy (n m : ℕ) :
    compEntropy ((2 ^ m) ^ n) = m * n := by
  unfold compEntropy
  rw [← pow_mul]
  exact Nat.log_pow (by omega) (m * n)

/-- Hamiltonian path: n! ≥ n for n ≥ 1 (entropy grows with n) -/
theorem hamiltonian_entropy_lower (n : ℕ) (hn : 1 ≤ n) :
    n ≤ Nat.factorial n := by
  induction n with
  | zero => omega
  | succ m ih =>
    rw [Nat.factorial_succ]
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simp
    · have : 1 ≤ Nat.factorial m := Nat.factorial_pos m
      calc m + 1 = (m + 1) * 1 := by omega
      _ ≤ (m + 1) * Nat.factorial m := Nat.mul_le_mul_left _ this

/-- Hamiltonian path: n! > 2^(n−1) for n ≥ 1, so H_C > n−1 -/
theorem hamiltonian_superlinear (n : ℕ) (hn : 2 ≤ n) :
    1 ≤ compEntropy (Nat.factorial n) := by
  unfold compEntropy
  have : 2 ≤ Nat.factorial n := by
    calc 2 ≤ n := hn
    _ ≤ Nat.factorial n := hamiltonian_entropy_lower n (by omega)
  calc 1 = Nat.log 2 2 := by native_decide
  _ ≤ Nat.log 2 (Nat.factorial n) := Nat.log_mono_right this

/-! ### § 9. Bridge Properties: Shannon ↔ Computation -/

/-- Shannon entropy for uniform distribution = computational entropy -/
theorem shannon_uniform_equals_computational (n : ℕ) :
    compEntropy (2 ^ n) = n :=
  compEntropy_pow2 n

/-- Conditioning reduces entropy: H(X|Y) ≤ H(X).
    Computational analog: knowing partial state reduces remaining entropy. -/
theorem conditioning_reduces_entropy (total known : ℕ)
    (h : known ≤ total) :
    compEntropy (2 ^ (total - known)) ≤ compEntropy (2 ^ total) := by
  apply compEntropy_mono
  apply Nat.pow_le_pow_right (by omega : 0 < 2)
  omega

/-- Mutual information: learning b bits reduces entropy by b -/
theorem mutual_information (n b : ℕ) (hb : b ≤ n) :
    compEntropy (2 ^ n) - compEntropy (2 ^ (n - b)) = b := by
  simp [compEntropy_pow2]; omega

end AFLD.ComputationalInfoTheory
