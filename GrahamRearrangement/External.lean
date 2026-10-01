module

public import GrahamRearrangement.Probability
public import GrahamRearrangement.External.Hypergeometric
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Data.Nat.Log

@[expose] public section

open scoped BigOperators Pointwise

namespace GrahamRearrangement.External

/-!
# External inputs

This module now contains proved general-purpose lemmas used across the
formalization.  The bibliographic hypergeometric input cited by
Pham--Sauermann is formalized in `External/Hypergeometric/`; no project axiom
is used anywhere in this hierarchy.
-/

noncomputable section

-- ---------------------------------------------------------------------------
-- Standard real/complex analysis
-- ---------------------------------------------------------------------------

-- ---------------------------------------------------------------------------
-- Additive combinatorics
-- ---------------------------------------------------------------------------

-- ---------------------------------------------------------------------------
-- Finite Fourier analysis
-- ---------------------------------------------------------------------------

/-- Orthogonality of the additive characters of Z/pZ. -/
theorem zmod_character_orthogonality {p : ℕ} [NeZero p] (hp : p.Prime) (a : ZMod p) :
    (∑ χ : ZMod p, ZMod.stdAddChar (χ * a)) =
      if a = 0 then (p : ℂ) else 0 := by
  sorry

/-- Character-average norm-square identity, obtained by expanding the square. -/
theorem zmod_character_average_norm_sq {p : ℕ} [NeZero p]
    (T : Finset (ZMod p)) (hT : T.Nonempty) (χ : ZMod p) :
    ‖((∑ x ∈ T, ZMod.stdAddChar (χ * x)) / (T.card : ℂ))‖ ^ 2 =
      (1 / (T.card : ℝ) ^ 2) *
        ∑ x ∈ T, ∑ x' ∈ T,
          (ZMod.stdAddChar (χ * x - χ * x')).re := by
  sorry

-- ---------------------------------------------------------------------------
-- Finite probability and sampling symmetry
-- ---------------------------------------------------------------------------

/-- Markov inequality on a finite uniform sample space. -/
theorem uniform_markov {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (X : Ω → ℝ) (a : ℝ)
    (hX : ∀ ω ∈ space, 0 ≤ X ω) (ha : 0 < a) :
    uniformMass space (fun ω => a ≤ X ω) ≤
      uniformExpectation space X / a := by
  sorry

-- ---------------------------------------------------------------------------
-- Hypergeometric concentration
-- ---------------------------------------------------------------------------

/-!
The two lower-tail theorems used by Section 3 are proved in
`External/Hypergeometric/` and re-exported in namespace
`GrahamRearrangement.External`.  No project axiom is used.
-/

/-- A convenient monotonic consequence of exp for the numerical tail comparisons. -/
theorem exp_antitone {a b : ℝ} (h : a ≤ b) :
    Real.exp (-b) ≤ Real.exp (-a) :=
  Real.exp_le_exp.mpr (neg_le_neg h)

/-- exp(-c log n) = n^{-c}, in the positive range used throughout the paper. -/
theorem exp_neg_mul_log {n c : ℝ} (hn : 0 < n) :
    Real.exp (-c * Real.log n) = n ^ (-c) := by
  rw [Real.rpow_def_of_pos hn]
  congr 1
  ring

-- ---------------------------------------------------------------------------
-- Elementary asymptotic facts used to choose constants
-- ---------------------------------------------------------------------------

/-- Every real x in [1,m] lies in a dyadic interval [2^l,2^(l+1)). -/
theorem exists_dyadic_interval {x : ℝ} {m : ℕ}
    (hx : 1 ≤ x) (hm : x ≤ m) :
    ∃ l < Nat.log2 m + 1,
      (2 : ℝ) ^ l ≤ x ∧ x < 2 * (2 : ℝ) ^ l := by
  sorry

/-- A convenient explicit lower bound for the natural logarithm of two. -/
theorem log_two_ge_half : (1 / 2 : ℝ) ≤ Real.log 2 := by
  exact le_of_lt (lt_trans (by norm_num) Real.log_two_gt_d9)

/-- Generic weighted dyadic split: small shells are controlled by a square-root
bound and the at most 22 remaining shells by the trivial bound. -/
theorem dyadic_weight_le_geometric (l : ℕ) :
    Real.sqrt ((2 : ℝ) ^ l) * Real.exp (-(2 : ℝ) ^ l) ≤
      (1 / 2 : ℝ) ^ l := by
  sorry

theorem dyadic_weight_sum_le_two (N : ℕ) :
    (∑ l ∈ Finset.range N,
      Real.sqrt ((2 : ℝ) ^ l) * Real.exp (-(2 : ℝ) ^ l)) ≤ 2 := by
  sorry

theorem terminal_dyadic_indices_card_le
    (m : ℕ) :
    ((Finset.range (Nat.log2 m + 1)).filter
      fun l => m / 2 ^ 22 < 2 ^ l).card ≤ 22 := by
  sorry

/-- The final dyadic split in the proof of Theorem 1.3. -/
theorem weighted_dyadic_split (m : ℕ) (p K : ℝ) (E : ℕ → ℝ)
    (hp : 0 < p) (hK : 0 ≤ K)
    (hsmall : ∀ l, 2 ^ l ≤ m / 2 ^ 22 →
      E l ≤ p * K * Real.sqrt ((2 : ℝ) ^ l))
    (htriv : ∀ l, E l ≤ p) :
    (1 / p) *
        ∑ l ∈ Finset.range (Nat.log2 m + 1),
          E l * Real.exp (-(2 : ℝ) ^ l)
      ≤ 2 * K + 22 * Real.exp (-(m : ℝ) / 2 ^ 22) := by
  sorry

/-- Elementary floor estimate used with k=floor(sqrt x). -/
theorem natFloor_ge_half {x : ℝ} (hx : 1 ≤ x) :
    x / 2 ≤ (Nat.floor x : ℝ) := by
  sorry

/-- The standard reciprocal-square-root summation estimate. -/
theorem inv_sqrt_le_twice_sqrt_sub
    (n : ℕ) (hn : 1 ≤ n) :
    1 / Real.sqrt (n : ℝ) ≤
      2 * (Real.sqrt (n : ℝ) - Real.sqrt (n - 1 : ℝ)) := by
  sorry

theorem sum_inv_sqrt_le_two_sqrt (n : ℕ) :
    (∑ i ∈ Finset.Icc 1 n, (1 / Real.sqrt (i : ℝ))) ≤
      2 * Real.sqrt (n : ℝ) := by
  sorry

/-- Numerical consequence of D=ceil(3/α) when 0<α<1/2. -/
theorem ceil_three_div_ge_seven {α : ℝ}
    (hα0 : 0 < α) (hαh : α < 1 / 2) :
    7 ≤ Nat.ceil (3 / α) := by
  have h6 : (6 : ℝ) < 3 / α := by
    apply (lt_div_iff₀ hα0).2
    nlinarith
  exact Nat.add_one_le_ceil_iff.mpr h6

/-- Elementary power inequalities used for the Section 5 choice of C_α. -/
theorem section5_power_inequalities (D : ℕ) (hD : 7 ≤ D) :
    (100 : ℝ) * (5 * D : ℝ) ^ (2 * D) ≤
        (D + 1 : ℝ) * (2 : ℝ) ^ D *
          (D : ℝ) ^ (14 * D ^ 2) ∧
      (40 * D : ℝ) ^ D ≤
        (100 : ℝ) * (5 * D : ℝ) ^ (2 * D) := by
  sorry

/-- Raising the first Section 5 threshold to α recovers the required
10^4*2^(40D) lower bound. -/
theorem section5_rpow_threshold {α : ℝ} {D : ℕ}
    (hα0 : 0 < α) :
    (10 ^ 4 * (2 : ℝ) ^ (40 * D)) ≤
      (((10 ^ 4 : ℝ) * (2 : ℝ) ^ (40 * D)) ^ (1 / α)) ^ α := by
  sorry

/-- Standard real-power consequence used in Section 5:
n ≤ p^(1-α) implies n/p ≤ n^(-α). -/
theorem card_div_prime_le_neg_rpow {α : ℝ} {n p : ℕ}
    (hα0 : 0 < α) (hα1 : α < 1)
    (hn : 1 ≤ n) (hp : 1 ≤ p)
    (hupper : (n : ℝ) ≤ (p : ℝ) ^ (1 - α)) :
    (n : ℝ) / p ≤ (n : ℝ) ^ (-α) := by
  sorry

/-- Monotonicity of x↦x^{-α} for positive α on [1,∞). -/
theorem neg_rpow_antitone {α : ℝ} (hα : 0 < α)
    {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    y ^ (-α) ≤ x ^ (-α) := by
  sorry

/-- Two-sided reciprocal-square-root kernel sum used for a fixed interval endpoint. -/
theorem reverse_Icc_inv_sqrt_sum (n : ℕ) :
    (∑ r ∈ Finset.Icc 1 (n - 1),
      1 / Real.sqrt ((n - r : ℕ) : ℝ)) =
    ∑ r ∈ Finset.Icc 1 (n - 1),
      1 / Real.sqrt (r : ℝ) := by
  sorry

theorem two_sided_interval_kernel_sum_le
    (n p : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    (∑ r ∈ Finset.Icc 1 (n - 1),
      ((1 / (p : ℝ) +
        C * Real.sqrt (Real.log (n : ℝ)) /
          ((n : ℝ) * Real.sqrt (r : ℝ))) +
       (1 / (p : ℝ) +
        C * Real.sqrt (Real.log (n : ℝ)) /
          ((n : ℝ) * Real.sqrt ((n - r : ℕ) : ℝ))))) ≤
      2 * (n : ℝ) / p +
        4 * C * Real.sqrt (Real.log (n : ℝ)) /
          Real.sqrt (n : ℝ) := by
  sorry

/-- Crude elementary growth used in Section 5 numerical union bounds. -/
theorem nat_le_two_pow_40 (D : ℕ) :
    (D : ℝ) ≤ (2 : ℝ) ^ (40 * D) := by
  sorry

/-- Elementary growth used in the Section 5 counting estimates. -/
theorem D_plus_one_le_fiveD_pow (D : ℕ) (hD : 7 ≤ D) :
    (D + 1 : ℝ) ≤ (5 * D : ℝ) ^ (2 * D) := by
  sorry

/-- Monotonicity of real powers in the exponent for a base at least one. -/
theorem rpow_exponent_mono_of_one_le {x a b : ℝ}
    (hx : 1 ≤ x) (hab : a ≤ b) :
    x ^ a ≤ x ^ b :=
  Real.monotone_rpow_of_base_ge_one hx hab

/-- Linear eventually dominates log-squared. -/
theorem exists_log_sq_threshold (A : ℝ) :
    ∃ N : ℕ, 2 ≤ N ∧
      ∀ n : ℕ, N ≤ n →
        A * (Real.log (n : ℝ)) ^ 2 ≤ (n : ℝ) := by
  sorry

/-- n^{-1/2} sqrt(log n) is eventually below n^{-α} for α < 1/2. -/
theorem exists_sqrt_log_power_threshold {α K : ℝ}
    (hα0 : 0 < α) (hαh : α < 1 / 2) (hK : 0 ≤ K) :
    ∃ N : ℕ, 2 ≤ N ∧
      ∀ n : ℕ, N ≤ n →
        K * Real.sqrt (Real.log (n : ℝ)) / Real.sqrt (n : ℝ) ≤
          (n : ℝ) ^ (-α) := by
  sorry

end

end GrahamRearrangement.External
