module

public import GrahamRearrangement.Combinatorial.Corollary42

@[expose] public section

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Lemma 4.3

The induction inequality (4.1), the omitted-gap factorization, and the final sum.
-/

noncomputable section

def lemma43Base (p n : ℕ) (C : ℝ) : ℝ :=
  (n : ℝ) / p +
    2 * C * Real.sqrt (Real.log (n : ℝ)) /
      Real.sqrt (n : ℝ)

theorem lemma43_kernel_nonneg {p n : ℕ} (hp : p.Prime)
    (C : ℝ) (hC : 0 < C) :
    ∀ d, 0 ≤ lemma43Kernel p n C d := by
  intro d
  unfold lemma43Kernel chainFactor
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  positivity

theorem lemma43_kernel_row_bound {p n : ℕ} (hp : p.Prime)
    (hn : 2 ≤ n) (C : ℝ) (hC : 0 < C)
    (a : ℕ) (ha : a < n) :
    (∑ d ∈ Finset.Icc 1 (n - a),
        lemma43Kernel p n C d) ≤
      lemma43Base p n C := by
  sorry

/-- Equation (4.1). -/
theorem equation_4_1 {p n h : ℕ} (hp : p.Prime)
    (hn : 2 ≤ n) (C : ℝ) (hC : 0 < C) :
    prefixKernelSum n h (lemma43Kernel p n C) ≤
      (lemma43Base p n C) ^ h := by
  apply Section4External.prefixKernelSum_le_pow
  · exact lemma43_kernel_nonneg hp C hC
  · intro a ha
    exact lemma43_kernel_row_bound hp hn C hC a ha

/-- The fixed-j estimate (4.14 in the prose following (4.1)): after omitting the
j-th gap the left and reversed-right tuple sums are independent upper bounds. -/
theorem lemma43_fixed_j {p n k : ℕ} (hp : p.Prime)
    (hn : 2 ≤ n) (C : ℝ) (hC : 0 < C)
    (j : Fin (k + 1)) :
    omittedKernelSum n k (lemma43Kernel p n C) j ≤
      (lemma43Base p n C) ^ k := by
  sorry

theorem lemma43LHS_eq_sum_omitted (p n k : ℕ) (C : ℝ) :
    lemma43LHS p n k C =
      ∑ j : Fin (k + 1),
        omittedKernelSum n k (lemma43Kernel p n C) j := by
  sorry

/-- Lemma 4.3. -/
theorem lemma4_3 : Lemma43Statement := by
  intro k hk Ck hCk p hp n hn
  rw [lemma43LHS_eq_sum_omitted]
  have hfixed : ∀ j : Fin (k + 1),
      omittedKernelSum n k (lemma43Kernel p n Ck) j ≤
        (lemma43Base p n Ck) ^ k :=
    lemma43_fixed_j hp hn Ck hCk
  calc
    ∑ j : Fin (k + 1),
        omittedKernelSum n k (lemma43Kernel p n Ck) j
      ≤ ∑ _j : Fin (k + 1),
          (lemma43Base p n Ck) ^ k := by
          gcongr with j
          exact hfixed j
    _ = (k + 1 : ℝ) * (lemma43Base p n Ck) ^ k := by
          simp
    _ = lemma43RHS p n k Ck := by
          unfold lemma43RHS lemma43Base
          rfl

end

end GrahamRearrangement
