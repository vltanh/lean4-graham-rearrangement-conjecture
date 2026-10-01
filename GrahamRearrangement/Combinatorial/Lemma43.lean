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
  unfold lemma43Kernel chainFactor lemma43Base
  rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hnR : (0 : ℝ) < n := by positivity
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  have hL := Real.sqrt_nonneg (Real.log (n : ℝ))
  have h1 : ((n - a + 1 - 1 : ℕ) : ℝ) * (1 / (p : ℝ)) ≤ (n : ℝ) / p := by
    rw [mul_one_div]
    apply div_le_div_of_nonneg_right _ hpR.le
    exact_mod_cast (show n - a + 1 - 1 ≤ n by omega)
  have h2 : ∑ d ∈ Finset.Icc 1 (n - a),
      C * Real.sqrt (Real.log (n : ℝ)) / ((n : ℝ) * Real.sqrt (d : ℝ)) =
      (C * Real.sqrt (Real.log (n : ℝ)) / n) *
        ∑ d ∈ Finset.Icc 1 (n - a), 1 / Real.sqrt (d : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    ring
  have h3 : ∑ d ∈ Finset.Icc 1 (n - a), 1 / Real.sqrt (d : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by
    refine (Section4.sum_one_div_sqrt_le (n - a)).trans ?_
    gcongr
    exact_mod_cast Nat.sub_le n a
  have h4 : (C * Real.sqrt (Real.log (n : ℝ)) / n) * (2 * Real.sqrt (n : ℝ)) =
      2 * C * Real.sqrt (Real.log (n : ℝ)) / Real.sqrt (n : ℝ) := by
    have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = n := Real.mul_self_sqrt hnR.le
    rw [div_mul_eq_mul_div, div_eq_div_iff hnR.ne' hsn.ne']
    calc
      C * Real.sqrt (Real.log (n : ℝ)) * (2 * Real.sqrt (n : ℝ)) * Real.sqrt (n : ℝ)
        = 2 * C * Real.sqrt (Real.log (n : ℝ)) *
            (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) := by ring
      _ = 2 * C * Real.sqrt (Real.log (n : ℝ)) * n := by rw [hsq]
  rw [h2]
  have h5 : (C * Real.sqrt (Real.log (n : ℝ)) / n) *
        ∑ d ∈ Finset.Icc 1 (n - a), 1 / Real.sqrt (d : ℝ) ≤
      2 * C * Real.sqrt (Real.log (n : ℝ)) / Real.sqrt (n : ℝ) := by
    rw [← h4]
    exact mul_le_mul_of_nonneg_left h3 (by positivity)
  linarith

/-- Equation (4.1). -/
theorem equation_4_1 {p n h : ℕ} (hp : p.Prime)
    (hn : 2 ≤ n) (C : ℝ) (hC : 0 < C) :
    prefixKernelSum n h (lemma43Kernel p n C) ≤
      (lemma43Base p n C) ^ h := by
  apply Section4.prefixKernelSum_le_pow
  · exact lemma43_kernel_nonneg hp C hC
  · intro a ha
    exact lemma43_kernel_row_bound hp hn C hC a ha
  · have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
    unfold lemma43Base
    positivity

/-- The fixed-j estimate (4.14 in the prose following (4.1)): after omitting the
j-th gap the left and reversed-right tuple sums are independent upper bounds. -/
theorem lemma43_fixed_j {p n k : ℕ} (hp : p.Prime)
    (hn : 2 ≤ n) (C : ℝ) (hC : 0 < C)
    (j : Fin (k + 1)) :
    omittedKernelSum n k (lemma43Kernel p n C) j ≤
      (lemma43Base p n C) ^ k := by
  have hw := lemma43_kernel_nonneg (n := n) hp C hC
  have hB : 0 ≤ lemma43Base p n C := by
    have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
    unfold lemma43Base
    positivity
  have h1 := Section4.omittedKernelSum_le_prefix_mul n k
    (lemma43Kernel p n C) hw j
  have h2 : prefixKernelSum n j.val (lemma43Kernel p n C) ≤
      (lemma43Base p n C) ^ j.val := equation_4_1 hp hn C hC
  have h3 : prefixKernelSum n (k - j.val) (lemma43Kernel p n C) ≤
      (lemma43Base p n C) ^ (k - j.val) := equation_4_1 hp hn C hC
  have h3' : 0 ≤ prefixKernelSum n (k - j.val) (lemma43Kernel p n C) :=
    Finset.sum_nonneg (fun m _ => Finset.prod_nonneg (fun i _ => hw _))
  calc
    omittedKernelSum n k (lemma43Kernel p n C) j
      ≤ prefixKernelSum n j.val (lemma43Kernel p n C) *
          prefixKernelSum n (k - j.val) (lemma43Kernel p n C) := h1
    _ ≤ (lemma43Base p n C) ^ j.val * (lemma43Base p n C) ^ (k - j.val) :=
        mul_le_mul h2 h3 h3' (pow_nonneg hB _)
    _ = (lemma43Base p n C) ^ k := by
        rw [← pow_add, Nat.add_sub_cancel' (Nat.le_of_lt_succ j.isLt)]

theorem lemma43LHS_eq_sum_omitted (p n k : ℕ) (C : ℝ) :
    lemma43LHS p n k C =
      ∑ j : Fin (k + 1),
        omittedKernelSum n k (lemma43Kernel p n C) j := by
  unfold lemma43LHS lemma43Summand chainUpperBound omittedKernelSum lemma43Kernel
  exact Finset.sum_comm

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
