module

public import GrahamRearrangement.Combinatorial.Lemma41

@[expose] public section

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Corollary 1.4

The three-regime deduction from Theorem 1.3 and Lemma 4.1.
-/

noncomputable section

def section3Constant : ℝ := 2 ^ 24

theorem log_card_ge_half {n : ℕ} (hn : 2 ≤ n) :
    (1 / 2 : ℝ) ≤ Real.log (n : ℝ) := by
  sorry

theorem sqrt_log_card_ge_half {n : ℕ} (hn : 2 ≤ n) :
    (1 / 2 : ℝ) ≤ Real.sqrt (Real.log (n : ℝ)) := by
  have hlog := log_card_ge_half hn
  have hs := Real.sq_sqrt (show 0 ≤ Real.log (n : ℝ) by
    exact le_trans (by norm_num) hlog)
  have hsnonneg := Real.sqrt_nonneg (Real.log (n : ℝ))
  nlinarith

/-- A deliberately generous coefficient that handles all ground sets below N
without disturbing the asymptotic constants in the main three cases. -/
def smallGroundConstant (N : ℕ) : ℝ :=
  4 * (N : ℝ) ^ 3

theorem small_ground_trivial_bound {p m N : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hS : 2 ≤ S.card)
    (hSN : S.card < N) (hm : 0 < m) (hmS : m ≤ S.card)
    (z : ZMod p) :
    sliceMass S m z ≤
      smallGroundConstant N * Real.sqrt (Real.log (S.card : ℝ)) /
        ((S.card : ℝ) * Real.sqrt (m : ℝ)) := by
  sorry

/-- Consequences of the large-ground-set threshold used in Corollary 1.4. -/
theorem cor14_threshold_bounds (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (n N : ℕ) (hN : N ≤ n)
    (hthreshold :
      (4000 * section3Constant / ε) * (Real.log (n : ℝ)) ^ 2 ≤ n)
    (hn : 2 ≤ n) :
    section3Constant * Real.log (n : ℝ) ≤ (n : ℝ) / 2 ∧
    1 ≤ ε * (1 / 1000 : ℝ) * n / Real.log (n : ℝ) := by
  sorry

/-- Small-m regime of Corollary 1.4. -/
theorem cor14_small_m {p m : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hS : 2 ≤ S.card)
    (hm : 0 < m)
    (hmSmall : (m : ℝ) ≤
      section3Constant * Real.log (S.card : ℝ))
    (hHalf : section3Constant * Real.log (S.card : ℝ) ≤
      (S.card : ℝ) / 2)
    (z : ZMod p) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    sliceMass S m z ≤
      2 * Real.sqrt section3Constant *
        Real.sqrt (Real.log (S.card : ℝ)) /
          ((S.card : ℝ) * Real.sqrt (m : ℝ)) := by
  sorry

/-- Middle regime: Theorem 1.3 already gives more than Corollary 1.4. -/
theorem cor14_middle_m {p m : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hS : 2 ≤ S.card)
    (hmLower :
      section3Constant * Real.log (S.card : ℝ) ≤ (m : ℝ))
    (hmUpper :
      (m : ℝ) ≤ (1 / 1000 : ℝ) * S.card /
        Real.log (S.card : ℝ))
    (z : ZMod p) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    sliceMass S m z ≤
      1 / (p : ℝ) +
        2 * section3Constant *
          Real.sqrt (Real.log (S.card : ℝ)) /
            ((S.card : ℝ) * Real.sqrt (m : ℝ)) := by
  sorry

/-- Bounds for m₂ in the large-m regime. -/
theorem cor14_m2_bounds (ε : ℝ) (hε0 : 0 < ε)
    (n m : ℕ) (hn : 2 ≤ n)
    (hthreshold :
      (4000 * section3Constant / ε) * (Real.log (n : ℝ)) ^ 2 ≤ n)
    (hlarge :
      ε * (1 / 1000 : ℝ) * n / Real.log (n : ℝ) < m) :
    let m₂ := Nat.floor
      (ε * (1 / 1000 : ℝ) * n / Real.log (n : ℝ))
    m₂ ≤ m ∧
    (ε / 2) * (1 / 1000 : ℝ) * n / Real.log (n : ℝ) ≤ m₂ ∧
    section3Constant * Real.log (n : ℝ) ≤ m₂ := by
  sorry

/-- Corollary 1.4. -/
theorem corollary14 : Corollary14Statement := by
  sorry

end

end GrahamRearrangement
