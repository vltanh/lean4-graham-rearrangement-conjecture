module

public import GrahamRearrangement.Rearrangement.IntervalLemmas

@[expose] public section

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Section 5: constants and parameter package
-/

noncomputable section

def section5D (α : ℝ) : ℕ :=
  Nat.ceil (3 / α)

theorem section5D_ge_seven {α : ℝ}
    (hα0 : 0 < α) (hαh : α < 1 / 2) :
    7 ≤ section5D α :=
  External.ceil_three_div_ge_seven hα0 hαh

theorem section5D_pos {α : ℝ}
    (hα0 : 0 < α) (hαh : α < 1 / 2) :
    0 < section5D α :=
  lt_of_lt_of_le (by norm_num) (section5D_ge_seven hα0 hαh)

theorem alpha_mul_section5D_ge_three {α : ℝ}
    (hα0 : 0 < α) :
    3 ≤ α * section5D α := by
  have hceil :
      3 / α ≤ (section5D α : ℝ) := by
    exact_mod_cast Nat.le_ceil (3 / α)
  have := mul_le_mul_of_nonneg_left hceil (le_of_lt hα0)
  field_simp at this
  nlinarith

structure Section5Parameters (α : ℝ) where
  D : ℕ
  D_eq : D = section5D α
  Cα : ℝ
  Cα_pos : 0 < Cα
  Cα_first :
    ((10 ^ 4 : ℝ) * (2 : ℝ) ^ (40 * D)) ^ (1 / α) ≤ Cα
  Cα_second :
    (D + 1 : ℝ) * (2 : ℝ) ^ D *
      (D : ℝ) ^ (14 * D ^ 2) ≤ Cα
  Cα_fiftyD : (50 * D : ℝ) ≤ Cα
  second_ge_100 :
    (100 : ℝ) * (5 * D : ℝ) ^ (2 * D) ≤
      (D + 1 : ℝ) * (2 : ℝ) ^ D *
        (D : ℝ) ^ (14 * D ^ 2)
  hundred_ge_40 :
    (40 * D : ℝ) ^ D ≤
      (100 : ℝ) * (5 * D : ℝ) ^ (2 * D)
  asymptotic :
    ∀ n : ℕ, Cα ≤ n →
      4 * max (chainConstant D) (chainConstant 1) *
          Real.sqrt (Real.log (n : ℝ)) /
            Real.sqrt (n : ℝ) ≤
        (n : ℝ) ^ (-α)

theorem exists_section5Parameters {α : ℝ}
    (hα0 : 0 < α) (hαh : α < 1 / 2) :
    ∃ P : Section5Parameters α, True := by
  sorry

theorem section5Parameters_D_pos {α : ℝ}
    (hα0 : 0 < α) (hαh : α < 1 / 2)
    (P : Section5Parameters α) :
    0 < P.D := by
  rw [P.D_eq]
  exact section5D_pos hα0 hαh

theorem section5Parameters_alphaD {α : ℝ}
    (hα0 : 0 < α) (P : Section5Parameters α) :
    3 ≤ α * P.D := by
  rw [P.D_eq]
  exact alpha_mul_section5D_ge_three hα0

def Section5Regime {α : ℝ} (P : Section5Parameters α)
    (p : ℕ) (S : Finset (ZMod p)) : Prop :=
  0 ∉ S ∧
  P.Cα ≤ (S.card : ℝ) ∧
  (S.card : ℝ) ≤ (p : ℝ) ^ (1 - α)

theorem section5_card_ge_fiftyD {α : ℝ} {P : Section5Parameters α}
    {p : ℕ} {S : Finset (ZMod p)}
    (hreg : Section5Regime P p S) :
    50 * P.D ≤ S.card := by
  exact_mod_cast le_trans P.Cα_fiftyD hreg.2.1

theorem section5_card_ge_two {α : ℝ} {P : Section5Parameters α}
    (hα0 : 0 < α) (hαh : α < 1 / 2)
    {p : ℕ} {S : Finset (ZMod p)}
    (hreg : Section5Regime P p S) :
    2 ≤ S.card := by
  have hD : 7 ≤ P.D := by
    rw [P.D_eq]
    exact section5D_ge_seven hα0 hαh
  have h50 := section5_card_ge_fiftyD hreg
  omega

theorem section5_card_over_p {α : ℝ} {P : Section5Parameters α}
    (hα0 : 0 < α) (hαh : α < 1 / 2)
    {p : ℕ} (hp : p.Prime) {S : Finset (ZMod p)}
    (hreg : Section5Regime P p S) :
    (S.card : ℝ) / p ≤ (S.card : ℝ) ^ (-α) := by
  apply External.card_div_prime_le_neg_rpow hα0 (lt_trans hαh (by norm_num))
  · exact le_trans (by norm_num) (section5_card_ge_two hα0 hαh hreg)
  · exact hp.one_le
  · exact hreg.2.2

theorem section5_chainConstant_bound {α : ℝ}
    {P : Section5Parameters α}
    {p : ℕ} {S : Finset (ZMod p)}
    (hreg : Section5Regime P p S) (k : ℕ)
    (hk : k = 1 ∨ k = P.D) :
    4 * chainConstant k * Real.sqrt (Real.log (S.card : ℝ)) /
        Real.sqrt (S.card : ℝ) ≤
      (S.card : ℝ) ^ (-α) := by
  sorry

/-- The first lower bound on Cα in the power form actually used by union bounds. -/
theorem section5_Calpha_power {α : ℝ}
    (hα0 : 0 < α) (P : Section5Parameters α) :
    (10 ^ 4 : ℝ) * (2 : ℝ) ^ (40 * P.D) ≤ P.Cα ^ α := by
  have hbase :=
    External.section5_rpow_threshold (D := P.D) hα0
  have hmono :=
    Real.rpow_le_rpow (by positivity) P.Cα_first (le_of_lt hα0)
  exact le_trans hbase hmono

end

end GrahamRearrangement
