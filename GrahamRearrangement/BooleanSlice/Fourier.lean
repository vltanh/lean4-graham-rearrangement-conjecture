module

public import GrahamRearrangement.BooleanSlice.External

@[expose] public section

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Section 3: Fourier reduction

Paper equations (3.1)--(3.4).
-/

noncomputable section

/-- The blockwise character estimate used in equation (3.2), proved from
Fact 2.5 exactly as in the paper. -/
theorem block_character_decay {p : ℕ} (hp : p.Prime)
    (T : Finset (ZMod p)) (hT : T.Nonempty) (χ : ZMod p) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    ‖((∑ x ∈ T, ZMod.stdAddChar (χ * x)) / (T.card : ℂ))‖ ≤
      Real.exp (-
        (1 / (T.card : ℝ) ^ 2) *
          ∑ x ∈ T, ∑ x' ∈ T,
            zmodNorm (χ * x - χ * x') ^ 2) := by
  sorry

theorem zmod_eq_indicator_fourier {p : ℕ} (hp : p.Prime)
    (a : ZMod p) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    (((if a = 0 then 1 else 0 : ℝ) : ℂ)) =
      (1 / (p : ℂ)) *
        ∑ χ : ZMod p, ZMod.stdAddChar (χ * a) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  rw [External.zmod_character_orthogonality hp a]
  by_cases ha : a = 0
  · simp [ha, hp.ne_zero]
  · simp [ha]

theorem character_choiceSum_factorization {p m : ℕ}
    [NeZero p]
    (P : Fin m → Finset (ZMod p)) (χ : ZMod p) :
    (∑ X ∈ blockChoices P,
        ZMod.stdAddChar (χ * choiceSum X)) =
      ∏ i : Fin m,
        ∑ x ∈ P i, ZMod.stdAddChar (χ * x) := by
  sorry

theorem conditional_sum_mass_fourier_eq {p m : ℕ}
    (hp : p.Prime)
    (P : Fin m → Finset (ZMod p))
    (hne : ∀ i, (P i).Nonempty) (z : ZMod p) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    (conditionalSumMass P z : ℂ) =
      (1 / (p : ℂ)) *
        ∑ χ : ZMod p,
          ZMod.stdAddChar (-χ * z) *
            ∏ i : Fin m,
              ((∑ x ∈ P i, ZMod.stdAddChar (χ * x)) /
                ((P i).card : ℂ)) := by
  sorry

theorem conditional_sum_mass_fourier_bound {p m : ℕ}
    (hp : p.Prime)
    (P : Fin m → Finset (ZMod p))
    (hne : ∀ i, (P i).Nonempty) (z : ZMod p) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    conditionalSumMass P z ≤
      (1 / (p : ℝ)) *
        ∑ χ : ZMod p,
          ∏ i,
            ‖((∑ x ∈ P i, ZMod.stdAddChar (χ * x)) /
              ((P i).card : ℂ))‖ := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have heq := conditional_sum_mass_fourier_eq hp P hne z
  have hnonneg : 0 ≤ conditionalSumMass P z :=
    uniformMass_nonneg _ _
  have hnorm :
      conditionalSumMass P z ≤
        ‖((conditionalSumMass P z : ℝ) : ℂ)‖ := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  rw [heq] at hnorm
  calc
    conditionalSumMass P z
      ≤ ‖(1 / (p : ℂ)) *
          ∑ χ : ZMod p,
            ZMod.stdAddChar (-χ * z) *
              ∏ i : Fin m,
                ((∑ x ∈ P i, ZMod.stdAddChar (χ * x)) /
                  ((P i).card : ℂ))‖ := hnorm
    _ = (1 / (p : ℝ)) *
        ‖∑ χ : ZMod p,
            ZMod.stdAddChar (-χ * z) *
              ∏ i : Fin m,
                ((∑ x ∈ P i, ZMod.stdAddChar (χ * x)) /
                  ((P i).card : ℂ))‖ := by
          rw [norm_mul]
          simp [hp.pos.ne']
    _ ≤ (1 / (p : ℝ)) *
        ∑ χ : ZMod p,
          ‖ZMod.stdAddChar (-χ * z) *
              ∏ i : Fin m,
                ((∑ x ∈ P i, ZMod.stdAddChar (χ * x)) /
                  ((P i).card : ℂ))‖ := by
          gcongr
          exact norm_sum_le _ _
    _ = (1 / (p : ℝ)) *
        ∑ χ : ZMod p,
          ∏ i,
            ‖((∑ x ∈ P i, ZMod.stdAddChar (χ * x)) /
              ((P i).card : ℂ))‖ := by
          congr 1
          apply Finset.sum_congr rfl
          intro χ hχ
          rw [norm_mul, norm_prod]
          simp

/-- Equation (3.1), followed by the blockwise decay that gives (3.2). -/
theorem conditional_sum_mass_le_exp_psi {p m : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hm : 0 < m) (hmS : m ≤ S.card)
    {P : Fin m → Finset (ZMod p)} (hP : IsBalancedPartition S P)
    (z : ZMod p) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    conditionalSumMass P z ≤
      (1 / (p : ℝ)) * ∑ χ : ZMod p, Real.exp (-psi P χ) := by
  sorry

/-- Equation (3.3), obtained from the balanced block-size upper bound. -/
theorem psi_lower_bound {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hS : 2 ≤ S.card)
    (hm : 0 < m) (hm4 : m ≤ S.card / 4)
    {P : Fin m → Finset (ZMod p)} (hP : IsBalancedPartition S P)
    (χ : ZMod p) :
    ((m : ℝ) ^ 2 / (2 * (S.card : ℝ) ^ 2)) *
        ∑ i, ∑ x ∈ P i, ∑ x' ∈ P i,
          zmodNorm (χ * x - χ * x') ^ 2
      ≤ psi P χ := by
  sorry

theorem psi_zero {p m : ℕ} [NeZero p]
    (P : Fin m → Finset (ZMod p)) :
    psi P 0 = 0 := by
  sorry

/-- The crude bound `ψ(χ)≤m` used to terminate the dyadic partition. -/
theorem psi_le_m {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hm : 0 < m) (hmS : m ≤ S.card)
    {P : Fin m → Finset (ZMod p)} (hP : IsBalancedPartition S P)
    (χ : ZMod p) :
    psi P χ ≤ m := by
  sorry

theorem dyadic_exp_sum_bound
    {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → ℝ) (A0 : Finset α) (At : ℕ → Finset α) (m : ℕ)
    (hnonneg : ∀ a, 0 ≤ f a)
    (hcover : ∀ a, a ∈ A0 ∨ ∃ l < Nat.log2 m + 1, a ∈ At (2 ^ l))
    (hA0 : ∀ a ∈ A0, f a < 1)
    (hAt : ∀ l a, a ∈ At (2 ^ l) →
      (2 : ℝ) ^ l ≤ f a) :
    (∑ a : α, Real.exp (-f a)) ≤
      (A0.card : ℝ) +
        ∑ l ∈ Finset.range (Nat.log2 m + 1),
          (At (2 ^ l)).card * Real.exp (-(2 : ℝ) ^ l) := by
  sorry

/-- The dyadic decomposition bound before averaging over partitions. -/
theorem dyadic_conditional_bound {p m : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hS : 2 ≤ S.card)
    (hm : 0 < m) (hm4 : m ≤ S.card / 4)
    {P : Fin m → Finset (ZMod p)} (hP : IsBalancedPartition S P)
    (z : ZMod p) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    conditionalSumMass P z ≤
      (1 / (p : ℝ)) * (A0 P).card +
      (1 / (p : ℝ)) *
        ∑ l ∈ Finset.range (Nat.log2 m + 1),
          (At P (2 ^ l)).card * Real.exp (-(2 : ℝ) ^ l) := by
  sorry

/-- Equation (3.4): average the preceding inequality over the random partition. -/
theorem equation_3_4 {p m : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hS : 2 ≤ S.card)
    (hm : 0 < m) (hm4 : m ≤ S.card / 4)
    (z : ZMod p) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    sliceMass S m z ≤
      (1 / (p : ℝ)) *
        partitionExpectation (m := m) S (fun P => ((A0 P).card : ℝ)) +
      (1 / (p : ℝ)) *
        ∑ l ∈ Finset.range (Nat.log2 m + 1),
          partitionExpectation (m := m) S
            (fun P => ((At P (2 ^ l)).card : ℝ)) *
              Real.exp (-(2 : ℝ) ^ l) := by
  sorry

end

end GrahamRearrangement
