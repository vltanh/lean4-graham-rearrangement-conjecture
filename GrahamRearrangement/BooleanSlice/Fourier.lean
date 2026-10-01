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
  letI : NeZero p := ⟨hp.ne_zero⟩
  set δ : ℝ :=
    (1 / (T.card : ℝ) ^ 2) *
      ∑ x ∈ T, ∑ x' ∈ T,
        zmodNorm (χ * x - χ * x') ^ 2 with hδdef
  have hsq :=
    External.zmod_character_average_norm_sq T hT χ
  -- Fact 2.5 applied to every pair `(x,x')`.
  have hdouble :
      (∑ x ∈ T, ∑ x' ∈ T,
          (ZMod.stdAddChar (χ * x - χ * x')).re)
        ≤ (T.card : ℝ) ^ 2 -
          2 * ∑ x ∈ T, ∑ x' ∈ T,
            zmodNorm (χ * x - χ * x') ^ 2 := by
    calc
      _ ≤ ∑ x ∈ T, ∑ x' ∈ T,
          (1 - 2 * zmodNorm (χ * x - χ * x') ^ 2) := by
            gcongr with x hx x' hx'
            have h := fact2_5 hp (χ * x - χ * x')
            rw [ep_eq_stdAddChar] at h
            exact h
      _ = (T.card : ℝ) ^ 2 -
          2 * ∑ x ∈ T, ∑ x' ∈ T,
            zmodNorm (χ * x - χ * x') ^ 2 := by
            simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
              mul_one, ← Finset.mul_sum]
            ring
  have hnormsq :
      ‖((∑ x ∈ T, ZMod.stdAddChar (χ * x)) / (T.card : ℂ))‖ ^ 2
        ≤ 1 - 2 * δ := by
    rw [hsq, hδdef]
    have hcoef : 0 ≤ 1 / (T.card : ℝ) ^ 2 := by positivity
    have hcard : 0 < (T.card : ℝ) := by
      exact_mod_cast hT.card_pos
    calc
      _ ≤ (1 / (T.card : ℝ) ^ 2) *
          ((T.card : ℝ) ^ 2 -
            2 * ∑ x ∈ T, ∑ x' ∈ T,
              zmodNorm (χ * x - χ * x') ^ 2) := by
            exact mul_le_mul_of_nonneg_left hdouble hcoef
      _ = _ := by field_simp
  -- `(1 - 2δ)^{1/2} ≤ exp(-δ)`.
  have hexp :
      1 - 2 * δ ≤ Real.exp (-2 * δ) := by
    have := Real.add_one_le_exp (-2 * δ)
    linarith
  have hsquare :
      (Real.exp (-δ)) ^ 2 = Real.exp (-2 * δ) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsq' :
      ‖((∑ x ∈ T, ZMod.stdAddChar (χ * x)) / (T.card : ℂ))‖ ^ 2
        ≤ (Real.exp (-δ)) ^ 2 := by
    rw [hsquare]
    exact le_trans hnormsq hexp
  have hnorm0 :
      0 ≤ ‖((∑ x ∈ T, ZMod.stdAddChar (χ * x)) / (T.card : ℂ))‖ :=
    norm_nonneg _
  have hexp0 : 0 ≤ Real.exp (-δ) := Real.exp_nonneg _
  rw [show -(1 / (T.card : ℝ) ^ 2) *
      ∑ x ∈ T, ∑ x' ∈ T, zmodNorm (χ * x - χ * x') ^ 2 = -δ by
    rw [hδdef]; ring]
  exact (pow_le_pow_iff_left₀ hnorm0 hexp0 two_ne_zero).1 hsq'

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

/-- An additive character turns finite sums into finite products. -/
theorem fourier_stdAddChar_sum_eq_prod {p : ℕ} [NeZero p] {ι : Type*}
    (s : Finset ι) (f : ι → ZMod p) :
    ZMod.stdAddChar (∑ i ∈ s, f i) = ∏ i ∈ s, ZMod.stdAddChar (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

theorem character_choiceSum_factorization {p m : ℕ}
    [NeZero p]
    (P : Fin m → Finset (ZMod p)) (χ : ZMod p) :
    (∑ X ∈ blockChoices P,
        ZMod.stdAddChar (χ * choiceSum X)) =
      ∏ i : Fin m,
        ∑ x ∈ P i, ZMod.stdAddChar (χ * x) := by
  classical
  rw [Finset.prod_univ_sum]
  unfold blockChoices choiceSum
  apply Finset.sum_congr rfl
  intro X _
  rw [Finset.mul_sum, fourier_stdAddChar_sum_eq_prod]

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
  letI : NeZero p := ⟨hp.ne_zero⟩
  classical
  have hcardP :
      (blockChoices P).card = ∏ i : Fin m, (P i).card :=
    blockChoices_card P
  have hcardne : ∀ i, ((P i).card : ℂ) ≠ 0 := by
    intro i
    exact_mod_cast (hne i).card_pos.ne'
  unfold conditionalSumMass uniformMass
  have hindicator :
      ((((blockChoices P).filter fun X => choiceSum X = z).card : ℝ) : ℂ) =
        ∑ X ∈ blockChoices P,
          (((if choiceSum X - z = 0 then 1 else 0 : ℝ) : ℂ)) := by
    rw [Finset.card_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro X _
    simp [sub_eq_zero]
  have hfactor :
      ∀ χ : ZMod p,
        (∑ X ∈ blockChoices P,
            ZMod.stdAddChar (χ * (choiceSum X - z))) =
          ZMod.stdAddChar (-χ * z) *
            ∏ i : Fin m,
              ∑ x ∈ P i, ZMod.stdAddChar (χ * x) := by
    intro χ
    rw [← character_choiceSum_factorization P χ, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro X _
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  rw [Complex.ofReal_div, hindicator]
  simp_rw [zmod_eq_indicator_fourier hp]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [hfactor]
  rw [hcardP]
  push_cast
  simp_rw [Finset.prod_div_distrib]
  rw [mul_div_assoc, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro χ _
  ring

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
    simp [Real.norm_eq_abs, abs_of_nonneg hnonneg]
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
          simp
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

/-- Every block of a balanced partition is nonempty when `0 < m ≤ |S|`. -/
theorem balancedPartition_block_nonempty {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hm : 0 < m) (hmS : m ≤ S.card)
    {P : Fin m → Finset (ZMod p)} (hP : IsBalancedPartition S P)
    (i : Fin m) : (P i).Nonempty := by
  have hb := Section3External.balanced_block_size_bounds S hm hmS hP i
  have hdiv : 0 < S.card / m := Nat.div_pos hmS hm
  exact Finset.card_pos.mp (lt_of_lt_of_le hdiv hb.1)

/-- Equation (3.1), followed by the blockwise decay that gives (3.2). -/
theorem conditional_sum_mass_le_exp_psi {p m : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hm : 0 < m) (hmS : m ≤ S.card)
    {P : Fin m → Finset (ZMod p)} (hP : IsBalancedPartition S P)
    (z : ZMod p) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    conditionalSumMass P z ≤
      (1 / (p : ℝ)) * ∑ χ : ZMod p, Real.exp (-psi P χ) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hne : ∀ i, (P i).Nonempty :=
    balancedPartition_block_nonempty S hm hmS hP
  have h31 := conditional_sum_mass_fourier_bound hp P hne z
  refine le_trans h31 ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro χ _
  calc
    ∏ i,
        ‖((∑ x ∈ P i, ZMod.stdAddChar (χ * x)) /
          ((P i).card : ℂ))‖
        ≤ ∏ i,
            Real.exp (-
              (1 / ((P i).card : ℝ) ^ 2) *
                ∑ x ∈ P i, ∑ x' ∈ P i,
                  zmodNorm (χ * x - χ * x') ^ 2) := by
          apply Finset.prod_le_prod₀
          · intro i _
            positivity
          · intro i _
            exact block_character_decay hp (P i) (hne i) χ
    _ = Real.exp (-psi P χ) := by
          rw [← Real.exp_sum]
          congr 1
          simp only [psi, neg_mul, Finset.sum_neg_distrib]

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
  unfold psi
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hmS : m ≤ S.card := le_trans hm4 (Nat.div_le_self _ _)
  have hcard :=
    Section3External.balanced_block_sqrt_two_bound S hS hm4 hP i
  have hcardpos : 0 < ((P i).card : ℝ) := by
    exact_mod_cast (balancedPartition_block_nonempty S hm hmS hP i).card_pos
  have hSpos : 0 < (S.card : ℝ) := by
    have : (2 : ℝ) ≤ S.card := by exact_mod_cast hS
    linarith
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  -- `|S_i| ≤ √2 |S| / m` gives `m²/(2|S|²) ≤ 1/|S_i|²`.
  have hcoef :
      (m : ℝ) ^ 2 / (2 * (S.card : ℝ) ^ 2) ≤
        1 / ((P i).card : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    have h1 : ((P i).card : ℝ) * m ≤ Real.sqrt 2 * S.card := by
      rw [le_div_iff₀ hmpos] at hcard
      exact hcard
    have h2 : (((P i).card : ℝ) * m) ^ 2 ≤ (Real.sqrt 2 * S.card) ^ 2 := by
      gcongr
    nlinarith [h2]
  have hsum :
      0 ≤ ∑ x ∈ P i, ∑ x' ∈ P i,
        zmodNorm (χ * x - χ * x') ^ 2 := by positivity
  exact mul_le_mul_of_nonneg_right hcoef hsum

theorem psi_zero {p m : ℕ} [NeZero p]
    (P : Fin m → Finset (ZMod p)) :
    psi P 0 = 0 := by
  simp [psi, zmodNorm, distToInt]

theorem psi_nonneg {p m : ℕ} [NeZero p]
    (P : Fin m → Finset (ZMod p)) (χ : ZMod p) :
    0 ≤ psi P χ := by
  unfold psi
  positivity

/-- The crude bound `ψ(χ)≤m` used to terminate the dyadic partition. -/
theorem psi_le_m {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hm : 0 < m) (hmS : m ≤ S.card)
    {P : Fin m → Finset (ZMod p)} (hP : IsBalancedPartition S P)
    (χ : ZMod p) :
    psi P χ ≤ m := by
  unfold psi
  calc
    ∑ i,
        (1 / ((P i).card : ℝ) ^ 2) *
          ∑ x ∈ P i, ∑ x' ∈ P i,
            zmodNorm (χ * x - χ * x') ^ 2
      ≤ ∑ _i : Fin m, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          have hpair :
              ∑ x ∈ P i, ∑ x' ∈ P i,
                  zmodNorm (χ * x - χ * x') ^ 2
                ≤ ((P i).card : ℝ) ^ 2 := by
            calc
              _ ≤ ∑ x ∈ P i, ∑ _x' ∈ P i, (1 : ℝ) := by
                gcongr with x hx x' hx'
                have hn := zmodNorm_nonneg (χ * x - χ * x')
                have hh := zmodNorm_le_half (χ * x - χ * x')
                nlinarith
              _ = ((P i).card : ℝ) ^ 2 := by simp [pow_two]
          have hcardpos : 0 < ((P i).card : ℝ) := by
            exact_mod_cast (balancedPartition_block_nonempty S hm hmS hP i).card_pos
          rw [one_div_mul_eq_div, div_le_one (by positivity)]
          exact hpair
    _ = m := by simp

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
  classical
  have hpoint : ∀ a : α,
      Real.exp (-f a) ≤
        (if a ∈ A0 then 1 else 0) +
          ∑ l ∈ Finset.range (Nat.log2 m + 1),
            if a ∈ At (2 ^ l) then
              Real.exp (-(2 : ℝ) ^ l) else 0 := by
    intro a
    have hexp1 : Real.exp (-f a) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      linarith [hnonneg a]
    have hsum0 : 0 ≤ ∑ l ∈ Finset.range (Nat.log2 m + 1),
            if a ∈ At (2 ^ l) then
              Real.exp (-(2 : ℝ) ^ l) else 0 := by
      apply Finset.sum_nonneg
      intro l _
      split_ifs <;> positivity
    by_cases ha0 : a ∈ A0
    · simp only [ha0, ite_true]
      linarith
    · rcases hcover a with ha0' | ⟨l, hl, hAtmem⟩
      · exact absurd ha0' ha0
      · have hexp :
            Real.exp (-f a) ≤ Real.exp (-(2 : ℝ) ^ l) :=
          Real.exp_le_exp.mpr (by
            have := hAt l a hAtmem
            linarith)
        have hsingle :
            Real.exp (-(2 : ℝ) ^ l) ≤
              ∑ r ∈ Finset.range (Nat.log2 m + 1),
                if a ∈ At (2 ^ r) then
                  Real.exp (-(2 : ℝ) ^ r) else 0 := by
          have := Finset.single_le_sum (f := fun r =>
              if a ∈ At (2 ^ r) then Real.exp (-(2 : ℝ) ^ r) else 0)
            (fun r _ => by split_ifs <;> positivity)
            (Finset.mem_range.mpr hl)
          simpa [hAtmem] using this
        simp only [ha0, ite_false, zero_add]
        exact le_trans hexp hsingle
  calc
    (∑ a : α, Real.exp (-f a))
      ≤ ∑ a : α,
          ((if a ∈ A0 then 1 else 0) +
            ∑ l ∈ Finset.range (Nat.log2 m + 1),
              if a ∈ At (2 ^ l) then
                Real.exp (-(2 : ℝ) ^ l) else 0) := by
          gcongr with a
          exact hpoint a
    _ = (A0.card : ℝ) +
        ∑ l ∈ Finset.range (Nat.log2 m + 1),
          (At (2 ^ l)).card * Real.exp (-(2 : ℝ) ^ l) := by
          rw [Finset.sum_add_distrib, Finset.sum_comm]
          congr 1
          · rw [Finset.sum_boole]
            simp
          · apply Finset.sum_congr rfl
            intro l _
            rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
              nsmul_eq_mul]
            congr 2
            congr 1
            ext a
            simp

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
  letI : NeZero p := ⟨hp.ne_zero⟩
  classical
  have hmS : m ≤ S.card := le_trans hm4 (Nat.div_le_self _ _)
  have hbase := conditional_sum_mass_le_exp_psi hp S hm hmS hP z
  have hψ := psi_le_m S hm hmS hP
  -- Every character lies in `A₀` or in one of the dyadic shells `A_{2^l}`.
  have hcover : ∀ χ : ZMod p,
      χ ∈ A0 P ∨
        ∃ l < Nat.log2 m + 1, χ ∈ At P (2 ^ l) := by
    intro χ
    by_cases hχ : psi P χ < 1
    · exact Or.inl (by simp [A0, hχ])
    · right
      have hχ1 : 1 ≤ psi P χ := le_of_not_gt hχ
      obtain ⟨l, hl, hlo, hhi⟩ :=
        External.exists_dyadic_interval hχ1 (hψ χ)
      refine ⟨l, hl, ?_⟩
      simp only [At, Finset.mem_filter, Finset.mem_univ, true_and]
      push_cast
      exact ⟨hlo, hhi⟩
  have hA0 : ∀ a ∈ A0 P, psi P a < 1 := by
    intro a ha
    simpa [A0] using ha
  have hAt : ∀ l a, a ∈ At P (2 ^ l) →
      (2 : ℝ) ^ l ≤ psi P a := by
    intro l a ha
    simp only [At, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    exact_mod_cast ha.1
  have hdy := dyadic_exp_sum_bound
    (psi P) (A0 P) (At P) m (psi_nonneg P) hcover hA0 hAt
  calc
    conditionalSumMass P z
      ≤ (1 / (p : ℝ)) * ∑ χ : ZMod p, Real.exp (-psi P χ) := hbase
    _ ≤ (1 / (p : ℝ)) * ((A0 P).card +
          ∑ l ∈ Finset.range (Nat.log2 m + 1),
            (At P (2 ^ l)).card * Real.exp (-(2 : ℝ) ^ l)) :=
        mul_le_mul_of_nonneg_left hdy (by positivity)
    _ = _ := by ring

/-- Linearity of a finite uniform expectation over a finite sum. -/
theorem fourier_uniformExpectation_finset_sum {Ω ι : Type*} [DecidableEq Ω]
    (space : Finset Ω) (s : Finset ι) (f : ι → Ω → ℝ) :
    uniformExpectation space (fun ω => ∑ i ∈ s, f i ω) =
      ∑ i ∈ s, uniformExpectation space (f i) := by
  unfold uniformExpectation
  rw [Finset.sum_comm, Finset.sum_div]

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
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hmS : m ≤ S.card := le_trans hm4 (Nat.div_le_self _ _)
  rw [Section3External.sliceMass_eq_partition_average hp S hm hmS z]
  have hmono :
      partitionExpectation (m := m) S (fun P => conditionalSumMass P z) ≤
        partitionExpectation (m := m) S (fun P =>
          (1 / (p : ℝ)) * (A0 P).card +
          (1 / (p : ℝ)) *
            ∑ l ∈ Finset.range (Nat.log2 m + 1),
              (At P (2 ^ l)).card * Real.exp (-(2 : ℝ) ^ l)) := by
    unfold partitionExpectation
    apply uniformExpectation_mono
    intro P hP
    have hP' : IsBalancedPartition S P := by
      simpa [balancedPartitions] using hP
    exact dyadic_conditional_bound hp S hS hm hm4 hP' z
  refine le_trans hmono (le_of_eq ?_)
  unfold partitionExpectation
  rw [uniformExpectation_add, uniformExpectation_smul, uniformExpectation_smul,
    fourier_uniformExpectation_finset_sum]
  congr 2
  apply Finset.sum_congr rfl
  intro l _
  rw [show (fun P : Fin m → Finset (ZMod p) =>
      ((At P (2 ^ l)).card : ℝ) * Real.exp (-(2 : ℝ) ^ l)) =
      (fun P => Real.exp (-(2 : ℝ) ^ l) * ((At P (2 ^ l)).card : ℝ)) by
    funext P; ring]
  rw [uniformExpectation_smul, mul_comm]

end

end GrahamRearrangement
