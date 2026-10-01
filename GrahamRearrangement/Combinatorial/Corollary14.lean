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
  have h2 : Real.log 2 ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have := Real.log_two_gt_d9
  linarith

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
  have h1 := sliceMass_le_one (m := m) S z
  have hlog := sqrt_log_card_ge_half hS
  have hn2 : (2 : ℝ) ≤ S.card := by exact_mod_cast hS
  have hnN : (S.card : ℝ) ≤ N := by exact_mod_cast hSN.le
  have hmpos : (0 : ℝ) < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hm)
  have hsqrtm : Real.sqrt (m : ℝ) ≤ S.card := by
    rw [Real.sqrt_le_left (by positivity)]
    have : (m : ℝ) ≤ S.card := by exact_mod_cast hmS
    nlinarith
  rw [le_div_iff₀ (by positivity)]
  unfold smallGroundConstant
  have hprod : (S.card : ℝ) * Real.sqrt (m : ℝ) ≤ (N : ℝ) * N := by
    apply mul_le_mul hnN (hsqrtm.trans hnN) hmpos.le (by positivity)
  have hN1 : (1 : ℝ) ≤ N := by linarith
  calc
    sliceMass S m z * ((S.card : ℝ) * Real.sqrt (m : ℝ))
      ≤ 1 * ((S.card : ℝ) * Real.sqrt (m : ℝ)) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ ≤ (N : ℝ) * N := by rw [one_mul]; exact hprod
    _ ≤ 4 * (N : ℝ) ^ 3 * (1 / 2) := by nlinarith
    _ ≤ 4 * (N : ℝ) ^ 3 * Real.sqrt (Real.log (S.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)

/-- Consequences of the large-ground-set threshold used in Corollary 1.4. -/
theorem cor14_threshold_bounds (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (n : ℕ)
    (hthreshold :
      (4000 * section3Constant / ε) * (Real.log (n : ℝ)) ^ 2 ≤ n)
    (hn : 2 ≤ n) :
    section3Constant * Real.log (n : ℝ) ≤ (n : ℝ) / 2 ∧
    1 ≤ ε * (1 / 1000 : ℝ) * n / Real.log (n : ℝ) := by
  have hlog := log_card_ge_half hn
  have hlogpos : 0 < Real.log (n : ℝ) := by linarith
  have hC : section3Constant = 2 ^ 24 := rfl
  have hεn : 4000 * section3Constant * (Real.log (n : ℝ)) ^ 2 ≤ ε * n := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hε0] at hthreshold
    linarith
  have hεn' : ε * n ≤ n := by
    have : (0 : ℝ) ≤ n := by positivity
    nlinarith
  constructor
  · rw [hC] at hεn ⊢
    nlinarith
  · rw [le_div_iff₀ hlogpos]
    rw [hC] at hεn
    nlinarith

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
  let _ : NeZero p := ⟨hp.ne_zero⟩
  show sliceMass S m z ≤ _
  have hn2 : (2 : ℝ) ≤ S.card := by exact_mod_cast hS
  have hmn : (m : ℝ) ≤ (S.card : ℝ) / 2 := hmSmall.trans hHalf
  have hmS : m ≤ S.card := by
    have : (m : ℝ) ≤ S.card := by linarith
    exact_mod_cast this
  have h41 := lemma4_1 hp S hm hmS z
  have hcast : ((S.card - m + 1 : ℕ) : ℝ) = (S.card : ℝ) - m + 1 := by
    push_cast [Nat.cast_sub hmS]
    ring
  have hstep1 : 1 / ((S.card - m + 1 : ℕ) : ℝ) ≤ 2 / (S.card : ℝ) := by
    rw [hcast, div_le_div_iff₀ (by linarith) (by positivity)]
    linarith
  have hC : (0 : ℝ) ≤ section3Constant := by unfold section3Constant; positivity
  have hmpos : (0 : ℝ) < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hm)
  have hsqrt : Real.sqrt (m : ℝ) ≤
      Real.sqrt section3Constant * Real.sqrt (Real.log (S.card : ℝ)) := by
    rw [← Real.sqrt_mul hC]
    exact Real.sqrt_le_sqrt hmSmall
  have hstep2 : 2 / (S.card : ℝ) ≤
      2 * Real.sqrt section3Constant * Real.sqrt (Real.log (S.card : ℝ)) /
        ((S.card : ℝ) * Real.sqrt (m : ℝ)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hn0 : (0 : ℝ) ≤ S.card := by positivity
    nlinarith
  exact h41.trans (hstep1.trans hstep2)

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
  have h13 := theorem13_explicit p hp S hS m hmLower hmUpper z
  refine h13.trans ?_
  have hlog := sqrt_log_card_ge_half hS
  have hC : section3Constant = 2 ^ 24 := rfl
  rw [hC]
  gcongr
  nlinarith

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
  intro m₂
  have hlog := log_card_ge_half hn
  have hlogpos : 0 < Real.log (n : ℝ) := by linarith
  have hC : section3Constant = 2 ^ 24 := rfl
  have hεn : 4000 * section3Constant * (Real.log (n : ℝ)) ^ 2 ≤ ε * n := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hε0] at hthreshold
    linarith
  set x := ε * (1 / 1000 : ℝ) * n / Real.log (n : ℝ) with hx
  have hxpos : 0 ≤ x := by positivity
  have hx4 : 4 * section3Constant * Real.log (n : ℝ) ≤ x := by
    rw [hx, le_div_iff₀ hlogpos]
    nlinarith
  have hx1 : 1 ≤ x := by
    rw [hC] at hx4
    nlinarith
  have hfloor_le : (m₂ : ℝ) ≤ x := Nat.floor_le hxpos
  have hfloor_gt : x < m₂ + 1 := Nat.lt_floor_add_one x
  have hm1 : (1 : ℝ) ≤ m₂ := by
    have : 1 ≤ m₂ := Nat.le_floor (by exact_mod_cast hx1)
    exact_mod_cast this
  have hhalf : (ε / 2) * (1 / 1000 : ℝ) * n / Real.log (n : ℝ) = x / 2 := by
    rw [hx]
    ring
  refine ⟨?_, ?_, ?_⟩
  · have : (m₂ : ℝ) < m := lt_of_le_of_lt hfloor_le hlarge
    exact_mod_cast this.le
  · rw [hhalf]
    linarith
  · have hC0 : 0 ≤ section3Constant * Real.log (n : ℝ) := by
      rw [hC]
      positivity
    linarith

/-- The large-ground-set threshold of Corollary 1.4 holds for all large `n`. -/
theorem cor14_eventually_threshold (ε : ℝ) (hε0 : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (4000 * section3Constant / ε) * (Real.log (n : ℝ)) ^ 2 ≤ n := by
  have hK : 0 < 4000 * section3Constant / ε := by
    unfold section3Constant
    positivity
  have h := (Real.isLittleO_pow_log_id_atTop (n := 2)).bound (inv_pos.mpr hK)
  have h' := tendsto_natCast_atTop_atTop.eventually h
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h'
  refine ⟨N, fun n hn => ?_⟩
  have hb := hN n hn
  simp only [Real.norm_eq_abs, id] at hb
  rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (Nat.cast_nonneg n)] at hb
  calc
    (4000 * section3Constant / ε) * (Real.log (n : ℝ)) ^ 2
      ≤ (4000 * section3Constant / ε) * ((4000 * section3Constant / ε)⁻¹ * n) :=
        mul_le_mul_of_nonneg_left hb hK.le
    _ = n := by
        have hC0 : section3Constant ≠ 0 := by
          unfold section3Constant
          positivity
        field_simp

/-- Large-m regime of Corollary 1.4: split off a uniformly random subset of size
m₂ and apply Theorem 1.3 conditionally on the first m₁ = m - m₂ elements. -/
theorem cor14_large_m {p m : ℕ} (hp : p.Prime) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (S : Finset (ZMod p)) (hS : 2 ≤ S.card)
    (hmε : (m : ℝ) ≤ (1 - ε) * S.card)
    (hthreshold :
      (4000 * section3Constant / ε) * (Real.log (S.card : ℝ)) ^ 2 ≤ S.card)
    (hlarge : (1 / 1000 : ℝ) * S.card / Real.log (S.card : ℝ) < m)
    (z : ZMod p) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    sliceMass S m z ≤
      1 / (p : ℝ) +
        (50 * section3Constant / ε ^ 2) * Real.sqrt (Real.log (S.card : ℝ)) /
          ((S.card : ℝ) * Real.sqrt (m : ℝ)) := by
  let _ : NeZero p := ⟨hp.ne_zero⟩
  show sliceMass S m z ≤ _
  have hn2 : (2 : ℝ) ≤ S.card := by exact_mod_cast hS
  have hlog := log_card_ge_half hS
  have hlogpos : 0 < Real.log (S.card : ℝ) := by linarith
  have hC : section3Constant = 2 ^ 24 := rfl
  have hεn : 4000 * section3Constant * (Real.log (S.card : ℝ)) ^ 2 ≤ ε * S.card := by
    have h := hthreshold
    rw [div_mul_eq_mul_div, div_le_iff₀ hε0] at h
    linarith
  have hlarge' : ε * (1 / 1000 : ℝ) * S.card / Real.log (S.card : ℝ) < m := by
    refine lt_of_le_of_lt ?_ hlarge
    rw [div_le_div_iff_of_pos_right hlogpos]
    have : (0 : ℝ) ≤ (1 / 1000 : ℝ) * S.card := by positivity
    nlinarith
  obtain ⟨hm₂m, hm₂lower, hm₂C⟩ :=
    cor14_m2_bounds ε hε0 S.card m hS hthreshold hlarge'
  set m₂ := ⌊ε * (1 / 1000 : ℝ) * S.card / Real.log (S.card : ℝ)⌋₊ with hm₂_def
  have hm₂upper : (m₂ : ℝ) ≤ ε * (1 / 1000 : ℝ) * S.card / Real.log (S.card : ℝ) :=
    Nat.floor_le (by positivity)
  have hmS : m ≤ S.card := by
    have : (m : ℝ) ≤ S.card := by nlinarith
    exact_mod_cast this
  have hsplit : sliceMass S m z =
      uniformExpectation (S.powersetCard (m - m₂))
        (fun R₁ => uniformMass ((S \ R₁).powersetCard m₂)
          (fun R₂ => subsetSum (R₁ ∪ R₂) = z)) := by
    have hm : sliceMass S m z = sliceMass S ((m - m₂) + m₂) z := by
      rw [Nat.sub_add_cancel hm₂m]
    rw [hm]
    exact Section4.uniformSubset_split S (m - m₂) m₂ (by omega) _
  rw [hsplit]
  apply uniformExpectation_le_const _ (powersetCard_nonempty S (by omega))
  intro R₁ hR₁
  rw [Finset.mem_powersetCard] at hR₁
  have hTcard : (S \ R₁).card = S.card - (m - m₂) := by
    rw [Finset.card_sdiff_of_subset hR₁.1, hR₁.2]
  have hTcardR : ((S \ R₁).card : ℝ) = (S.card : ℝ) - ((m - m₂ : ℕ) : ℝ) := by
    rw [hTcard, Nat.cast_sub (by omega)]
  have hinner : uniformMass ((S \ R₁).powersetCard m₂)
        (fun R₂ => subsetSum (R₁ ∪ R₂) = z) =
      sliceMass (S \ R₁) m₂ (z - subsetSum R₁) := by
    unfold sliceMass uniformMass
    congr 2
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro R₂ hR₂
    rw [Finset.mem_powersetCard] at hR₂
    have hdisj : Disjoint R₁ R₂ := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      exact (Finset.mem_sdiff.mp (hR₂.1 hx2)).2 hx1
    unfold subsetSum
    rw [Finset.sum_union hdisj, eq_sub_iff_add_eq, add_comm]
  rw [hinner]
  have hm₁le : ((m - m₂ : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.sub_le m m₂
  have hTlower : ε * S.card ≤ ((S \ R₁).card : ℝ) := by
    rw [hTcardR]
    linarith
  have hεn2 : (2 : ℝ) ≤ ε * S.card := by
    rw [hC] at hεn
    nlinarith
  have hT2 : 2 ≤ (S \ R₁).card := by
    have : (2 : ℝ) ≤ (S \ R₁).card := le_trans hεn2 hTlower
    exact_mod_cast this
  have hT2R : (2 : ℝ) ≤ (S \ R₁).card := by exact_mod_cast hT2
  have hTle : ((S \ R₁).card : ℝ) ≤ S.card := by
    exact_mod_cast Finset.card_le_card Finset.sdiff_subset
  have hlogT : Real.log ((S \ R₁).card : ℝ) ≤ Real.log (S.card : ℝ) :=
    Real.log_le_log (by linarith) hTle
  have hlogTpos : 0 < Real.log ((S \ R₁).card : ℝ) := by
    have := log_card_ge_half hT2
    linarith
  have hlow : (2 ^ 24 : ℝ) * Real.log ((S \ R₁).card : ℝ) ≤ m₂ := by
    rw [hC] at hm₂C
    nlinarith
  have hup : (m₂ : ℝ) ≤ (1 / 1000 : ℝ) * (S \ R₁).card /
      Real.log ((S \ R₁).card : ℝ) := by
    refine hm₂upper.trans ?_
    calc
      ε * (1 / 1000 : ℝ) * S.card / Real.log (S.card : ℝ)
        ≤ (1 / 1000 : ℝ) * (S \ R₁).card / Real.log (S.card : ℝ) := by
          rw [div_le_div_iff_of_pos_right hlogpos]
          linarith
      _ ≤ (1 / 1000 : ℝ) * (S \ R₁).card / Real.log ((S \ R₁).card : ℝ) := by
          apply div_le_div_of_nonneg_left (by positivity) hlogTpos hlogT
  have h13 := theorem13_explicit p hp (S \ R₁) hT2 m₂ hlow hup (z - subsetSum R₁)
  refine h13.trans (add_le_add le_rfl ?_)
  -- the explicit comparison of error terms
  have hm₂pos : (0 : ℝ) < m₂ := by
    have : 0 < section3Constant * Real.log (S.card : ℝ) := by
      rw [hC]
      positivity
    linarith
  have hmpos : (0 : ℝ) < m := lt_of_lt_of_le hm₂pos (by exact_mod_cast hm₂m)
  have hmSR : (m : ℝ) ≤ S.card := by exact_mod_cast hmS
  have e1 : Real.sqrt (m : ℝ) ≤ Real.sqrt (S.card : ℝ) := Real.sqrt_le_sqrt hmSR
  have e2 : ε * Real.sqrt (S.card : ℝ) / 50 ≤ Real.sqrt (ε * S.card / 2000) := by
    rw [Real.le_sqrt (by positivity) (by positivity), div_pow, mul_pow,
      Real.sq_sqrt (by positivity)]
    have : (0 : ℝ) ≤ S.card := by positivity
    nlinarith
  have hLm₂ : ε * S.card / 2000 ≤ Real.log (S.card : ℝ) * m₂ := by
    have h := hm₂lower
    rw [div_le_iff₀ hlogpos] at h
    linarith
  have e3 : Real.sqrt (ε * S.card / 2000) ≤
      Real.sqrt (Real.log (S.card : ℝ)) * Real.sqrt (m₂ : ℝ) := by
    rw [← Real.sqrt_mul hlogpos.le]
    exact Real.sqrt_le_sqrt hLm₂
  have hsm : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmpos
  have hsm₂ : 0 < Real.sqrt (m₂ : ℝ) := Real.sqrt_pos.mpr hm₂pos
  have hnpos : (0 : ℝ) < S.card := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity), hC]
  calc
    (2 ^ 24 : ℝ) * ((S.card : ℝ) * Real.sqrt (m : ℝ))
      ≤ 2 ^ 24 * ((S.card : ℝ) * Real.sqrt (S.card : ℝ)) := by gcongr
    _ = (50 * 2 ^ 24 / ε ^ 2) * (ε * S.card) * (ε * Real.sqrt (S.card : ℝ) / 50) := by
        field_simp
    _ ≤ (50 * 2 ^ 24 / ε ^ 2) * ((S \ R₁).card : ℝ) *
          (Real.sqrt (Real.log (S.card : ℝ)) * Real.sqrt (m₂ : ℝ)) := by
        gcongr
        exact e2.trans e3
    _ = (50 * 2 ^ 24 / ε ^ 2) * Real.sqrt (Real.log (S.card : ℝ)) *
          (((S \ R₁).card : ℝ) * Real.sqrt (m₂ : ℝ)) := by ring

/-- Relaxing the constant in a Corollary 1.4 type bound. -/
private theorem cor14_relax {a b C' Cε x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hC : C' ≤ Cε) (h : a ≤ b + C' * x / y) : a ≤ b + Cε * x / y :=
  h.trans (add_le_add le_rfl
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC hx) hy))

/-- Corollary 1.4. -/
theorem corollary14 : Corollary14Statement := by
  intro ε hε0 hε1
  obtain ⟨N, hN⟩ := cor14_eventually_threshold ε hε0
  have hCpos : 0 < section3Constant := by
    unfold section3Constant
    positivity
  have hG : 0 ≤ smallGroundConstant N := by
    unfold smallGroundConstant
    positivity
  have hsC := Real.sqrt_nonneg section3Constant
  have hK : 0 ≤ 50 * section3Constant / ε ^ 2 := by positivity
  refine ⟨smallGroundConstant N + 2 * Real.sqrt section3Constant +
      2 * section3Constant + 50 * section3Constant / ε ^ 2, by positivity, ?_⟩
  intro p hp S hS m hm hmε z
  have hn2 : (2 : ℝ) ≤ S.card := by exact_mod_cast hS
  have hmS : m ≤ S.card := by
    have : (m : ℝ) ≤ S.card := by nlinarith
    exact_mod_cast this
  have hx := Real.sqrt_nonneg (Real.log (S.card : ℝ))
  have hy : 0 ≤ (S.card : ℝ) * Real.sqrt (m : ℝ) := by positivity
  have hp0 : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
  by_cases hSN : S.card < N
  · apply cor14_relax hx hy (C' := smallGroundConstant N) (by linarith)
    exact (@small_ground_trivial_bound p m N ⟨hp.ne_zero⟩ S hS hSN hm hmS z).trans
      (le_add_of_nonneg_left hp0)
  · push Not at hSN
    have hthr := hN S.card hSN
    obtain ⟨hHalf, -⟩ := cor14_threshold_bounds ε hε0 hε1 S.card hthr hS
    by_cases hsmall : (m : ℝ) ≤ section3Constant * Real.log (S.card : ℝ)
    · apply cor14_relax hx hy (C' := 2 * Real.sqrt section3Constant) (by linarith)
      exact (cor14_small_m hp S hS hm hsmall hHalf z).trans (le_add_of_nonneg_left hp0)
    · push Not at hsmall
      by_cases hmid : (m : ℝ) ≤ (1 / 1000 : ℝ) * S.card / Real.log (S.card : ℝ)
      · apply cor14_relax hx hy (C' := 2 * section3Constant) (by linarith)
        exact cor14_middle_m hp S hS hsmall.le hmid z
      · push Not at hmid
        apply cor14_relax hx hy (C' := 50 * section3Constant / ε ^ 2) (by linarith)
        exact cor14_large_m hp ε hε0 hε1 S hS hmε hthr hmid z

end

end GrahamRearrangement
