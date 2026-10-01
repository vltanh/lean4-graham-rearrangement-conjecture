module

public import GrahamRearrangement.BooleanSlice.Lemmas

@[expose] public section

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Section 3: proof of Theorem 1.3

This file combines Lemmas 3.1--3.7 with the dyadic Fourier reduction.
-/

noncomputable section

def lowPsiNonzero {p m : ℕ} [NeZero p]
    (P : Fin m → Finset (ZMod p)) (t : ℕ) : Finset (ZMod p) :=
  Finset.univ.filter fun χ => χ ≠ 0 ∧ psi P χ < 2 * t

theorem lowPsi_partition {p m t : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (P : Fin m → Finset (ZMod p)) :
    (lowPsiNonzero P t).card ≤
      (((Finset.univ.erase (0 : ZMod p)) \ Dset S m t).filter
        (fun χ => psi P χ < 2 * t)).card +
      ((Dset S m t \ Bset S m (2000 * t)).filter
        (fun χ => psi P χ < 2 * t)).card +
      (Bset S m (2000 * t) \ {0}).card := by
  classical
  set A := ((Finset.univ.erase (0 : ZMod p)) \ Dset S m t).filter
    (fun χ => psi P χ < 2 * t) with hA
  set B := (Dset S m t \ Bset S m (2000 * t)).filter
    (fun χ => psi P χ < 2 * t) with hB
  set C := Bset S m (2000 * t) \ {0} with hC
  have hsub : lowPsiNonzero P t ⊆ A ∪ B ∪ C := by
    intro χ hχ
    have hlow : χ ≠ 0 ∧ psi P χ < 2 * t := (Finset.mem_filter.1 hχ).2
    by_cases hD : χ ∈ Dset S m t
    · by_cases hBt : χ ∈ Bset S m (2000 * t)
      · exact Finset.mem_union_right _
          (Finset.mem_sdiff.2 ⟨hBt, by simpa using hlow.1⟩)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨hD, hBt⟩, hlow.2⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.2
          ⟨Finset.mem_sdiff.2 ⟨Finset.mem_erase.2 ⟨hlow.1, Finset.mem_univ _⟩, hD⟩,
            hlow.2⟩))
  calc
    (lowPsiNonzero P t).card ≤ (A ∪ B ∪ C).card := Finset.card_le_card hsub
    _ ≤ (A ∪ B).card + C.card := Finset.card_union_le _ _
    _ ≤ A.card + B.card + C.card :=
      Nat.add_le_add_right (Finset.card_union_le _ _) _

/-- In the Section 3 range, `m ≥ 2^23` (since `log |S| ≥ log 2 > 0.69`). -/
theorem theorem13_m_ge (SCard m : ℕ)
    (hS : 2 ≤ SCard)
    (hlower : (2 ^ 24 : ℝ) * Real.log (SCard : ℝ) ≤ m) :
    2 ^ 23 ≤ m := by
  have hlogmono : Real.log 2 ≤ Real.log (SCard : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hS)
  have hlog2 := Real.log_two_gt_d9
  have : (2 ^ 23 : ℝ) ≤ m := by nlinarith
  exact_mod_cast this

/-- Expected number of nonzero characters with ψ(χ)<2t.  This is the estimate
immediately preceding the bounds for A₀ and A_t in the proof of Theorem 1.3. -/
theorem expected_lowPsi_bound {p m t : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hS : 2 ≤ S.card)
    (hmLower : (2 ^ 24 : ℝ) * Real.log (S.card : ℝ) ≤ m)
    (hmUpper : (m : ℝ) ≤
      (1 / 1000 : ℝ) * S.card / Real.log (S.card : ℝ))
    (ht : 0 < t) (htsmall : t ≤ m / (2000 ^ 2)) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    partitionExpectation (m := m) S
        (fun P => ((lowPsiNonzero P t).card : ℝ)) ≤
      (10 ^ 4 : ℝ) * p * Real.sqrt t /
        ((S.card : ℝ) * Real.sqrt m) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  classical
  obtain ⟨hm, hm4, hbig⟩ :=
    section3_basic_bounds S.card m hS hmLower hmUpper
  have hmS : m ≤ S.card := le_trans hm4 (Nat.div_le_self _ _)
  set T₁ := (Finset.univ.erase (0 : ZMod p)) \ Dset S m t with hT₁
  set T₂ := Dset S m t \ Bset S m (2000 * t) with hT₂
  set T₃ := Bset S m (2000 * t) \ {0} with hT₃
  have h1 : ∀ χ ∈ T₁,
      partitionMass (m := m) S (fun P => psi P χ < 2 * t) ≤
        1 / (S.card : ℝ) ^ 9 := by
    intro χ hχ
    have hχ0 : χ ≠ 0 := (Finset.mem_erase.1 (Finset.mem_sdiff.1 hχ).1).1
    have hχD : χ ∉ Dset S m t := (Finset.mem_sdiff.1 hχ).2
    exact lemma3_1 hp S hS hmLower hmUpper ht χ hχ0 hχD
  have h2 : ∀ χ ∈ T₂,
      partitionMass (m := m) S (fun P => psi P χ < 2 * t) ≤
        1 / (S.card : ℝ) ^ 9 := by
    intro χ hχ
    rcases Finset.mem_sdiff.1 hχ with ⟨hD, hB⟩
    exact lemma3_3 hp S hS hmLower hmUpper ht χ hD hB
  have hE1 :=
    Section3.partitionExpectation_filter_le (m := m)
      S T₁ (fun χ P => psi P χ < 2 * t) h1
  have hE2 :=
    Section3.partitionExpectation_filter_le (m := m)
      S T₂ (fun χ P => psi P χ < 2 * t) h2
  have hparts := Section3.balancedPartitions_nonempty (m := m) S hm hmS
  have hExp :
      partitionExpectation (m := m) S
          (fun P => ((lowPsiNonzero P t).card : ℝ)) ≤
        (T₁.card : ℝ) / (S.card : ℝ) ^ 9 +
        (T₂.card : ℝ) / (S.card : ℝ) ^ 9 +
        (T₃.card : ℝ) := by
    calc
      _ ≤ partitionExpectation (m := m) S
          (fun P =>
            (((T₁.filter fun χ => psi P χ < 2 * t).card : ℝ) +
             ((T₂.filter fun χ => psi P χ < 2 * t).card : ℝ)) +
             (T₃.card : ℝ)) := by
            unfold partitionExpectation
            apply uniformExpectation_mono
            intro P _
            exact_mod_cast lowPsi_partition (t := t) S P
      _ = partitionExpectation (m := m) S
            (fun P => ((T₁.filter fun χ => psi P χ < 2 * t).card : ℝ)) +
          partitionExpectation (m := m) S
            (fun P => ((T₂.filter fun χ => psi P χ < 2 * t).card : ℝ)) +
          (T₃.card : ℝ) := by
            unfold partitionExpectation
            rw [uniformExpectation_add, uniformExpectation_add,
              uniformExpectation_const _ hparts]
      _ ≤ _ := by linarith
  -- Lemma 3.4 at scale `2000t`.
  have h2000 : 2000 * t ≤ m / 2000 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    have := (Nat.le_div_iff_mul_le (by norm_num)).1 htsmall
    linarith
  have hB := lemma3_4 hp S hbig hm (Nat.mul_pos (by norm_num) ht) h2000
  push_cast at hB
  have hT12 : (T₁.card : ℝ) + T₂.card ≤ p := by
    have hdisj : Disjoint T₁ T₂ := by
      rw [Finset.disjoint_left]
      intro χ h₁ h₂
      exact (Finset.mem_sdiff.1 h₁).2 (Finset.mem_sdiff.1 h₂).1
    have hcard : T₁.card + T₂.card ≤ p := by
      rw [← Finset.card_union_of_disjoint hdisj]
      calc (T₁ ∪ T₂).card ≤ (Finset.univ : Finset (ZMod p)).card :=
            Finset.card_le_univ _
        _ = p := by rw [Finset.card_univ, ZMod.card]
    exact_mod_cast hcard
  have hzero : (0 : ZMod p) ∈ Bset S m (2000 * t) :=
    (Bset_zero_neg (m := m) (t := 2000 * t) S).1
  have hT3card : (T₃.card : ℝ) + 1 = (Bset S m (2000 * t)).card := by
    have : T₃.card + 1 = (Bset S m (2000 * t)).card := by
      rw [hT₃, Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.2 hzero),
        Finset.card_singleton]
      have : 1 ≤ (Bset S m (2000 * t)).card :=
        Finset.card_pos.2 ⟨0, hzero⟩
      omega
    exact_mod_cast this
  have hSpos : (0 : ℝ) < S.card := by
    have : (2 : ℝ) ≤ S.card := by exact_mod_cast hS
    linarith
  have hSge1 : (1 : ℝ) ≤ S.card := by
    have : (2 : ℝ) ≤ S.card := by exact_mod_cast hS
    linarith
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hsqrtm : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hmpos
  have hsqrtt1 : 1 ≤ Real.sqrt (t : ℝ) := by
    rw [Real.one_le_sqrt]; exact htR
  have hD : (0 : ℝ) < (S.card : ℝ) * Real.sqrt m := by positivity
  -- `√(2000 t) ≤ 44.73 √t`.
  have hsqrt2000 : Real.sqrt ((2000 : ℝ) * t) ≤ 4473 / 100 * Real.sqrt t := by
    rw [Real.sqrt_mul (by norm_num)]
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hT3 :
      (T₃.card : ℝ) ≤ 8946 * p * Real.sqrt t / ((S.card : ℝ) * Real.sqrt m) := by
    have h1' : (T₃.card : ℝ) ≤
        200 * p * Real.sqrt (2000 * t) / ((S.card : ℝ) * Real.sqrt m) := by
      linarith
    refine le_trans h1' ?_
    apply div_le_div_of_nonneg_right _ hD.le
    nlinarith
  -- The noise term `p/|S|^9`.
  have hsqrtm_le : Real.sqrt (m : ℝ) ≤ S.card := by
    calc Real.sqrt (m : ℝ) ≤ m :=
          Real.sqrt_le_self_iff.2 (Or.inr (Nat.one_le_cast.2 hm))
      _ ≤ S.card := by exact_mod_cast hmS
  have hnoise :
      (p : ℝ) / (S.card : ℝ) ^ 9 ≤
        1054 * p * Real.sqrt t / ((S.card : ℝ) * Real.sqrt m) := by
    rw [div_le_div_iff₀ (by positivity) hD]
    have hpow : (S.card : ℝ) * Real.sqrt m ≤ (S.card : ℝ) ^ 9 := by
      calc (S.card : ℝ) * Real.sqrt m ≤ (S.card : ℝ) * S.card :=
            mul_le_mul_of_nonneg_left hsqrtm_le hSpos.le
        _ = (S.card : ℝ) ^ 2 := by ring
        _ ≤ (S.card : ℝ) ^ 9 := pow_le_pow_right₀ hSge1 (by norm_num)
    have h9 : 0 < (S.card : ℝ) ^ 9 := by positivity
    calc (p : ℝ) * ((S.card : ℝ) * Real.sqrt m)
        ≤ (p : ℝ) * (S.card : ℝ) ^ 9 := mul_le_mul_of_nonneg_left hpow hpR.le
      _ ≤ 1054 * p * Real.sqrt t * (S.card : ℝ) ^ 9 := by
          have : (p : ℝ) ≤ 1054 * p * Real.sqrt t := by nlinarith
          exact mul_le_mul_of_nonneg_right this h9.le
  calc
    partitionExpectation (m := m) S
        (fun P => ((lowPsiNonzero P t).card : ℝ))
      ≤ (T₁.card : ℝ) / (S.card : ℝ) ^ 9 +
        (T₂.card : ℝ) / (S.card : ℝ) ^ 9 +
        (T₃.card : ℝ) := hExp
    _ = ((T₁.card : ℝ) + T₂.card) / (S.card : ℝ) ^ 9 + (T₃.card : ℝ) := by ring
    _ ≤ (p : ℝ) / (S.card : ℝ) ^ 9 +
        8946 * p * Real.sqrt t / ((S.card : ℝ) * Real.sqrt m) := by
          gcongr
    _ ≤ 1054 * p * Real.sqrt t / ((S.card : ℝ) * Real.sqrt m) +
        8946 * p * Real.sqrt t / ((S.card : ℝ) * Real.sqrt m) := by
          gcongr
    _ = (10 ^ 4 : ℝ) * p * Real.sqrt t /
          ((S.card : ℝ) * Real.sqrt m) := by ring

theorem expected_A0_bound {p m : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hS : 2 ≤ S.card)
    (hmLower : (2 ^ 24 : ℝ) * Real.log (S.card : ℝ) ≤ m)
    (hmUpper : (m : ℝ) ≤
      (1 / 1000 : ℝ) * S.card / Real.log (S.card : ℝ)) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    partitionExpectation (m := m) S (fun P => ((A0 P).card : ℝ)) ≤
      1 + (10 ^ 4 : ℝ) * p /
        ((S.card : ℝ) * Real.sqrt m) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  classical
  obtain ⟨hm, hm4, _hbig⟩ :=
    section3_basic_bounds S.card m hS hmLower hmUpper
  have hmS : m ≤ S.card := le_trans hm4 (Nat.div_le_self _ _)
  have hm23 := theorem13_m_ge S.card m hS hmLower
  have hm2000 : 1 ≤ m / (2000 ^ 2) := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    have : (2 : ℕ) ^ 23 = 8388608 := by norm_num
    omega
  have hlow :=
    expected_lowPsi_bound (t := 1) hp S hS hmLower hmUpper (by norm_num) hm2000
  have hpoint : ∀ P ∈ balancedPartitions (m := m) S,
      ((A0 P).card : ℝ) ≤ 1 + ((lowPsiNonzero P 1).card : ℝ) := by
    intro P _
    have hsub : A0 P ⊆ insert 0 (lowPsiNonzero P 1) := by
      intro χ hχ
      by_cases hz : χ = 0
      · rw [hz]
        exact Finset.mem_insert_self _ _
      · apply Finset.mem_insert_of_mem
        have hψ : psi P χ < 1 := (Finset.mem_filter.1 hχ).2
        apply Finset.mem_filter.2
        refine ⟨Finset.mem_univ _, hz, ?_⟩
        push_cast
        linarith
    have hcard : (A0 P).card ≤ 1 + (lowPsiNonzero P 1).card := by
      calc (A0 P).card ≤ (insert 0 (lowPsiNonzero P 1)).card :=
            Finset.card_le_card hsub
        _ ≤ (lowPsiNonzero P 1).card + 1 := Finset.card_insert_le _ _
        _ = 1 + (lowPsiNonzero P 1).card := by ring
    exact_mod_cast hcard
  have hparts :=
    Section3.balancedPartitions_nonempty (m := m) S hm hmS
  calc
    partitionExpectation (m := m) S (fun P => ((A0 P).card : ℝ))
      ≤ partitionExpectation (m := m) S
          (fun P => 1 + ((lowPsiNonzero P 1).card : ℝ)) := by
            unfold partitionExpectation
            exact uniformExpectation_mono _ _ _ hpoint
    _ = 1 + partitionExpectation (m := m) S
          (fun P => ((lowPsiNonzero P 1).card : ℝ)) := by
            unfold partitionExpectation
            rw [uniformExpectation_add, uniformExpectation_const _ hparts]
    _ ≤ 1 + (10 ^ 4 : ℝ) * p /
          ((S.card : ℝ) * Real.sqrt m) := by
            have h1 : Real.sqrt ((1 : ℕ) : ℝ) = 1 := by simp
            rw [h1, mul_one] at hlow
            linarith

theorem expected_At_bound {p m t : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hS : 2 ≤ S.card)
    (hmLower : (2 ^ 24 : ℝ) * Real.log (S.card : ℝ) ≤ m)
    (hmUpper : (m : ℝ) ≤
      (1 / 1000 : ℝ) * S.card / Real.log (S.card : ℝ))
    (ht : 0 < t) (htsmall : t ≤ m / 2 ^ 22) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    partitionExpectation (m := m) S (fun P => ((At P t).card : ℝ)) ≤
      (10 ^ 4 : ℝ) * p * Real.sqrt t /
        ((S.card : ℝ) * Real.sqrt m) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  classical
  have h2000 : 2000 ^ 2 ≤ 2 ^ 22 := by norm_num
  have hsmall' : t ≤ m / (2000 ^ 2) :=
    le_trans htsmall (Nat.div_le_div_left h2000 (by norm_num))
  have hlow :=
    expected_lowPsi_bound hp S hS hmLower hmUpper ht hsmall'
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hpoint : ∀ P ∈ balancedPartitions (m := m) S,
      ((At P t).card : ℝ) ≤ ((lowPsiNonzero P t).card : ℝ) := by
    intro P _
    have hsub : At P t ⊆ lowPsiNonzero P t := by
      intro χ hχ
      have htmem : (t : ℝ) ≤ psi P χ ∧ psi P χ < 2 * t :=
        (Finset.mem_filter.1 hχ).2
      have hχ0 : χ ≠ 0 := by
        intro hz
        rw [hz, psi_zero] at htmem
        linarith [htmem.1]
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hχ0, htmem.2⟩
    exact_mod_cast Finset.card_le_card hsub
  calc
    partitionExpectation (m := m) S (fun P => ((At P t).card : ℝ))
      ≤ partitionExpectation (m := m) S
          (fun P => ((lowPsiNonzero P t).card : ℝ)) := by
            unfold partitionExpectation
            exact uniformExpectation_mono _ _ _ hpoint
    _ ≤ _ := hlow

theorem expected_At_trivial {p m t : ℕ} [NeZero p]
    (S : Finset (ZMod p)) :
    partitionExpectation (m := m) S (fun P => ((At P t).card : ℝ)) ≤ p := by
  unfold partitionExpectation uniformExpectation
  have hsum :
      (∑ P ∈ balancedPartitions (m := m) S, ((At P t).card : ℝ)) ≤
        (p : ℝ) * (balancedPartitions (m := m) S).card := by
    calc
      (∑ P ∈ balancedPartitions (m := m) S, ((At P t).card : ℝ))
          ≤ ∑ _P ∈ balancedPartitions (m := m) S, (p : ℝ) := by
            apply Finset.sum_le_sum
            intro P _
            have h := Finset.card_le_univ (At P t)
            rw [ZMod.card] at h
            exact_mod_cast h
      _ = (p : ℝ) * (balancedPartitions (m := m) S).card := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  exact div_le_of_le_mul₀ (by positivity) (by positivity) hsum

/-- Theorem 1.3 with the paper's explicit choice C=2^24. -/
theorem theorem13_explicit :
    ∀ (p : ℕ) (hp : p.Prime),
      letI : NeZero p := ⟨hp.ne_zero⟩
      ∀ (S : Finset (ZMod p)), 2 ≤ S.card →
      ∀ (m : ℕ),
        (2 ^ 24 : ℝ) * Real.log (S.card : ℝ) ≤ (m : ℝ) →
        (m : ℝ) ≤ (1 / 1000 : ℝ) * S.card /
          Real.log (S.card : ℝ) →
        ∀ z : ZMod p,
          sliceMass S m z ≤
            1 / (p : ℝ) +
              (2 ^ 24 : ℝ) /
                ((S.card : ℝ) * Real.sqrt (m : ℝ)) := by
  intro p hp
  letI : NeZero p := ⟨hp.ne_zero⟩
  intro S hS m hmLower hmUpper z
  obtain ⟨hm, hm4, _hbig⟩ :=
    section3_basic_bounds S.card m hS hmLower hmUpper
  have hmS : m ≤ S.card := le_trans hm4 (Nat.div_le_self _ _)
  have h34 := equation_3_4 hp S hS hm hm4 z
  have hA0 := expected_A0_bound hp S hS hmLower hmUpper
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hSpos : (0 : ℝ) < S.card := by
    have : (2 : ℝ) ≤ S.card := by exact_mod_cast hS
    linarith
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hsqrtm : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hmpos
  have hD : (0 : ℝ) < (S.card : ℝ) * Real.sqrt m := by positivity
  set K : ℝ := (10 ^ 4 : ℝ) / ((S.card : ℝ) * Real.sqrt m) with hK
  set E : ℕ → ℝ := fun l => partitionExpectation (m := m) S
      (fun P => ((At P (2 ^ l)).card : ℝ)) with hE
  have hsmall : ∀ l, 2 ^ l ≤ m / 2 ^ 22 →
      E l ≤ (p : ℝ) * K * Real.sqrt ((2 : ℝ) ^ l) := by
    intro l hl
    have ht : 0 < 2 ^ l := pow_pos (by norm_num) _
    have h := expected_At_bound hp S hS hmLower hmUpper ht hl
    push_cast at h
    calc E l ≤ (10 ^ 4 : ℝ) * p * Real.sqrt ((2 : ℝ) ^ l) /
          ((S.card : ℝ) * Real.sqrt m) := h
      _ = (p : ℝ) * K * Real.sqrt ((2 : ℝ) ^ l) := by
          rw [hK]
          field_simp
  have htriv : ∀ l, E l ≤ p := fun l => expected_At_trivial S
  have hdy :=
    Auxiliary.weighted_dyadic_split m p K E hpR (by positivity) hsmall htriv
  -- The terminal tail `22 exp(-m/2^22) ≤ 22/(|S| √m)`.
  have hlogpos : 0 < Real.log (S.card : ℝ) := by
    apply Real.log_pos
    have : (2 : ℝ) ≤ S.card := by exact_mod_cast hS
    linarith
  have htail :
      22 * Real.exp (-(m : ℝ) / 2 ^ 22) ≤ 22 / (S.card : ℝ) ^ 4 := by
    have hlog : 4 * Real.log (S.card : ℝ) ≤ (m : ℝ) / 2 ^ 22 := by
      rw [le_div_iff₀ (by norm_num)]
      linarith
    have hexp : Real.exp (-(m : ℝ) / 2 ^ 22) ≤
        Real.exp (-(4 * Real.log (S.card : ℝ))) := by
      apply Real.exp_le_exp.mpr
      rw [neg_div]
      linarith
    have hpow : Real.exp (4 * Real.log (S.card : ℝ)) = (S.card : ℝ) ^ 4 := by
      have := Real.exp_nat_mul (Real.log (S.card : ℝ)) 4
      push_cast at this
      rw [this, Real.exp_log hSpos]
    rw [Real.exp_neg, hpow] at hexp
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hexp (by norm_num)
  have htail2 :
      22 / (S.card : ℝ) ^ 4 ≤ 22 / ((S.card : ℝ) * Real.sqrt m) := by
    apply div_le_div_of_nonneg_left (by norm_num) hD
    have hsqrtm_le : Real.sqrt (m : ℝ) ≤ S.card := by
      calc Real.sqrt (m : ℝ) ≤ m :=
            Real.sqrt_le_self_iff.2 (Or.inr (Nat.one_le_cast.2 hm))
        _ ≤ S.card := by exact_mod_cast hmS
    have hSge1 : (1 : ℝ) ≤ S.card := by
      have : (2 : ℝ) ≤ S.card := by exact_mod_cast hS
      linarith
    calc (S.card : ℝ) * Real.sqrt m ≤ (S.card : ℝ) * S.card :=
          mul_le_mul_of_nonneg_left hsqrtm_le hSpos.le
      _ = (S.card : ℝ) ^ 2 := by ring
      _ ≤ (S.card : ℝ) ^ 4 := pow_le_pow_right₀ hSge1 (by norm_num)
  have hA0' : (1 / (p : ℝ)) *
      partitionExpectation (m := m) S (fun P => ((A0 P).card : ℝ)) ≤
        1 / (p : ℝ) + K := by
    calc (1 / (p : ℝ)) *
          partitionExpectation (m := m) S (fun P => ((A0 P).card : ℝ))
        ≤ (1 / (p : ℝ)) * (1 + (10 ^ 4 : ℝ) * p /
            ((S.card : ℝ) * Real.sqrt m)) :=
          mul_le_mul_of_nonneg_left hA0 (by positivity)
      _ = 1 / (p : ℝ) + K := by
          rw [hK]
          field_simp
  calc
    sliceMass S m z
      ≤ (1 / (p : ℝ)) *
          partitionExpectation (m := m) S (fun P => ((A0 P).card : ℝ)) +
        (1 / (p : ℝ)) *
          ∑ l ∈ Finset.range (Nat.log2 m + 1),
            E l * Real.exp (-(2 : ℝ) ^ l) := h34
    _ ≤ (1 / (p : ℝ) + K) +
        (2 * K + 22 * Real.exp (-(m : ℝ) / 2 ^ 22)) := add_le_add hA0' hdy
    _ ≤ (1 / (p : ℝ) + K) +
        (2 * K + 22 / ((S.card : ℝ) * Real.sqrt m)) := by
          linarith
    _ = 1 / (p : ℝ) + 30022 / ((S.card : ℝ) * Real.sqrt m) := by
          rw [hK]
          ring
    _ ≤ 1 / (p : ℝ) +
          (2 ^ 24 : ℝ) / ((S.card : ℝ) * Real.sqrt m) := by
          gcongr
          norm_num

/-- Theorem 1.3. -/
theorem theorem13 : Theorem13Statement := by
  refine ⟨(2 ^ 24 : ℝ), by norm_num, ?_⟩
  intro p hp
  letI : NeZero p := ⟨hp.ne_zero⟩
  intro S hS m hmLower hmUpper z
  exact theorem13_explicit p hp S hS m hmLower hmUpper z

end

end GrahamRearrangement
