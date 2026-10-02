module

public import GrahamRearrangement.BooleanSlice.Fourier

@[expose] public section

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Section 3: concentration and deterministic low-spectrum lemmas

Lemmas 3.1--3.7 and the proof of Lemma 3.4.
-/

noncomputable section

/-- The set of points farther than the Lemma 3.1 threshold from `χx'`. -/
def farSet {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (m t : ℕ) (χ x' : ZMod p) : Finset (ZMod p) :=
  S.filter fun x =>
    8 * Real.sqrt ((t : ℝ) / m) <
      zmodNorm (χ * x - χ * x')

theorem near_far_card {p m t : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (χ x' : ZMod p) :
    (nearSet S m t χ (χ * x')).card +
      (farSet S m t χ x').card = S.card := by
  classical
  have hdisj :
      Disjoint (nearSet S m t χ (χ * x')) (farSet S m t χ x') := by
    rw [Finset.disjoint_left]
    intro x hnear hfar
    have hn := (Finset.mem_filter.1 hnear).2
    have hf := (Finset.mem_filter.1 hfar).2
    linarith
  have hunion :
      nearSet S m t χ (χ * x') ∪ farSet S m t χ x' = S := by
    ext x
    simp only [nearSet, farSet, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩)
      · exact hx
      · exact hx
    · intro hx
      by_cases hle :
          zmodNorm (χ * x - χ * x') ≤
            8 * Real.sqrt ((t : ℝ) / m)
      · exact Or.inl ⟨hx, hle⟩
      · exact Or.inr ⟨hx, lt_of_not_ge hle⟩
  rw [← Finset.card_union_of_disjoint hdisj, hunion]

/-- If `χ ≠ 0` and `χ ∉ D_t`, then for every `x'` at least a quarter of `S` lies outside the
`‖·‖ₚ`-ball of radius `8√(t/m)` around `χx'`. -/
theorem farSet_quarter {p m t : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (χ : ZMod p)
    (hχ0 : χ ≠ 0) (hχD : χ ∉ Dset S m t)
    {x' : ZMod p} :
    S.card ≤ 4 * (farSet S m t χ x').card := by
  classical
  by_contra h
  have hnot : 4 * (farSet S m t χ x').card < S.card := Nat.lt_of_not_ge h
  have hpartition := near_far_card (m := m) (t := t) S χ x'
  have hnear :
      3 * S.card ≤ 4 * (nearSet S m t χ (χ * x')).card := by
    omega
  apply hχD
  simp only [Dset, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hχ0, χ * x', hnear⟩

/-- `‖0‖ₚ = 0`. -/
theorem sec3_zmodNorm_zero {p : ℕ} [NeZero p] : zmodNorm (0 : ZMod p) = 0 := by
  simp [zmodNorm, distToInt]

/-- `log |S| ≥ 1/2` and `m log |S| ≤ |S|/1000` in the Section 3 range. -/
theorem section3_log_facts (SCard m : ℕ)
    (hS : 2 ≤ SCard)
    (hupper : (m : ℝ) ≤
      (1 / 1000 : ℝ) * SCard / Real.log (SCard : ℝ)) :
    (1 / 2 : ℝ) ≤ Real.log (SCard : ℝ) ∧
      (m : ℝ) * Real.log (SCard : ℝ) ≤ (SCard : ℝ) / 1000 := by
  have hlogmono : Real.log 2 ≤ Real.log (SCard : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hS)
  have hlog : (1 / 2 : ℝ) ≤ Real.log (SCard : ℝ) :=
    le_trans Auxiliary.log_two_ge_half hlogmono
  have hlogpos : 0 < Real.log (SCard : ℝ) := by linarith
  refine ⟨hlog, ?_⟩
  have h := (le_div_iff₀ hlogpos).1 hupper
  linarith

/-- Section 3 range implies the elementary bounds used by the random partition. -/
theorem section3_basic_bounds (SCard m : ℕ)
    (hS : 2 ≤ SCard)
    (hlower : (2 ^ 24 : ℝ) * Real.log (SCard : ℝ) ≤ m)
    (hupper : (m : ℝ) ≤
      (1 / 1000 : ℝ) * SCard / Real.log (SCard : ℝ)) :
    0 < m ∧ m ≤ SCard / 4 ∧ 10 ^ 7 ≤ SCard := by
  obtain ⟨hlog, hmlog⟩ := section3_log_facts SCard m hS hupper
  have hlog2 : (69 / 100 : ℝ) ≤ Real.log (SCard : ℝ) := by
    have h1 : Real.log 2 ≤ Real.log (SCard : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hS)
    have h2 := Real.log_two_gt_d9
    linarith
  have hbigm : (10 ^ 7 : ℝ) ≤ m := by nlinarith
  have hm : 0 < m := by
    have : (0 : ℝ) < m := by linarith
    exact_mod_cast this
  have hm500 : (500 : ℝ) * m ≤ SCard := by
    have hm0 : (0 : ℝ) ≤ m := by positivity
    nlinarith
  have hm4 : 4 * m ≤ SCard := by
    have : (4 : ℝ) * m ≤ SCard := by
      have hm0 : (0 : ℝ) ≤ m := by positivity
      linarith
    exact_mod_cast this
  refine ⟨hm, (Nat.le_div_iff_mul_le (by norm_num)).2 (by linarith), ?_⟩
  have : (10 ^ 7 : ℝ) ≤ SCard := by linarith
  exact_mod_cast this

/-- In the Section 3 range, `|S| ≥ 500m`. -/
theorem section3_card_ge_500m (SCard m : ℕ)
    (hS : 2 ≤ SCard)
    (hupper : (m : ℝ) ≤
      (1 / 1000 : ℝ) * SCard / Real.log (SCard : ℝ)) :
    500 * m ≤ SCard := by
  obtain ⟨hlog, hmlog⟩ := section3_log_facts SCard m hS hupper
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have : (500 : ℝ) * m ≤ SCard := by nlinarith
  exact_mod_cast this

/-- The numerical exponential tail comparison used in Lemmas 3.1 and 3.3.

The hypotheses `0 < m` and `0 < c` are necessary: for `m = 0` (allowed by
`hmUpper` alone) or `c ≤ 0` the exponent is `≥ 0` and the left side is `≥ |S|`. -/
theorem section3_tail_nine (SCard m : ℕ)
    (hS : 2 ≤ SCard) (hm : 0 < m)
    (hmUpper : (m : ℝ) ≤
      (1 / 1000 : ℝ) * SCard / Real.log (SCard : ℝ))
    (c : ℝ) (hc0 : 0 < c) (hc : c ≤ 100) :
    (SCard : ℝ) * Real.exp (-(SCard : ℝ) / (c * m)) ≤
      1 / (SCard : ℝ) ^ 9 := by
  obtain ⟨hlog, hmlog⟩ := section3_log_facts SCard m hS hmUpper
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hSpos : (0 : ℝ) < SCard := by
    have : (2 : ℝ) ≤ SCard := by exact_mod_cast hS
    linarith
  have hratio :
      10 * Real.log (SCard : ℝ) ≤ (SCard : ℝ) / (c * m) := by
    rw [le_div_iff₀ (by positivity)]
    have hlogpos : 0 < Real.log (SCard : ℝ) := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hc (le_of_lt (mul_pos hmpos hlogpos))]
  have hexp :
      Real.exp (-(SCard : ℝ) / (c * m)) ≤
        Real.exp (-(10 * Real.log (SCard : ℝ))) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hpow : Real.exp (10 * Real.log (SCard : ℝ)) = (SCard : ℝ) ^ 10 := by
    have := Real.exp_nat_mul (Real.log (SCard : ℝ)) 10
    push_cast at this
    rw [this, Real.exp_log hSpos]
  rw [Real.exp_neg, hpow] at hexp
  calc
    (SCard : ℝ) * Real.exp (-(SCard : ℝ) / (c * m))
      ≤ (SCard : ℝ) * ((SCard : ℝ) ^ 10)⁻¹ := by gcongr
    _ = 1 / (SCard : ℝ) ^ 9 := by
      field_simp

/-- Sharp form of (3.3): every block has at most `⌊|S|/m⌋+1` elements, so
`ψ(χ)` dominates the total within-block energy divided by `(⌊|S|/m⌋+1)²`. -/
theorem psi_ge_energy_div_sq {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hm : 0 < m) (hmS : m ≤ S.card)
    {P : Fin m → Finset (ZMod p)} (hP : IsBalancedPartition S P)
    (χ : ZMod p) :
    (1 / (((S.card / m : ℕ) : ℝ) + 1) ^ 2) *
        ∑ i, ∑ x ∈ P i, ∑ x' ∈ P i,
          zmodNorm (χ * x - χ * x') ^ 2
      ≤ psi P χ := by
  unfold psi
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have hb := Section3.balanced_block_size_bounds S hP i
  have hdiv : 0 < S.card / m := Nat.div_pos hmS hm
  have hcpos : (0 : ℝ) < (P i).card := by
    exact_mod_cast lt_of_lt_of_le hdiv hb.1
  have hcM : ((P i).card : ℝ) ≤ ((S.card / m : ℕ) : ℝ) + 1 := by
    exact_mod_cast hb.2
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hcpos.le hcM 2)

/-- Deterministic implication used in Lemma 3.1: if every point sees enough far
points in its own block, then ψ(χ)≥2t.

Since the row count `|S|/(16m)` is a natural-number floor, the paper's computation
via (3.3) has no slack; we use the sharp block-size bound instead, which needs
`32m ≤ |S|` (true in the Section 3 range, where `|S| ≥ 500m`). Without this
hypothesis the statement fails, e.g. for `|S| = 8`, `m = 2`, `t = 1`, `χ = 0`
(the row condition `8/32 = 0 ≤ ⋯` is vacuous while `ψ(0) = 0`). -/
theorem psi_ge_two_of_far_rows {p m t : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hS : 2 ≤ S.card)
    (hm : 0 < m) (hm4 : m ≤ S.card / 4) (hbig : 32 * m ≤ S.card)
    {P : Fin m → Finset (ZMod p)} (hP : IsBalancedPartition S P)
    (χ : ZMod p)
    (hrow : ∀ x' ∈ S,
      S.card / (16 * m) ≤
        ((pointBlock S P x' \ {x'}) ∩ farSet S m t χ x').card) :
    (2 : ℝ) * t ≤ psi P χ := by
  classical
  have hmS : m ≤ S.card := le_trans hm4 (Nat.div_le_self _ _)
  set k : ℕ := S.card / (16 * m) with hk
  set a : ℕ := S.card / m with ha
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hsq : (Real.sqrt ((t : ℝ) / m)) ^ 2 = (t : ℝ) / m :=
    Real.sq_sqrt (by positivity)
  -- Row lower bound: each row contains at least `k` far points.
  have henergy :
      (S.card : ℝ) * ((k : ℝ) * (64 * t / m)) ≤
        ∑ i, ∑ x ∈ P i, ∑ x' ∈ P i,
          zmodNorm (χ * x - χ * x') ^ 2 := by
    have hrows := Section3.partition_energy_lower_by_rows
      S P ⟨hP.1, hP.2.1, hP.2.2.1⟩
      (fun a b => zmodNorm (χ * b - χ * a) ^ 2)
      (fun _ => (k : ℝ) * (64 * t / m))
      (by
        intro i x' hx'
        have hxS : x' ∈ S := hP.1 i hx'
        have hidx : blockIndex S P x' = i :=
          blockIndex_eq_of_mem S hm hP hxS hx'
        have hcount := hrow x' hxS
        have hblock : pointBlock S P x' = P i := by
          unfold pointBlock
          rw [hidx]
        rw [hblock] at hcount
        set T := (P i \ {x'}) ∩ farSet S m t χ x' with hT
        have hTsub : T ⊆ P i := fun x hx =>
          (Finset.mem_sdiff.1 (Finset.mem_inter.1 hx).1).1
        have hthreshold :
            ∀ x ∈ T, (64 * t / m : ℝ) ≤ zmodNorm (χ * x - χ * x') ^ 2 := by
          intro x hx
          have hfar := (Finset.mem_inter.1 hx).2
          have hdist := (Finset.mem_filter.1 hfar).2
          have hs0 : 0 ≤ Real.sqrt ((t : ℝ) / m) := Real.sqrt_nonneg _
          have h8 : (8 * Real.sqrt ((t : ℝ) / m)) ^ 2 ≤
              zmodNorm (χ * x - χ * x') ^ 2 :=
            pow_le_pow_left₀ (by positivity) hdist.le 2
          have : (8 * Real.sqrt ((t : ℝ) / m)) ^ 2 = 64 * t / m := by
            rw [mul_pow, hsq]; ring
          linarith
        calc
          (k : ℝ) * (64 * t / m)
              ≤ (T.card : ℝ) * (64 * t / m) := by
                apply mul_le_mul_of_nonneg_right _ (by positivity)
                exact_mod_cast hcount
          _ ≤ ∑ x ∈ T, zmodNorm (χ * x - χ * x') ^ 2 := by
                have := Finset.card_nsmul_le_sum T
                  (fun x => zmodNorm (χ * x - χ * x') ^ 2) (64 * t / m) hthreshold
                simpa [nsmul_eq_mul] using this
          _ ≤ ∑ x ∈ P i, zmodNorm (χ * x - χ * x') ^ 2 :=
                Finset.sum_le_sum_of_subset_of_nonneg hTsub
                  (fun _ _ _ => by positivity))
    have hcomm :
        ∑ i, ∑ x ∈ P i, ∑ y ∈ P i, zmodNorm (χ * y - χ * x) ^ 2 =
          ∑ i, ∑ x ∈ P i, ∑ x' ∈ P i, zmodNorm (χ * x - χ * x') ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    rw [hcomm] at hrows
    simpa using hrows
  have hpsi := psi_ge_energy_div_sq S hm hmS hP χ
  -- Arithmetic: `m (a+1)^2 ≤ 32 |S| k`.
  have harith : m * (a + 1) ^ 2 ≤ 32 * S.card * k := by
    have h1 : a * m ≤ S.card := Nat.div_mul_le_self _ _
    have h2 : S.card < 16 * m * (k + 1) :=
      Nat.lt_mul_div_succ _ (by positivity)
    have h3 : a + 1 ≤ 16 * (k + 1) := by
      have : a * m < 16 * (k + 1) * m := by
        calc a * m ≤ S.card := h1
          _ < 16 * m * (k + 1) := h2
          _ = 16 * (k + 1) * m := by ring
      have := Nat.lt_of_mul_lt_mul_right this
      omega
    have h4 : 32 ≤ a := (Nat.le_div_iff_mul_le hm).2 (by linarith)
    have h5 : 2 ≤ k := (Nat.le_div_iff_mul_le (by positivity)).2 (by linarith)
    have h6 : (a + 1) * (k + 1) ≤ 2 * a * k := by nlinarith
    calc m * (a + 1) ^ 2 = m * (a + 1) * (a + 1) := by ring
      _ ≤ m * (a + 1) * (16 * (k + 1)) := Nat.mul_le_mul_left _ h3
      _ = 16 * m * ((a + 1) * (k + 1)) := by ring
      _ ≤ 16 * m * (2 * a * k) := Nat.mul_le_mul_left _ h6
      _ = 32 * (a * m) * k := by ring
      _ ≤ 32 * S.card * k := by
        apply Nat.mul_le_mul_right
        exact Nat.mul_le_mul_left _ h1
  have harithR : (m : ℝ) * ((a : ℝ) + 1) ^ 2 ≤ 32 * S.card * k := by
    exact_mod_cast harith
  have hM : (0 : ℝ) < ((a : ℝ) + 1) ^ 2 := by positivity
  have ht0 : (0 : ℝ) ≤ t := by positivity
  calc
    (2 : ℝ) * t ≤ (1 / ((a : ℝ) + 1) ^ 2) * ((S.card : ℝ) * ((k : ℝ) * (64 * t / m))) := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hM]
      have : (S.card : ℝ) * ((k : ℝ) * (64 * t / m)) =
          (32 * S.card * k) * (2 * t) / m := by
        field_simp
        ring
      rw [this, le_div_iff₀ hmpos]
      nlinarith [mul_le_mul_of_nonneg_right harithR (by positivity : (0 : ℝ) ≤ 2 * t)]
    _ ≤ (1 / ((a : ℝ) + 1) ^ 2) *
          ∑ i, ∑ x ∈ P i, ∑ x' ∈ P i, zmodNorm (χ * x - χ * x') ^ 2 :=
      mul_le_mul_of_nonneg_left henergy (by positivity)
    _ ≤ psi P χ := hpsi

/-- Lemma 3.2. -/
theorem lemma3_2 {p m t : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hm : 0 < m) (ht : 0 < t)
    (χ : ZMod p)
    (hχB : χ ∉ Bset S m (2000 * t)) :
    (200 : ℝ) * t / m * S.card ≤
      ∑ x ∈ S \ Jset S m t χ,
        zmodNorm (χ * x - centerAt S m t χ) ^ 2 := by
  classical
  set c := centerAt S m t χ with hc
  have hPsi : (2000 : ℝ) * t < Psi S m χ := by
    have hnot : ¬ (Psi S m χ ≤ ((2000 * t : ℕ) : ℝ)) := by
      intro h
      exact hχB (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
    push_cast at hnot
    linarith
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  have hSpos : (0 : ℝ) < S.card := by
    rcases Nat.eq_zero_or_pos S.card with h0 | hpos
    · exfalso
      have hS0 : S = ∅ := Finset.card_eq_zero.mp h0
      have : Psi S m χ = 0 := by simp [Psi, hS0]
      linarith
    · exact_mod_cast hpos
  have hpair : ∀ x x' : ZMod p,
      zmodNorm (χ * x - χ * x') ^ 2 ≤
        2 * zmodNorm (χ * x - c) ^ 2 + 2 * zmodNorm (χ * x' - c) ^ 2 := by
    intro x x'
    have h := fact2_3_general [χ * x - c, -(χ * x' - c)]
    simp only [List.sum_cons, List.sum_nil, add_zero, List.length_cons, List.length_nil,
      List.map_cons, List.map_nil, zmodNorm_neg] at h
    have he : χ * x - c + -(χ * x' - c) = χ * x - χ * x' := by ring
    rw [he] at h
    push_cast at h
    linarith
  set A := ∑ x ∈ S, zmodNorm (χ * x - c) ^ 2 with hA
  have hsum :
      ∑ x ∈ S, ∑ x' ∈ S, zmodNorm (χ * x - χ * x') ^ 2 ≤ 4 * S.card * A := by
    calc
      _ ≤ ∑ x ∈ S, ∑ x' ∈ S,
          (2 * zmodNorm (χ * x - c) ^ 2 + 2 * zmodNorm (χ * x' - c) ^ 2) := by
            gcongr with x hx x' hx'
            exact hpair x x'
      _ = 4 * S.card * A := by
            simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
              ← Finset.mul_sum, hA]
            ring
  have htotal : (500 : ℝ) * t / m * S.card < A := by
    have h1 : Psi S m χ ≤ (m : ℝ) / (S.card : ℝ) ^ 2 * (4 * S.card * A) := by
      unfold Psi
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    have h2 : (m : ℝ) / (S.card : ℝ) ^ 2 * (4 * S.card * A) = 4 * m * A / S.card := by
      field_simp
    rw [h2] at h1
    have h3 : (2000 : ℝ) * t < 4 * m * A / S.card := lt_of_lt_of_le hPsi h1
    rw [lt_div_iff₀ hSpos] at h3
    rw [div_mul_eq_mul_div, div_lt_iff₀ hmpos]
    nlinarith
  -- On `J_{χ,t}` each term is at most `(16√(t/m))² = 256t/m` (the paper prints
  -- `265t/m`, a typo).
  have hJ :
      ∑ x ∈ S ∩ Jset S m t χ, zmodNorm (χ * x - c) ^ 2 ≤
        (256 : ℝ) * t / m * S.card := by
    have hsq : (Real.sqrt ((t : ℝ) / m)) ^ 2 = (t : ℝ) / m :=
      Real.sq_sqrt (by positivity)
    calc
      _ ≤ ∑ _x ∈ S ∩ Jset S m t χ, (256 : ℝ) * t / m := by
            apply Finset.sum_le_sum
            intro x hx
            have hxJ := (Finset.mem_inter.1 hx).2
            have hdist := (Finset.mem_filter.1 hxJ).2
            have h16 : zmodNorm (χ * x - c) ^ 2 ≤
                (16 * Real.sqrt ((t : ℝ) / m)) ^ 2 :=
              pow_le_pow_left₀ (zmodNorm_nonneg _) hdist 2
            have : (16 * Real.sqrt ((t : ℝ) / m)) ^ 2 = 256 * t / m := by
              rw [mul_pow, hsq]; ring
            linarith
      _ = ((S ∩ Jset S m t χ).card : ℝ) * (256 * t / m) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (S.card : ℝ) * (256 * t / m) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact_mod_cast Finset.card_le_card Finset.inter_subset_left
      _ = (256 : ℝ) * t / m * S.card := by ring
  have hsplit := Finset.sum_inter_add_sum_sdiff S (Jset S m t χ)
    (fun x => zmodNorm (χ * x - c) ^ 2)
  rw [← hA] at hsplit
  have h244 : (500 : ℝ) * t / m * S.card - 256 * t / m * S.card =
      244 * t / m * S.card := by ring
  have h200 : (200 : ℝ) * t / m * S.card ≤ (244 : ℝ) * t / m * S.card := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply div_le_div_of_nonneg_right _ hmpos.le
    linarith
  linarith

/-- Deterministic implication used in Lemma 3.3.

As in `psi_ge_two_of_far_rows`, the floor in `|S|/(4m)` is absorbed by using the
sharp block-size bound `|S_i| ≤ ⌊|S|/m⌋ + 1` instead of (3.3). -/
theorem psi_ge_five_of_dense_rows {p m t : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hS : 2 ≤ S.card)
    (hm : 0 < m) (hm4 : m ≤ S.card / 4)
    {P : Fin m → Finset (ZMod p)} (hP : IsBalancedPartition S P)
    (χ : ZMod p) (hχD : χ ∈ Dset S m t)
    (hχB : χ ∉ Bset S m (2000 * t))
    (hrow : ∀ x ∈ S \ Jset S m t χ,
      S.card / (4 * m) ≤
        ((pointBlock S P x \ {x}) ∩
          nearSet S m t χ (centerAt S m t χ)).card) :
    (5 : ℝ) * t ≤ psi P χ := by
  classical
  rcases Nat.eq_zero_or_pos t with ht0 | ht
  · subst ht0
    simp only [Nat.cast_zero, mul_zero]
    unfold psi
    positivity
  have hmS : m ≤ S.card := le_trans hm4 (Nat.div_le_self _ _)
  set c := centerAt S m t χ with hc
  set G := nearSet S m t χ c with hG
  set U := S \ Jset S m t χ with hU
  set k : ℕ := S.card / (4 * m) with hk
  set a : ℕ := S.card / m with ha
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  have hL32 := lemma3_2 S hm ht χ hχB
  have hsq : (Real.sqrt ((t : ℝ) / m)) ^ 2 = (t : ℝ) / m :=
    Real.sq_sqrt (by positivity)
  -- A point outside `J` and a point of the dense interval are far apart.
  have hfar_near : ∀ x ∈ U, ∀ x' ∈ G,
      zmodNorm (χ * x - c) ^ 2 / 4 ≤ zmodNorm (χ * x - χ * x') ^ 2 := by
    intro x hx x' hx'
    have hxJ : x ∉ Jset S m t χ := (Finset.mem_sdiff.1 hx).2
    have hfar : 16 * Real.sqrt ((t : ℝ) / m) < zmodNorm (χ * x - c) := by
      by_contra hle
      exact hxJ (Finset.mem_filter.2 ⟨Finset.mem_univ _, le_of_not_gt hle⟩)
    have hnear : zmodNorm (χ * x' - c) ≤ 8 * Real.sqrt ((t : ℝ) / m) :=
      (Finset.mem_filter.1 hx').2
    have h := fact2_3_general [χ * x - χ * x', χ * x' - c]
    simp only [List.sum_cons, List.sum_nil, add_zero, List.length_cons, List.length_nil,
      List.map_cons, List.map_nil] at h
    have he : χ * x - χ * x' + (χ * x' - c) = χ * x - c := by ring
    rw [he] at h
    push_cast at h
    have hs0 : 0 ≤ Real.sqrt ((t : ℝ) / m) := Real.sqrt_nonneg _
    have hn0 := zmodNorm_nonneg (χ * x' - c)
    have h1 : zmodNorm (χ * x' - c) ^ 2 ≤ 64 * (t / m) := by
      have := pow_le_pow_left₀ hn0 hnear 2
      rw [mul_pow, hsq] at this
      linarith
    have h2 : 256 * (t / m) < zmodNorm (χ * x - c) ^ 2 := by
      have := pow_lt_pow_left₀ hfar (by positivity) (two_ne_zero)
      rw [mul_pow, hsq] at this
      linarith
    nlinarith
  -- Row lower bound.
  have henergy :
      (k : ℝ) * ∑ x ∈ U, zmodNorm (χ * x - c) ^ 2 / 4 ≤
        ∑ i, ∑ x ∈ P i, ∑ x' ∈ P i,
          zmodNorm (χ * x - χ * x') ^ 2 := by
    have hrows := Section3.partition_energy_lower_by_rows
      S P ⟨hP.1, hP.2.1, hP.2.2.1⟩
      (fun a b => zmodNorm (χ * a - χ * b) ^ 2)
      (fun x => if x ∈ U then (k : ℝ) * (zmodNorm (χ * x - c) ^ 2 / 4) else 0)
      (by
        intro i x hx
        by_cases hxU : x ∈ U
        · simp only [hxU, ↓reduceIte]
          have hxS : x ∈ S := hP.1 i hx
          have hidx : blockIndex S P x = i :=
            blockIndex_eq_of_mem S hm hP hxS hx
          have hcount := hrow x hxU
          have hblock : pointBlock S P x = P i := by
            unfold pointBlock
            rw [hidx]
          rw [hblock] at hcount
          set T := (P i \ {x}) ∩ G with hT
          have hTsub : T ⊆ P i := fun y hy =>
            (Finset.mem_sdiff.1 (Finset.mem_inter.1 hy).1).1
          calc
            (k : ℝ) * (zmodNorm (χ * x - c) ^ 2 / 4)
                ≤ (T.card : ℝ) * (zmodNorm (χ * x - c) ^ 2 / 4) := by
                  apply mul_le_mul_of_nonneg_right _ (by positivity)
                  exact_mod_cast hcount
            _ ≤ ∑ x' ∈ T, zmodNorm (χ * x - χ * x') ^ 2 := by
                  have := Finset.card_nsmul_le_sum T
                    (fun x' => zmodNorm (χ * x - χ * x') ^ 2)
                    (zmodNorm (χ * x - c) ^ 2 / 4)
                    (fun x' hx' => hfar_near x hxU x' (Finset.mem_inter.1 hx').2)
                  simpa [nsmul_eq_mul] using this
            _ ≤ ∑ x' ∈ P i, zmodNorm (χ * x - χ * x') ^ 2 :=
                  Finset.sum_le_sum_of_subset_of_nonneg hTsub
                    (fun _ _ _ => by positivity)
        · simp only [hxU, ↓reduceIte]
          positivity)
    have hUS : S ∩ U = U := Finset.inter_eq_right.2 Finset.sdiff_subset
    rw [Finset.sum_ite_mem, hUS, ← Finset.mul_sum] at hrows
    exact hrows
  have hpsi := psi_ge_energy_div_sq S hm hmS hP χ
  -- Arithmetic: `m (a+1)^2 ≤ 10 k |S|`.
  have harith : m * (a + 1) ^ 2 ≤ 10 * k * S.card := by
    have h1 : a * m ≤ S.card := Nat.div_mul_le_self _ _
    have h2 : S.card < 4 * m * (k + 1) :=
      Nat.lt_mul_div_succ _ (by positivity)
    have h3 : a + 1 ≤ 4 * (k + 1) := by
      have : a * m < 4 * (k + 1) * m := by
        calc a * m ≤ S.card := h1
          _ < 4 * m * (k + 1) := h2
          _ = 4 * (k + 1) * m := by ring
      have := Nat.lt_of_mul_lt_mul_right this
      omega
    have h4m : 4 * m ≤ S.card := by
      have := (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).1 hm4
      linarith
    have h4 : 4 ≤ a := (Nat.le_div_iff_mul_le hm).2 (by linarith)
    have h5 : 1 ≤ k := (Nat.le_div_iff_mul_le (by positivity)).2 (by linarith)
    have h6 : 4 * ((a + 1) * (k + 1)) ≤ 10 * a * k := by nlinarith
    calc m * (a + 1) ^ 2 = m * (a + 1) * (a + 1) := by ring
      _ ≤ m * (a + 1) * (4 * (k + 1)) := Nat.mul_le_mul_left _ h3
      _ = m * (4 * ((a + 1) * (k + 1))) := by ring
      _ ≤ m * (10 * a * k) := Nat.mul_le_mul_left _ h6
      _ = 10 * k * (a * m) := by ring
      _ ≤ 10 * k * S.card := Nat.mul_le_mul_left _ h1
  have harithR : (m : ℝ) * ((a : ℝ) + 1) ^ 2 ≤ 10 * k * S.card := by
    exact_mod_cast harith
  have hM : (0 : ℝ) < ((a : ℝ) + 1) ^ 2 := by positivity
  have hsumU : (200 : ℝ) * t / m * S.card / 4 ≤ ∑ x ∈ U, zmodNorm (χ * x - c) ^ 2 / 4 := by
    rw [← Finset.sum_div]
    exact div_le_div_of_nonneg_right hL32 (by norm_num)
  calc
    (5 : ℝ) * t ≤ (1 / ((a : ℝ) + 1) ^ 2) * ((k : ℝ) * ((200 : ℝ) * t / m * S.card / 4)) := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hM]
      have : (k : ℝ) * ((200 : ℝ) * t / m * S.card / 4) =
          (10 * k * S.card) * (5 * t) / m := by
        field_simp
        ring
      rw [this, le_div_iff₀ hmpos]
      nlinarith [mul_le_mul_of_nonneg_right harithR (by positivity : (0 : ℝ) ≤ 5 * t)]
    _ ≤ (1 / ((a : ℝ) + 1) ^ 2) * ((k : ℝ) * ∑ x ∈ U, zmodNorm (χ * x - c) ^ 2 / 4) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left hsumU (by positivity)
    _ ≤ (1 / ((a : ℝ) + 1) ^ 2) *
          ∑ i, ∑ x ∈ P i, ∑ x' ∈ P i, zmodNorm (χ * x - χ * x') ^ 2 :=
      mul_le_mul_of_nonneg_left henergy (by positivity)
    _ ≤ psi P χ := hpsi

/-- Lemma 3.1. -/
theorem lemma3_1 {p m t : ℕ} [NeZero p] (hp : p.Prime)
    (S : Finset (ZMod p)) (hS : 2 ≤ S.card)
    (hmLower : (2 ^ 24 : ℝ) * Real.log (S.card : ℝ) ≤ m)
    (hmUpper : (m : ℝ) ≤
      (1 / 1000 : ℝ) * S.card / Real.log (S.card : ℝ))
    (χ : ZMod p) (hχ0 : χ ≠ 0)
    (hχD : χ ∉ Dset S m t) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    partitionMass (m := m) S (fun P => psi P χ < 2 * t) ≤
      1 / (S.card : ℝ) ^ 9 := by
  obtain ⟨hm, hm4, _hbig⟩ :=
    section3_basic_bounds S.card m hS hmLower hmUpper
  have h500 := section3_card_ge_500m S.card m hS hmUpper
  have h32 : 32 * m ≤ S.card := by omega
  unfold partitionMass
  calc
    uniformMass (balancedPartitions S) (fun P => psi P χ < 2 * t)
      ≤ uniformMass (balancedPartitions S) (fun P => ∃ x' ∈ S,
          ((pointBlock S P x' \ {x'}) ∩ farSet S m t χ x').card <
            S.card / (16 * m)) := by
          apply uniformMass_mono_on
          intro P hPmem hψ
          have hP : IsBalancedPartition S P := by
            simpa [balancedPartitions] using hPmem
          by_contra hall
          have hrows : ∀ x' ∈ S, S.card / (16 * m) ≤
              ((pointBlock S P x' \ {x'}) ∩ farSet S m t χ x').card :=
            fun x' hx' => not_lt.mp (fun h => hall ⟨x', hx', h⟩)
          have hge := psi_ge_two_of_far_rows S hS hm hm4 h32 hP χ hrows
          linarith
    _ ≤ ∑ x' ∈ S, uniformMass (balancedPartitions S) (fun P =>
          ((pointBlock S P x' \ {x'}) ∩ farSet S m t χ x').card <
            S.card / (16 * m)) :=
          uniformMass_exists_le_sum (balancedPartitions S) S
            (fun x' P => ((pointBlock S P x' \ {x'}) ∩ farSet S m t χ x').card <
              S.card / (16 * m))
    _ ≤ ∑ _x' ∈ S, Real.exp (-(S.card : ℝ) / (64 * m)) := by
          apply Finset.sum_le_sum
          intro x' hx'
          have hfar := farSet_quarter (m := m) (t := t) (x' := x') S χ hχ0 hχD
          have hx'G : x' ∉ farSet S m t χ x' := by
            intro hmem
            have h := (Finset.mem_filter.1 hmem).2
            rw [sub_self, sec3_zmodNorm_zero] at h
            have : 0 ≤ Real.sqrt ((t : ℝ) / m) := Real.sqrt_nonneg _
            linarith
          exact Section3.block_sparse_tail S (farSet S m t χ x') x'
            hx' hx'G (Finset.filter_subset _ _) hfar hm hm4
    _ = (S.card : ℝ) * Real.exp (-(S.card : ℝ) / (64 * m)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 1 / (S.card : ℝ) ^ 9 :=
          section3_tail_nine S.card m hS hm hmUpper 64 (by norm_num) (by norm_num)

/-- Lemma 3.3. -/
theorem lemma3_3 {p m t : ℕ} [NeZero p] (hp : p.Prime)
    (S : Finset (ZMod p)) (hS : 2 ≤ S.card)
    (hmLower : (2 ^ 24 : ℝ) * Real.log (S.card : ℝ) ≤ m)
    (hmUpper : (m : ℝ) ≤
      (1 / 1000 : ℝ) * S.card / Real.log (S.card : ℝ))
    (ht : 0 < t) (χ : ZMod p)
    (hχD : χ ∈ Dset S m t)
    (hχB : χ ∉ Bset S m (2000 * t)) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    partitionMass (m := m) S (fun P => psi P χ < 2 * t) ≤
      1 / (S.card : ℝ) ^ 9 := by
  obtain ⟨hm, hm4, _hbig⟩ :=
    section3_basic_bounds S.card m hS hmLower hmUpper
  have hGdensity : 3 * S.card ≤
      4 * (nearSet S m t χ (centerAt S m t χ)).card :=
    centerAt_spec S m t ht hχD
  have htpos : (0 : ℝ) ≤ t := by positivity
  unfold partitionMass
  calc
    uniformMass (balancedPartitions S) (fun P => psi P χ < 2 * t)
      ≤ uniformMass (balancedPartitions S) (fun P => ∃ x ∈ S \ Jset S m t χ,
          ((pointBlock S P x \ {x}) ∩ nearSet S m t χ (centerAt S m t χ)).card <
            S.card / (4 * m)) := by
          apply uniformMass_mono_on
          intro P hPmem hψ
          have hP : IsBalancedPartition S P := by
            simpa [balancedPartitions] using hPmem
          by_contra hall
          have hrows : ∀ x ∈ S \ Jset S m t χ, S.card / (4 * m) ≤
              ((pointBlock S P x \ {x}) ∩
                nearSet S m t χ (centerAt S m t χ)).card :=
            fun x hx => not_lt.mp (fun h => hall ⟨x, hx, h⟩)
          have hge := psi_ge_five_of_dense_rows S hS hm hm4 hP χ hχD hχB hrows
          linarith
    _ ≤ ∑ x ∈ S \ Jset S m t χ, uniformMass (balancedPartitions S) (fun P =>
          ((pointBlock S P x \ {x}) ∩ nearSet S m t χ (centerAt S m t χ)).card <
            S.card / (4 * m)) :=
          uniformMass_exists_le_sum (balancedPartitions S) (S \ Jset S m t χ)
            (fun x P => ((pointBlock S P x \ {x}) ∩
              nearSet S m t χ (centerAt S m t χ)).card < S.card / (4 * m))
    _ ≤ ∑ _x ∈ S \ Jset S m t χ, Real.exp (-(S.card : ℝ) / (48 * m)) := by
          apply Finset.sum_le_sum
          intro x hx
          have hxS : x ∈ S := (Finset.mem_sdiff.1 hx).1
          have hxG : x ∉ nearSet S m t χ (centerAt S m t χ) := by
            intro hxG
            have hxJ := (Finset.mem_sdiff.1 hx).2
            have hnear := (Finset.mem_filter.1 hxG).2
            apply hxJ
            apply Finset.mem_filter.2
            refine ⟨Finset.mem_univ _, ?_⟩
            have : 0 ≤ Real.sqrt ((t : ℝ) / m) := Real.sqrt_nonneg _
            linarith
          exact Section3.block_dense_tail S
            (nearSet S m t χ (centerAt S m t χ)) x hxS hxG
            (Finset.filter_subset _ _) hGdensity hm hm4
    _ ≤ (S.card : ℝ) * Real.exp (-(S.card : ℝ) / (48 * m)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
          exact_mod_cast Finset.card_le_card Finset.sdiff_subset
    _ ≤ 1 / (S.card : ℝ) ^ 9 :=
          section3_tail_nine S.card m hS hm hmUpper 48 (by norm_num) (by norm_num)

/-- The low-energy set is symmetric and contains zero. -/
theorem Bset_zero_neg {p m t : ℕ} [NeZero p]
    (S : Finset (ZMod p)) :
    (0 : ZMod p) ∈ Bset S m t ∧
      ∀ χ ∈ Bset S m t, -χ ∈ Bset S m t := by
  constructor
  · simp only [Bset, Finset.mem_filter, Finset.mem_univ, true_and]
    unfold Psi
    simp only [zero_mul, sub_self, sec3_zmodNorm_zero]
    simp
  · intro χ hχ
    have hE : Psi S m (-χ) = Psi S m χ := by
      unfold Psi
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro x' _
      rw [show (-χ) * x - (-χ) * x' = -(χ * x - χ * x') by ring, zmodNorm_neg]
    simp only [Bset, Finset.mem_filter, Finset.mem_univ, true_and] at hχ ⊢
    rw [hE]
    exact hχ

/-- Lemma 3.5. -/
theorem lemma3_5 {p m t : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hS : S.Nonempty)
    (hm : 0 < m) (ht : 0 < t) :
    (9 : ℝ) / 10 * S.card ≤ (Qset S m t (10 * t / m)).card := by
  classical
  set B := Bset S m t with hBdef
  set Q := Qset S m t (10 * t / m) with hQdef
  set f : ZMod p → ZMod p → ℝ :=
    fun x y => ∑ χ ∈ B, zmodNorm (χ * x - χ * y) ^ 2 with hfdef
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  have hBpos : (0 : ℝ) < B.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨0, (Bset_zero_neg (m := m) (t := t) S).1⟩
  have hSpos : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  -- `E[X] ≤ |B| t/m` for `X(Y,Y') = ∑_{χ∈B} ‖χY-χY'‖²`.
  have hEX : uniformExpectation (S.product S) (fun q => f q.1 q.2) ≤
      (B.card : ℝ) * ((t : ℝ) / m) := by
    rw [Section3.pair_uniform_expectation S]
    have hswap :
        ∑ x ∈ S, ∑ y ∈ S, f x y =
          ∑ χ ∈ B, ∑ x ∈ S, ∑ y ∈ S, zmodNorm (χ * x - χ * y) ^ 2 := by
      calc
        ∑ x ∈ S, ∑ y ∈ S, f x y
            = ∑ x ∈ S, ∑ χ ∈ B, ∑ y ∈ S, zmodNorm (χ * x - χ * y) ^ 2 := by
              apply Finset.sum_congr rfl
              intro x _
              exact Finset.sum_comm
        _ = ∑ χ ∈ B, ∑ x ∈ S, ∑ y ∈ S, zmodNorm (χ * x - χ * y) ^ 2 :=
              Finset.sum_comm
    rw [hswap, Finset.mul_sum]
    calc
      ∑ χ ∈ B, 1 / (S.card : ℝ) ^ 2 *
          ∑ x ∈ S, ∑ y ∈ S, zmodNorm (χ * x - χ * y) ^ 2
          ≤ ∑ _χ ∈ B, (t : ℝ) / m := by
            apply Finset.sum_le_sum
            intro χ hχ
            have hPsi : Psi S m χ ≤ t :=
              (Finset.mem_filter.1 hχ).2
            unfold Psi at hPsi
            rw [le_div_iff₀ hmpos]
            calc
              (1 / (S.card : ℝ) ^ 2 *
                  ∑ x ∈ S, ∑ y ∈ S, zmodNorm (χ * x - χ * y) ^ 2) * m
                  = (m : ℝ) / (S.card : ℝ) ^ 2 *
                      ∑ x ∈ S, ∑ y ∈ S, zmodNorm (χ * x - χ * y) ^ 2 := by ring
              _ ≤ (t : ℝ) := hPsi
      _ = (B.card : ℝ) * ((t : ℝ) / m) := by
            rw [Finset.sum_const, nsmul_eq_mul]
  -- Markov: `P[X ≥ (10t/m)|B|] ≤ 1/10`.
  have ha : (0 : ℝ) < (10 * t / m) * B.card := by positivity
  have hmarkov :=
    Auxiliary.uniform_markov (S.product S) (fun q => f q.1 q.2)
      ((10 * t / m) * B.card)
      (by intro q _; exact Finset.sum_nonneg (fun χ _ => sq_nonneg _)) ha
  have hbad :
      uniformMass (S.product S) (fun q => ¬ (q.1 - q.2 ∈ Q)) ≤ 1 / 10 := by
    have hident :
        uniformMass (S.product S) (fun q => ¬ (q.1 - q.2 ∈ Q)) =
          uniformMass (S.product S) (fun q => (10 * t / m) * B.card ≤ f q.1 q.2) := by
      apply uniformMass_congr
      intro q _
      simp only [hQdef, Qset, Finset.mem_filter, Finset.mem_univ, true_and, not_lt, hfdef,
        ← hBdef]
      constructor
      · intro h
        refine le_of_le_of_eq h ?_
        apply Finset.sum_congr rfl
        intro χ _
        rw [mul_sub]
      · intro h
        refine le_of_le_of_eq h ?_
        apply Finset.sum_congr rfl
        intro χ _
        rw [mul_sub]
    rw [hident]
    refine le_trans hmarkov ?_
    rw [div_le_iff₀ ha]
    have : (B.card : ℝ) * ((t : ℝ) / m) = 1 / 10 * ((10 * t / m) * B.card) := by
      field_simp
    linarith
  have hgood :
      (9 : ℝ) / 10 ≤ uniformMass (S.product S) (fun q => q.1 - q.2 ∈ Q) := by
    have hcompl := uniformMass_compl_eq_one (S.product S) (hS.product hS)
      (fun q => q.1 - q.2 ∈ Q)
    linarith
  obtain ⟨y', hy'S, hyfiber⟩ :=
    Section3.exists_fiber_mass_ge_pair_mass S hS
      (fun y y' => y - y' ∈ Q)
  have hcardfiber :
      (9 : ℝ) / 10 * S.card ≤ (S.filter fun y => y - y' ∈ Q).card :=
    card_filter_ge_of_uniformMass_ge S hS _ _ (le_trans hgood hyfiber)
  have hinj :
      (S.filter fun y => y - y' ∈ Q).card ≤ Q.card := by
    apply Finset.card_le_card_of_injOn (fun y => y - y')
    · intro y hy
      exact (Finset.mem_filter.1 hy).2
    · intro a _ b _ hab
      exact sub_left_injective hab
  calc
    (9 : ℝ) / 10 * S.card ≤ (S.filter fun y => y - y' ∈ Q).card := hcardfiber
    _ ≤ Q.card := by exact_mod_cast hinj

theorem character_sum_real_of_neg_symmetric
    {p : ℕ} [NeZero p]
    (B : Finset (ZMod p))
    (hsymm : ∀ χ ∈ B, -χ ∈ B)
    (x : ZMod p) :
    ((∑ χ ∈ B, ZMod.stdAddChar (χ * x)) : ℂ).im = 0 := by
  have hconj :
      (starRingEnd ℂ) (∑ χ ∈ B, ZMod.stdAddChar (χ * x)) =
        ∑ χ ∈ B, ZMod.stdAddChar (χ * x) := by
    rw [map_sum]
    simp_rw [← AddChar.map_neg_eq_conj]
    apply Finset.sum_nbij' (fun χ => -χ) (fun χ => -χ)
    · intro a ha
      exact hsymm a ha
    · intro a ha
      exact hsymm a ha
    · intro a _
      exact neg_neg a
    · intro a _
      exact neg_neg a
    · intro a _
      rw [neg_mul]
  have him := congrArg Complex.im hconj
  rw [Complex.conj_im] at him
  linarith

theorem symmetric_character_square_sum
    {p : ℕ} (hp : p.Prime)
    (B : Finset (ZMod p))
    (hsymm : ∀ χ ∈ B, -χ ∈ B) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    ∑ x : ZMod p,
      ((∑ χ ∈ B, ZMod.stdAddChar (χ * x)).re) ^ 2 =
        (p : ℝ) * B.card := by
  let : NeZero p := ⟨hp.ne_zero⟩
  classical
  have hreal : ∀ x : ZMod p,
      ((∑ χ ∈ B, ZMod.stdAddChar (χ * x)) : ℂ).im = 0 :=
    character_sum_real_of_neg_symmetric B hsymm
  have hsq : ∀ x : ZMod p,
      ((∑ χ ∈ B, ZMod.stdAddChar (χ * x)).re) ^ 2 =
        ((∑ χ ∈ B, ZMod.stdAddChar (χ * x)) ^ 2).re := by
    intro x
    set z := ∑ χ ∈ B, ZMod.stdAddChar (χ * x) with hz
    rw [sq z, Complex.mul_re, hreal x]
    ring
  have hexpand :
      ∑ x : ZMod p, (∑ χ ∈ B, ZMod.stdAddChar (χ * x)) ^ 2 =
        (p : ℂ) * B.card := by
    calc
      ∑ x : ZMod p, (∑ χ ∈ B, ZMod.stdAddChar (χ * x)) ^ 2
          = ∑ x : ZMod p, ∑ χ ∈ B, ∑ χ' ∈ B,
              ZMod.stdAddChar (x * (χ + χ')) := by
            apply Finset.sum_congr rfl
            intro x _
            rw [pow_two, Finset.sum_mul_sum]
            apply Finset.sum_congr rfl
            intro χ _
            apply Finset.sum_congr rfl
            intro χ' _
            rw [← AddChar.map_add_eq_mul]
            ring_nf
      _ = ∑ χ ∈ B, ∑ χ' ∈ B, ∑ x : ZMod p,
              ZMod.stdAddChar (x * (χ + χ')) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro χ _
            rw [Finset.sum_comm]
      _ = ∑ χ ∈ B, ∑ χ' ∈ B, if χ + χ' = 0 then (p : ℂ) else 0 := by
            apply Finset.sum_congr rfl
            intro χ _
            apply Finset.sum_congr rfl
            intro χ' _
            exact Auxiliary.zmod_character_orthogonality (χ + χ')
      _ = ∑ _χ ∈ B, (p : ℂ) := by
            apply Finset.sum_congr rfl
            intro χ hχ
            rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const]
            have hfilter : B.filter (fun χ' => χ + χ' = 0) = {-χ} := by
              ext χ'
              simp only [Finset.mem_filter, Finset.mem_singleton]
              constructor
              · rintro ⟨_, h⟩
                exact eq_neg_of_add_eq_zero_right h
              · rintro rfl
                exact ⟨hsymm χ hχ, add_neg_cancel χ⟩
            rw [hfilter]
            simp
      _ = (p : ℂ) * B.card := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hre := congrArg Complex.re hexpand
  rw [Complex.re_sum] at hre
  simp_rw [hsq]
  rw [hre]
  simp

/-- Lemma 3.6. -/
theorem lemma3_6 {p m t : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    ((Qset S m t (1 / 200)).card : ℝ) ≤
      (5 : ℝ) / 4 * p / (Bset S m t).card := by
  let : NeZero p := ⟨hp.ne_zero⟩
  classical
  set B := Bset S m t with hBdef
  set Q := Qset S m t (1 / 200) with hQdef
  obtain ⟨hzero, hsymm⟩ := Bset_zero_neg (m := m) (t := t) S
  have horth := symmetric_character_square_sum hp B hsymm
  have hBpos : (0 : ℝ) < B.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨0, hzero⟩
  have hpoint : ∀ x ∈ Q,
      (4 : ℝ) / 5 * (B.card : ℝ) ^ 2 ≤
        ((∑ χ ∈ B, ZMod.stdAddChar (χ * x)).re) ^ 2 := by
    intro x hx
    have hQ : ∑ χ ∈ B, zmodNorm (χ * x) ^ 2 < 1 / 200 * B.card :=
      (Finset.mem_filter.1 hx).2
    have hcos : ∀ χ ∈ B,
        1 - 20 * zmodNorm (χ * x) ^ 2 ≤ (ZMod.stdAddChar (χ * x)).re := by
      intro χ _
      rw [stdAddChar_re_eq_cos]
      exact (fact2_2 _).1
    have hre : (9 : ℝ) / 10 * B.card ≤
        (∑ χ ∈ B, ZMod.stdAddChar (χ * x)).re := by
      rw [Complex.re_sum]
      calc
        (9 : ℝ) / 10 * B.card
            ≤ ∑ χ ∈ B, (1 - 20 * zmodNorm (χ * x) ^ 2) := by
              rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
                ← Finset.mul_sum]
              linarith
        _ ≤ ∑ χ ∈ B, (ZMod.stdAddChar (χ * x)).re := Finset.sum_le_sum hcos
    have h0 : (0 : ℝ) ≤ 9 / 10 * B.card := by positivity
    have := pow_le_pow_left₀ h0 hre 2
    nlinarith
  have hsum :
      (Q.card : ℝ) * ((4 : ℝ) / 5 * (B.card : ℝ) ^ 2) ≤ p * B.card := by
    calc
      (Q.card : ℝ) * ((4 : ℝ) / 5 * (B.card : ℝ) ^ 2)
          ≤ ∑ x ∈ Q, ((∑ χ ∈ B, ZMod.stdAddChar (χ * x)).re) ^ 2 := by
            have := Finset.card_nsmul_le_sum Q
              (fun x => ((∑ χ ∈ B, ZMod.stdAddChar (χ * x)).re) ^ 2) _ hpoint
            simpa [nsmul_eq_mul] using this
      _ ≤ ∑ x : ZMod p, ((∑ χ ∈ B, ZMod.stdAddChar (χ * x)).re) ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun _ _ _ => sq_nonneg _)
      _ = p * B.card := horth
  rw [le_div_iff₀ hBpos]
  nlinarith

theorem Qset_mono_delta {p m t : ℕ} [NeZero p]
    (S : Finset (ZMod p)) {δ₁ δ₂ : ℝ} (hδ : δ₁ ≤ δ₂) :
    Qset S m t δ₁ ⊆ Qset S m t δ₂ := by
  intro x hx
  have hx' := (Finset.mem_filter.1 hx).2
  apply Finset.mem_filter.2
  refine ⟨Finset.mem_univ _, ?_⟩
  have hB : 0 ≤ ((Bset S m t).card : ℝ) := by positivity
  nlinarith

theorem finset_list_sum_comm {ι α : Type*} [DecidableEq ι]
    [AddCommMonoid α] (s : Finset ι) (xs : List α)
    (f : ι → α → α) :
    (∑ i ∈ s, (xs.map fun x => f i x).sum) =
      (xs.map fun x => ∑ i ∈ s, f i x).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp [ih, Finset.sum_add_distrib]

/-- Exchange a finite sum with a list sum (heterogeneous version). -/
theorem finset_sum_list_map_sum_comm {ι β α : Type*}
    [AddCommMonoid α] (s : Finset ι) (xs : List β)
    (f : ι → β → α) :
    (∑ i ∈ s, (xs.map fun x => f i x).sum) =
      (xs.map fun x => ∑ i ∈ s, f i x).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp [ih, Finset.sum_add_distrib]

/-- A list sum of terms each below `c` is below `length * c` when the list is nonempty. -/
theorem list_map_sum_lt_length_mul {α : Type*} (g : α → ℝ) (c : ℝ) :
    ∀ xs : List α, xs ≠ [] → (∀ y ∈ xs, g y < c) →
      (xs.map g).sum < (xs.length : ℝ) * c
  | [], h, _ => absurd rfl h
  | [y], _, hy => by
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
        List.length_cons, List.length_nil]
      have := hy y (by simp)
      push_cast
      linarith
  | y :: z :: zs, _, hy => by
      have ih := list_map_sum_lt_length_mul g c (z :: zs) (by simp)
        (fun w hw => hy w (List.mem_cons_of_mem y hw))
      have h0 := hy y (by simp)
      rw [List.map_cons, List.sum_cons, List.length_cons]
      push_cast
      linarith

/-- Lemma 3.7. -/
theorem lemma3_7 {p m t k : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (δ : ℝ)
    (hk : 0 < k) :
    kfoldSumset (Qset S m t δ) k ⊆
      Qset S m t ((k : ℝ) ^ 2 * δ) := by
  classical
  intro x hx
  obtain ⟨xs, hlen, hmem, rfl⟩ := (mem_kfoldSumset (Qset S m t δ) x).1 hx
  simp only [Qset, Finset.mem_filter, Finset.mem_univ, true_and]
  have hχ : ∀ χ ∈ Bset S m t,
      zmodNorm (χ * xs.sum) ^ 2 ≤
        (k : ℝ) * (xs.map fun y => zmodNorm (χ * y) ^ 2).sum := by
    intro χ _
    have hsum : (xs.map fun y => χ * y).sum = χ * xs.sum := by
      have := List.sum_map_mul_left xs (fun y => y) χ
      simpa using this
    have h := fact2_3_general (xs.map fun y => χ * y)
    rw [hsum, List.length_map, hlen, List.map_map] at h
    exact h
  have hne : xs ≠ [] := by
    intro h
    rw [h] at hlen
    simp at hlen
    omega
  have hy : ∀ y ∈ xs,
      ∑ χ ∈ Bset S m t, zmodNorm (χ * y) ^ 2 < δ * (Bset S m t).card := by
    intro y hy
    exact (Finset.mem_filter.1 (hmem y hy)).2
  have hlist := list_map_sum_lt_length_mul
    (fun y => ∑ χ ∈ Bset S m t, zmodNorm (χ * y) ^ 2)
    (δ * (Bset S m t).card) xs hne hy
  rw [hlen] at hlist
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  calc
    ∑ χ ∈ Bset S m t, zmodNorm (χ * xs.sum) ^ 2
      ≤ ∑ χ ∈ Bset S m t,
          (k : ℝ) * (xs.map fun y => zmodNorm (χ * y) ^ 2).sum :=
        Finset.sum_le_sum hχ
    _ = (k : ℝ) *
        (xs.map fun y =>
          ∑ χ ∈ Bset S m t, zmodNorm (χ * y) ^ 2).sum := by
        rw [← Finset.mul_sum, finset_sum_list_map_sum_comm]
    _ < (k : ℝ) * ((k : ℝ) * (δ * (Bset S m t).card)) :=
        mul_lt_mul_of_pos_left hlist hkpos
    _ = (k : ℝ) ^ 2 * δ * (Bset S m t).card := by ring

/-- Lemma 3.4. -/
theorem lemma3_4 {p m t : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hSbig : 10 ^ 7 ≤ S.card)
    (hm : 0 < m) (ht : 0 < t) (htm : t ≤ m / 2000) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    ((Bset S m t).card : ℝ) ≤
      1 + 200 * p * Real.sqrt t /
        ((S.card : ℝ) * Real.sqrt m) := by
  let : NeZero p := ⟨hp.ne_zero⟩
  classical
  set B := Bset S m t with hBdef
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hSne : S.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le (by norm_num) hSbig)
  have hSpos : (0 : ℝ) < S.card := by exact_mod_cast hSne.card_pos
  have hSbigR : (10 ^ 7 : ℝ) ≤ S.card := by exact_mod_cast hSbig
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  have hsqrtm : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hmpos
  have hsqrtt : 0 < Real.sqrt (t : ℝ) := Real.sqrt_pos.2 htpos
  have hRHS0 : 0 ≤ 200 * p * Real.sqrt t / ((S.card : ℝ) * Real.sqrt m) := by
    positivity
  by_cases hsmall : B.card < 2
  · have : (B.card : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.mp hsmall
    linarith
  have hB2 : 2 ≤ B.card := not_lt.mp hsmall
  have hBreal : (2 : ℝ) ≤ B.card := by exact_mod_cast hB2
  have hBpos : (0 : ℝ) < B.card := by linarith
  -- Lemma 3.6 gives `|Q_{t,1/200}| < p`.
  have hQsmall := lemma3_6 (m := m) (t := t) hp S
  have hQltp : (Qset S m t (1 / 200)).card < p := by
    have h1 : (5 : ℝ) / 4 * p / B.card ≤ (5 : ℝ) / 4 * p / 2 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hBreal
    have : ((Qset S m t (1 / 200)).card : ℝ) < p := by
      have := le_trans hQsmall h1
      linarith
    exact_mod_cast this
  -- The choice `k = ⌊√(m/(2000t))⌋`.
  have h2000 : 2000 * t ≤ m := by
    have := (Nat.le_div_iff_mul_le (by norm_num : 0 < 2000)).1 htm
    linarith
  have h2000R : (2000 : ℝ) * t ≤ m := by exact_mod_cast h2000
  set x : ℝ := Real.sqrt ((m : ℝ) / (2000 * t)) with hxdef
  set k : ℕ := ⌊x⌋₊ with hkdef
  have hx1 : 1 ≤ x := by
    rw [hxdef, Real.one_le_sqrt]
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hk1 : 1 ≤ k := Nat.le_floor (by simpa using hx1)
  have hkR1 : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hkx : (k : ℝ) ≤ x := Nat.floor_le (by positivity)
  have hxk : x ≤ 2 * k := by
    have := Nat.lt_floor_add_one x
    linarith
  have hxsq : x ^ 2 = (m : ℝ) / (2000 * t) := Real.sq_sqrt (by positivity)
  have hkδ : (k : ℝ) ^ 2 * (10 * t / m) ≤ 1 / 200 := by
    have hk2 : (k : ℝ) ^ 2 ≤ (m : ℝ) / (2000 * t) := by
      rw [← hxsq]
      exact pow_le_pow_left₀ (by positivity) hkx 2
    calc (k : ℝ) ^ 2 * (10 * t / m) ≤ (m : ℝ) / (2000 * t) * (10 * t / m) :=
          mul_le_mul_of_nonneg_right hk2 (by positivity)
      _ = 1 / 200 := by field_simp; ring
  have hsub :
      kfoldSumset (Qset S m t (10 * t / m)) k ⊆ Qset S m t (1 / 200) := by
    intro y hy
    exact Qset_mono_delta S hkδ
      (lemma3_7 S (10 * t / m) (by omega) hy)
  have hproper :
      kfoldSumset (Qset S m t (10 * t / m)) k ≠ Finset.univ := by
    intro h
    have hcard := Finset.card_le_card hsub
    rw [h, Finset.card_univ, ZMod.card] at hcard
    omega
  -- Cauchy--Davenport and Lemma 3.5.
  have hCD := fact2_4 hp (Qset S m t (10 * t / m)) (by omega : 0 < k) hproper
  have hQlarge := lemma3_5 S hSne hm ht
  have hCDreal : (1 : ℝ) + k * (((Qset S m t (10 * t / m)).card : ℝ) - 1) ≤
      ((kfoldSumset (Qset S m t (10 * t / m)) k).card : ℝ) := by
    exact_mod_cast hCD
  have hsumcard : (4 : ℝ) / 5 * k * S.card ≤
      ((kfoldSumset (Qset S m t (10 * t / m)) k).card : ℝ) := by
    have h1 : (k : ℝ) * ((9 : ℝ) / 10 * S.card - 1) ≤
        k * (((Qset S m t (10 * t / m)).card : ℝ) - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith
  have hupper : ((kfoldSumset (Qset S m t (10 * t / m)) k).card : ℝ) ≤
      (Qset S m t (1 / 200)).card := by
    exact_mod_cast Finset.card_le_card hsub
  -- `|B| ≤ (25/16) p / (k |S|)`.
  have hB : (B.card : ℝ) * (k * S.card) ≤ 25 / 16 * p := by
    have h1 : (4 : ℝ) / 5 * k * S.card ≤ (5 : ℝ) / 4 * p / B.card :=
      le_trans hsumcard (le_trans hupper hQsmall)
    rw [le_div_iff₀ hBpos] at h1
    nlinarith
  -- `√m ≤ 90 k √t`.
  have hsqrt2000 : Real.sqrt (2000 : ℝ) ≤ 45 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hroot : Real.sqrt (m : ℝ) ≤ 90 * k * Real.sqrt t := by
    have hm_eq : (m : ℝ) = (m : ℝ) / (2000 * t) * (2000 * t) := by
      field_simp
    have hsq_m : Real.sqrt (m : ℝ) = x * (Real.sqrt 2000 * Real.sqrt t) := by
      conv_lhs => rw [hm_eq]
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num)]
    rw [hsq_m]
    have hx0 : 0 ≤ x := by positivity
    calc x * (Real.sqrt 2000 * Real.sqrt t) ≤ (2 * k) * (45 * Real.sqrt t) := by
          apply mul_le_mul hxk _ (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_right hsqrt2000 hsqrtt.le
      _ = 90 * k * Real.sqrt t := by ring
  have hfinal : (B.card : ℝ) ≤ 200 * p * Real.sqrt t / ((S.card : ℝ) * Real.sqrt m) := by
    rw [le_div_iff₀ (by positivity)]
    have hkS : (0 : ℝ) < k * S.card := by positivity
    -- B n √m ≤ B n 90 k √t = 90 √t (B k n) ≤ 90 √t (25/16) p ≤ 200 p √t
    calc (B.card : ℝ) * ((S.card : ℝ) * Real.sqrt m)
        ≤ (B.card : ℝ) * ((S.card : ℝ) * (90 * k * Real.sqrt t)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left hroot (by positivity)
      _ = 90 * Real.sqrt t * ((B.card : ℝ) * (k * S.card)) := by ring
      _ ≤ 90 * Real.sqrt t * (25 / 16 * p) :=
          mul_le_mul_of_nonneg_left hB (by positivity)
      _ ≤ 200 * p * Real.sqrt t := by nlinarith
  linarith

end

end GrahamRearrangement
