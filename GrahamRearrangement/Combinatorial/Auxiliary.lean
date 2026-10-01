module

public import GrahamRearrangement.Combinatorial.Definitions

@[expose] public section

open scoped BigOperators Pointwise

namespace GrahamRearrangement.Section4

/-!
# Finite sampling and tuple bookkeeping for Section 4

Everything in this file is proved from finite cardinalities.  No Section 4
argument is axiomatized.
-/

noncomputable section

/-- Cardinality of a filtered product, computed fibrewise over the first factor. -/
theorem card_filter_product_eq_sum {β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (A : Finset β) (B : Finset γ) (P : β × γ → Prop) [DecidablePred P] :
    ((A.product B).filter P).card = ∑ a ∈ A, (B.filter fun b => P (a, b)).card := by
  rw [Finset.card_filter, Finset.product_eq_sprod, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.card_filter]

def extendPairSpace {α : Type*} [DecidableEq α]
    (S : Finset α) (m : ℕ) : Finset (Finset α × α) :=
  ((S.powersetCard (m - 1)).product S).filter fun q => q.2 ∉ q.1

theorem mem_extendPairSpace {α : Type*} [DecidableEq α]
    {S : Finset α} {m : ℕ} {R : Finset α} {x : α} :
    (R,x) ∈ extendPairSpace S m ↔
      R ∈ S.powersetCard (m - 1) ∧ x ∈ S \ R := by
  unfold extendPairSpace
  rw [Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_sdiff]
  tauto

def extendPairMap {α : Type*} [DecidableEq α]
    (q : Finset α × α) : Finset α :=
  insert q.2 q.1

theorem extendPairMap_mem {α : Type*} [DecidableEq α]
    {S : Finset α} {m : ℕ} (hm : 0 < m)
    {q : Finset α × α} (hq : q ∈ extendPairSpace S m) :
    extendPairMap q ∈ S.powersetCard m := by
  obtain ⟨R, x⟩ := q
  rcases (mem_extendPairSpace.mp hq) with ⟨hR, hx⟩
  rcases Finset.mem_powersetCard.mp hR with ⟨hRS, hcard⟩
  rcases Finset.mem_sdiff.mp hx with ⟨hxS, hxR⟩
  apply Finset.mem_powersetCard.mpr
  constructor
  · exact Finset.insert_subset hxS hRS
  · rw [extendPairMap, Finset.card_insert_of_notMem hxR, hcard]
    omega

/-- Every m-subset has exactly m extension-pair representations. -/
theorem extendPair_fiber_card {α : Type*} [DecidableEq α]
    (S : Finset α) {m : ℕ}
    {T : Finset α} (hT : T ∈ S.powersetCard m) :
    ((extendPairSpace S m).filter fun q => extendPairMap q = T).card = m := by
  rcases Finset.mem_powersetCard.mp hT with ⟨hTS, hTcard⟩
  rw [← hTcard]
  apply Finset.card_nbij' Prod.snd (fun x => (T.erase x, x))
  · rintro ⟨R, x⟩ hq
    rw [Finset.mem_coe, Finset.mem_filter] at hq
    rw [Finset.mem_coe, ← hq.2]
    exact Finset.mem_insert_self x R
  · intro x hx
    rw [Finset.mem_coe] at hx
    rw [Finset.mem_coe, Finset.mem_filter, mem_extendPairSpace]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [Finset.mem_powersetCard]
      refine ⟨(Finset.erase_subset x T).trans hTS, ?_⟩
      rw [Finset.card_erase_of_mem hx, hTcard]
    · exact Finset.mem_sdiff.mpr ⟨hTS hx, Finset.notMem_erase x T⟩
    · exact Finset.insert_erase hx
  · rintro ⟨R, x⟩ hq
    rw [Finset.mem_coe, Finset.mem_filter] at hq
    have hxR : x ∉ R := (Finset.mem_sdiff.mp (mem_extendPairSpace.mp hq.1).2).2
    have hmap : insert x R = T := hq.2
    simp only
    rw [← hmap, Finset.erase_insert hxR]
  · intro x _
    rfl

theorem extendPair_event_card {α : Type*} [DecidableEq α]
    (S : Finset α) {m : ℕ} (hm : 0 < m)
    (E : Finset α → Prop) [DecidablePred E] :
    ((extendPairSpace S m).filter fun q => E (extendPairMap q)).card =
      m * ((S.powersetCard m).filter E).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := extendPairMap)
    (t := (S.powersetCard m).filter E)]
  · rw [Finset.sum_congr rfl (g := fun _ => m), Finset.sum_const, smul_eq_mul, mul_comm]
    intro T hT
    rw [Finset.mem_filter] at hT
    rw [Finset.filter_filter]
    rw [Finset.filter_congr (q := fun q => extendPairMap q = T)]
    · exact extendPair_fiber_card S hT.1
    · intro q _
      constructor
      · exact And.right
      · intro h
        exact ⟨h ▸ hT.2, h⟩
  · intro q hq
    rw [Finset.mem_coe, Finset.mem_filter] at hq ⊢
    exact ⟨extendPairMap_mem hm hq.1, hq.2⟩

theorem extendPairSpace_card {α : Type*} [DecidableEq α]
    (S : Finset α) {m : ℕ} (hm : 0 < m) :
    (extendPairSpace S m).card = m * (S.powersetCard m).card := by
  simpa using extendPair_event_card S hm (fun _ => True)

/-- The extension-pair events, counted by first choosing the (m-1)-subset. -/
theorem extendPair_event_card_eq_sum {α : Type*} [DecidableEq α]
    (S : Finset α) (m : ℕ) (E : Finset α → Prop) [DecidablePred E] :
    ((extendPairSpace S m).filter fun q => E (extendPairMap q)).card =
      ∑ R ∈ S.powersetCard (m - 1), ((S \ R).filter fun x => E (insert x R)).card := by
  unfold extendPairSpace
  rw [Finset.filter_filter, card_filter_product_eq_sum]
  apply Finset.sum_congr rfl
  intro R _
  congr 1
  ext x
  rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_sdiff]
  simp only [extendPairMap]
  tauto

/-- A uniform m-subset can be sampled by first taking a uniform (m-1)-subset
and then one uniform point of its complement. -/
theorem uniformSubset_twoStage {α : Type*} [DecidableEq α]
    (S : Finset α) (m : ℕ) (hm : 0 < m) (hmS : m ≤ S.card)
    (E : Finset α → Prop) [DecidablePred E] :
    uniformMass (S.powersetCard m) E =
      uniformExpectation (S.powersetCard (m - 1))
        (fun R =>
          uniformMass (S \ R) (fun x => E (insert x R))) := by
  have hsum := extendPair_event_card_eq_sum S m E
  rw [extendPair_event_card S hm E] at hsum
  unfold uniformMass uniformExpectation
  have hcard : ∀ R ∈ S.powersetCard (m - 1),
      ((S \ R).card : ℝ) = ((S.card - m + 1 : ℕ) : ℝ) := by
    intro R hR
    rw [Finset.mem_powersetCard] at hR
    rw [Finset.card_sdiff_of_subset hR.1, hR.2]
    congr 1
    omega
  have hsum' : ∑ R ∈ S.powersetCard (m - 1),
      (((S \ R).filter fun x => E (insert x R)).card : ℝ) / ((S \ R).card : ℝ) =
      ∑ R ∈ S.powersetCard (m - 1),
        (((S \ R).filter fun x => E (insert x R)).card : ℝ) / ((S.card - m + 1 : ℕ) : ℝ) :=
    Finset.sum_congr rfl (fun R hR => by rw [hcard R hR])
  rw [hsum', ← Finset.sum_div, ← Nat.cast_sum, ← hsum, Finset.card_powersetCard,
    Finset.card_powersetCard]
  have hchoose : (S.card.choose m) * m =
      (S.card.choose (m - 1)) * (S.card - m + 1) := by
    have := Nat.choose_succ_right_eq S.card (m - 1)
    rwa [Nat.sub_add_cancel hm, show S.card - (m - 1) = S.card - m + 1 by omega] at this
  have hchooseR : ((S.card.choose m : ℕ) : ℝ) * (m : ℝ) =
      ((S.card.choose (m - 1) : ℕ) : ℝ) * ((S.card - m + 1 : ℕ) : ℝ) := by
    exact_mod_cast hchoose
  have hpos1 : (0 : ℝ) < (S.card.choose m : ℕ) := by exact_mod_cast Nat.choose_pos hmS
  have hpos2 : (0 : ℝ) < ((S.card - m + 1 : ℕ) : ℝ) := by positivity
  have hpos3 : (0 : ℝ) < (S.card.choose (m - 1) : ℕ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [div_div, Nat.cast_mul, mul_comm (((S.card - m + 1 : ℕ) : ℝ)), ← hchooseR]
  field_simp

def splitPairSpace {α : Type*} [DecidableEq α]
    (S : Finset α) (m₁ m₂ : ℕ) :
    Finset (Finset α × Finset α) :=
  ((S.powersetCard m₁).product (S.powersetCard m₂)).filter
    fun q => Disjoint q.1 q.2

def splitPairMap {α : Type*} [DecidableEq α]
    (q : Finset α × Finset α) : Finset α :=
  q.1 ∪ q.2

theorem splitPairMap_mem {α : Type*} [DecidableEq α]
    {S : Finset α} {m₁ m₂ : ℕ}
    {q : Finset α × Finset α}
    (hq : q ∈ splitPairSpace S m₁ m₂) :
    splitPairMap q ∈ S.powersetCard (m₁ + m₂) := by
  rcases Finset.mem_filter.mp hq with ⟨hqmem, hdisj⟩
  rcases Finset.mem_product.mp hqmem with ⟨h1,h2⟩
  rcases Finset.mem_powersetCard.mp h1 with ⟨h1S,hc1⟩
  rcases Finset.mem_powersetCard.mp h2 with ⟨h2S,hc2⟩
  apply Finset.mem_powersetCard.mpr
  constructor
  · exact Finset.union_subset h1S h2S
  · rw [splitPairMap, Finset.card_union_of_disjoint hdisj, hc1, hc2]

/-- A fixed (m₁+m₂)-subset has choose(m₁+m₂,m₁) ordered disjoint decompositions. -/
theorem splitPair_fiber_card {α : Type*} [DecidableEq α]
    (S : Finset α) (m₁ m₂ : ℕ)
    {T : Finset α} (hT : T ∈ S.powersetCard (m₁ + m₂)) :
    ((splitPairSpace S m₁ m₂).filter
      fun q => splitPairMap q = T).card =
      Nat.choose (m₁ + m₂) m₁ := by
  rcases Finset.mem_powersetCard.mp hT with ⟨hTS, hTcard⟩
  rw [← hTcard, ← Finset.card_powersetCard]
  apply Finset.card_nbij' Prod.fst (fun R => (R, T \ R))
  · rintro ⟨R₁, R₂⟩ hq
    rw [Finset.mem_coe, Finset.mem_filter] at hq
    obtain ⟨hq, hmap⟩ := hq
    rcases Finset.mem_filter.mp hq with ⟨hqmem, _⟩
    rcases Finset.mem_product.mp hqmem with ⟨h1, _⟩
    rw [Finset.mem_coe, Finset.mem_powersetCard]
    refine ⟨?_, (Finset.mem_powersetCard.mp h1).2⟩
    rw [← hmap]
    exact Finset.subset_union_left
  · intro R hR
    rw [Finset.mem_coe, Finset.mem_powersetCard] at hR
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩, ?_⟩
    · exact Finset.mem_powersetCard.mpr ⟨hR.1.trans hTS, hR.2⟩
    · refine Finset.mem_powersetCard.mpr ⟨Finset.sdiff_subset.trans hTS, ?_⟩
      rw [Finset.card_sdiff_of_subset hR.1, hR.2, hTcard]
      omega
    · exact Finset.disjoint_sdiff
    · exact Finset.union_sdiff_of_subset hR.1
  · rintro ⟨R₁, R₂⟩ hq
    rw [Finset.mem_coe, Finset.mem_filter] at hq
    obtain ⟨hq, hmap⟩ := hq
    have hdisj : Disjoint R₁ R₂ := (Finset.mem_filter.mp hq).2
    have hmap' : R₁ ∪ R₂ = T := hmap
    simp only
    rw [← hmap', Finset.union_sdiff_cancel_left hdisj]
  · intro R _
    rfl

theorem splitPair_event_card {α : Type*} [DecidableEq α]
    (S : Finset α) (m₁ m₂ : ℕ)
    (E : Finset α → Prop) [DecidablePred E] :
    ((splitPairSpace S m₁ m₂).filter
      fun q => E (splitPairMap q)).card =
      Nat.choose (m₁ + m₂) m₁ *
        ((S.powersetCard (m₁ + m₂)).filter E).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := splitPairMap)
    (t := (S.powersetCard (m₁ + m₂)).filter E)]
  · rw [Finset.sum_congr rfl (g := fun _ => Nat.choose (m₁ + m₂) m₁), Finset.sum_const,
      smul_eq_mul, mul_comm]
    intro T hT
    rw [Finset.mem_filter] at hT
    rw [Finset.filter_filter]
    rw [Finset.filter_congr (q := fun q => splitPairMap q = T)]
    · exact splitPair_fiber_card S m₁ m₂ hT.1
    · intro q _
      constructor
      · exact And.right
      · intro h
        exact ⟨h ▸ hT.2, h⟩
  · intro q hq
    rw [Finset.mem_coe, Finset.mem_filter] at hq ⊢
    exact ⟨splitPairMap_mem hq.1, hq.2⟩

/-- The split-pair events, counted by first choosing the m₁-subset. -/
theorem splitPair_event_card_eq_sum {α : Type*} [DecidableEq α]
    (S : Finset α) (m₁ m₂ : ℕ) (E : Finset α → Prop) [DecidablePred E] :
    ((splitPairSpace S m₁ m₂).filter fun q => E (splitPairMap q)).card =
      ∑ R₁ ∈ S.powersetCard m₁,
        (((S \ R₁).powersetCard m₂).filter fun R₂ => E (R₁ ∪ R₂)).card := by
  unfold splitPairSpace
  rw [Finset.filter_filter, card_filter_product_eq_sum]
  apply Finset.sum_congr rfl
  intro R₁ _
  congr 1
  ext R₂
  rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_powersetCard,
    Finset.mem_powersetCard, Finset.subset_sdiff]
  simp only [splitPairMap]
  constructor
  · rintro ⟨⟨hS, hc⟩, hd, hE⟩
    exact ⟨⟨⟨hS, hd.symm⟩, hc⟩, hE⟩
  · rintro ⟨⟨⟨hS, hd⟩, hc⟩, hE⟩
    exact ⟨⟨hS, hc⟩, hd.symm, hE⟩

/-- A uniform (m₁+m₂)-subset can be sampled in two uniform stages. -/
theorem uniformSubset_split {α : Type*} [DecidableEq α]
    (S : Finset α) (m₁ m₂ : ℕ)
    (hle : m₁ + m₂ ≤ S.card)
    (E : Finset α → Prop) [DecidablePred E] :
    uniformMass (S.powersetCard (m₁ + m₂)) E =
      uniformExpectation (S.powersetCard m₁)
        (fun R₁ =>
          uniformMass ((S \ R₁).powersetCard m₂)
            (fun R₂ => E (R₁ ∪ R₂))) := by
  have hsum := splitPair_event_card_eq_sum S m₁ m₂ E
  rw [splitPair_event_card S m₁ m₂ E] at hsum
  unfold uniformMass uniformExpectation
  have hcard : ∀ R₁ ∈ S.powersetCard m₁,
      (((S \ R₁).powersetCard m₂).card : ℝ) =
        ((Nat.choose (S.card - m₁) m₂ : ℕ) : ℝ) := by
    intro R₁ hR₁
    rw [Finset.mem_powersetCard] at hR₁
    rw [Finset.card_powersetCard, Finset.card_sdiff_of_subset hR₁.1, hR₁.2]
  have hsum' : ∑ R₁ ∈ S.powersetCard m₁,
      ((((S \ R₁).powersetCard m₂).filter fun R₂ => E (R₁ ∪ R₂)).card : ℝ) /
        (((S \ R₁).powersetCard m₂).card : ℝ) =
      ∑ R₁ ∈ S.powersetCard m₁,
        ((((S \ R₁).powersetCard m₂).filter fun R₂ => E (R₁ ∪ R₂)).card : ℝ) /
          ((Nat.choose (S.card - m₁) m₂ : ℕ) : ℝ) :=
    Finset.sum_congr rfl (fun R₁ hR₁ => by rw [hcard R₁ hR₁])
  rw [hsum', ← Finset.sum_div, ← Nat.cast_sum, ← hsum, Finset.card_powersetCard,
    Finset.card_powersetCard]
  have hchoose := Nat.choose_mul (n := S.card) (k := m₁ + m₂) (s := m₁)
    (Nat.le_add_right m₁ m₂)
  rw [Nat.add_sub_cancel_left] at hchoose
  have hchooseR : ((S.card.choose (m₁ + m₂) : ℕ) : ℝ) * ((m₁ + m₂).choose m₁ : ℕ) =
      ((S.card.choose m₁ : ℕ) : ℝ) * (((S.card - m₁).choose m₂ : ℕ) : ℝ) := by
    exact_mod_cast hchoose
  have hpos1 : (0 : ℝ) < (S.card.choose (m₁ + m₂) : ℕ) := by
    exact_mod_cast Nat.choose_pos hle
  have hpos2 : (0 : ℝ) < ((m₁ + m₂).choose m₁ : ℕ) := by
    exact_mod_cast Nat.choose_pos (Nat.le_add_right m₁ m₂)
  have hpos3 : (0 : ℝ) < (S.card.choose m₁ : ℕ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hpos4 : (0 : ℝ) < ((S.card - m₁).choose m₂ : ℕ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  rw [div_div, Nat.cast_mul, mul_comm (((S.card - m₁).choose m₂ : ℕ) : ℝ), ← hchooseR]
  field_simp

/-- Pigeonhole for the k+1 consecutive gaps of an increasing size tuple. -/
theorem exists_large_chain_gap {k n : ℕ} (m : Fin k → ℕ)
    (hm : IsChainSizeTuple n m) :
    ∃ j : Fin (k + 1),
      (n : ℝ) / (k + 1 : ℝ) ≤ chainGap n m j := by
  by_contra h
  push Not at h
  have hsum : (∑ j : Fin (k + 1), (chainGap n m j : ℝ)) = n := by
    exact_mod_cast sum_chainGap m hm
  have hlt : (∑ j : Fin (k + 1), (chainGap n m j : ℝ)) <
      ∑ _j : Fin (k + 1), (n : ℝ) / (k + 1 : ℝ) :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun j _ => h j)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hsum] at hlt
  have hk : (0 : ℝ) < k + 1 := by positivity
  push_cast at hlt
  rw [mul_div_cancel₀ _ hk.ne'] at hlt
  exact lt_irrefl _ hlt

/-- The last entry of an increasing tuple (or `0` for the empty tuple) is below `n`
whenever `n > 0`. -/
theorem extendedSize_self_lt_of_mem {n h : ℕ} {m : Fin h → ℕ}
    (hm : m ∈ chainSizeTuples n h) (hn : 0 < n) :
    extendedSize n m h < n := by
  classical
  unfold chainSizeTuples at hm
  have hchain : IsChainSizeTuple n m := (Finset.mem_filter.mp hm).2
  unfold extendedSize
  by_cases h0 : h = 0
  · rw [dite_eq_left h0]
    exact hn
  · rw [dite_eq_right h0, dite_eq_left le_rfl]
    exact (hchain.2 _).2

/-- Equation (4.1)'s positive-kernel induction, proved by induction on h.
(The hypothesis `0 ≤ B` is needed: for `n = 0` the row condition is vacuous while
`prefixKernelSum 0 1 w = 0`.) -/
theorem prefixKernelSum_le_pow (n h : ℕ) (w : ℕ → ℝ) (B : ℝ)
    (hw : ∀ d, 0 ≤ w d)
    (hrow : ∀ a < n,
      (∑ d ∈ Finset.Icc 1 (n - a), w d) ≤ B)
    (hB : 0 ≤ B) :
    prefixKernelSum n h w ≤ B ^ h := by
  induction h with
  | zero =>
    simp only [prefixKernelSum, Finset.univ_eq_empty, Finset.prod_empty,
      Finset.sum_const, nsmul_eq_mul, mul_one, pow_zero]
    exact_mod_cast Finset.card_le_one_of_subsingleton _
  | succ h ih =>
    rw [prefixKernelSum_succ]
    calc
      ∑ m ∈ chainSizeTuples n h,
          (∏ i : Fin h, w (chainGap n m ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)) *
            ∑ d ∈ Finset.Icc 1 (n - extendedSize n m h - 1), w d
        ≤ ∑ m ∈ chainSizeTuples n h,
          (∏ i : Fin h, w (chainGap n m ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)) * B := by
          apply Finset.sum_le_sum
          intro m hm
          apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (fun i _ => hw _))
          rcases Nat.eq_zero_or_pos n with hn | hn
          · subst hn
            simp only [Nat.zero_sub, Finset.Icc_eq_empty_of_lt Nat.zero_lt_one,
              Finset.sum_empty]
            exact hB
          · have hlast := extendedSize_self_lt_of_mem hm hn
            calc
              ∑ d ∈ Finset.Icc 1 (n - extendedSize n m h - 1), w d
                ≤ ∑ d ∈ Finset.Icc 1 (n - extendedSize n m h), w d :=
                  Finset.sum_le_sum_of_subset_of_nonneg
                    (Finset.Icc_subset_Icc_right (by omega)) (fun d _ _ => hw d)
              _ ≤ B := hrow _ hlast
      _ = prefixKernelSum n h w * B := by
          rw [prefixKernelSum, Finset.sum_mul]
      _ ≤ B ^ h * B := mul_le_mul_of_nonneg_right ih hB
      _ = B ^ (h + 1) := (pow_succ B h).symm

/-- Omitted-gap factorization used after (4.1). -/
theorem omittedKernelSum_le_prefix_mul (n k : ℕ) (w : ℕ → ℝ)
    (hw : ∀ d, 0 ≤ w d) (j : Fin (k + 1)) :
    omittedKernelSum n k w j ≤
      prefixKernelSum n j.val w *
        prefixKernelSum n (k - j.val) w := by
  classical
  unfold omittedKernelSum prefixKernelSum
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  apply Finset.sum_le_sum_of_injOn
    (fun m => (leftPrefixTuple m j, reverseRightTuple n m j))
  · intro m hm m' hm' heq
    exact fullTuple_eq_of_left_reverseRight_eq m m' j hm hm' heq
  · intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨m, hm, rfl⟩ := hx
    exact Finset.mem_product.mpr ⟨leftPrefixTuple_mem hm j, reverseRightTuple_mem hm j⟩
  · intro m hm
    have hchain : IsChainSizeTuple n m := by
      unfold chainSizeTuples at hm
      exact (Finset.mem_filter.mp hm).2
    rw [omitted_product_split w m j hchain]
  · intro x _ _
    exact mul_nonneg (Finset.prod_nonneg (fun i _ => hw _))
      (Finset.prod_nonneg (fun i _ => hw _))

/-- `∑_{t=1}^{N} 1/√t ≤ 2√N`. -/
theorem sum_one_div_sqrt_le (N : ℕ) :
    (∑ t ∈ Finset.Icc 1 N, 1 / Real.sqrt (t : ℝ)) ≤ 2 * Real.sqrt (N : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have ha := Real.sqrt_nonneg (N : ℝ)
    have hb : 0 < Real.sqrt ((N + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
    have ha2 := Real.sq_sqrt (show (0 : ℝ) ≤ (N : ℝ) by positivity)
    have hb2 := Real.sq_sqrt (show (0 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) by positivity)
    push_cast at hb hb2 ⊢
    set a := Real.sqrt (N : ℝ)
    set b := Real.sqrt ((N : ℝ) + 1)
    have hstep : 1 / b ≤ 2 * b - 2 * a := by
      rw [div_le_iff₀ hb]
      nlinarith [sq_nonneg (a - b)]
    linarith

end

end GrahamRearrangement.Section4
