module

public import GrahamRearrangement.Combinatorial.Corollary14

@[expose] public section

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Corollary 4.2

A uniformly random chain `R₁ ⊆ ⋯ ⊆ Rₖ ⊆ S` with `|Rᵢ| = mᵢ` corresponds bijectively to
its increments `Rᵢ₊₁ \ Rᵢ` (`i = 0, …, k`, with `R₀ = ∅`, `Rₖ₊₁ = S`), i.e. to a uniformly
random ordered partition of `S` with block sizes `mᵢ₊₁ - mᵢ`. The chain event
`Σ(Rᵢ) = zᵢ` becomes `Σ(Δᵢ) = zᵢ₊₁ - zᵢ`. We drop the condition on one large block `j`
and expose the other blocks one at a time (in any order): conditional on the exposed
blocks, the next block is a uniformly random subset of the unexposed elements, which
still contain the block `j`, so Corollary 1.4 bounds each conditional probability.
-/

noncomputable section

/-! ### Bookkeeping for the extended size sequence `m₀ = 0, m₁, …, mₖ, mₖ₊₁ = n` -/

private theorem extendedSize_at_zero {k : ℕ} (n : ℕ) (m : Fin k → ℕ) :
    extendedSize n m 0 = 0 := by
  simp [extendedSize]

private theorem extendedSize_at_succ_lt {k : ℕ} (n : ℕ) (m : Fin k → ℕ)
    {i : ℕ} (hi : i < k) :
    extendedSize n m (i + 1) = m ⟨i, hi⟩ := by
  have h : i + 1 ≤ k := hi
  simp [extendedSize, h]

private theorem extendedSize_at_gt {k : ℕ} (n : ℕ) (m : Fin k → ℕ)
    {j : ℕ} (hj : k < j) :
    extendedSize n m j = n := by
  have h0 : j ≠ 0 := by omega
  have h1 : ¬ j ≤ k := by omega
  simp [extendedSize, h0, h1]

theorem chainGap_pos {k n : ℕ} (hk : 0 < k)
    (m : Fin k → ℕ) (hm : IsChainSizeTuple n m)
    (i : Fin (k + 1)) :
    0 < chainGap n m i := by
  obtain ⟨hmono, hrange⟩ := hm
  obtain ⟨i, hi⟩ := i
  unfold chainGap
  dsimp only
  rcases Nat.lt_or_ge i k with hik | hik
  · rw [extendedSize_at_succ_lt n m hik]
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · subst h0
      rw [extendedSize_at_zero]
      have := (hrange ⟨0, hik⟩).1
      omega
    · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      rw [extendedSize_at_succ_lt n m (by omega : i' < k)]
      have : m ⟨i', by omega⟩ < m ⟨i' + 1, hik⟩ :=
        hmono (Fin.mk_lt_mk.mpr (by omega))
      omega
  · have hik' : i = k := by omega
    rw [extendedSize_at_gt n m (by omega : k < i + 1)]
    have hprev : extendedSize n m i = m ⟨k - 1, by omega⟩ := by
      have h := extendedSize_at_succ_lt n m (show k - 1 < k by omega)
      rwa [show k - 1 + 1 = i by omega] at h
    rw [hprev]
    have := (hrange ⟨k - 1, by omega⟩).2
    omega

theorem chainFactor_nonneg {p n gap : ℕ} (C : ℝ)
    (hC : 0 ≤ C) :
    0 ≤ chainFactor p n C gap := by
  unfold chainFactor
  positivity

theorem chain_factor_from_cor14 {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hS : 2 ≤ S.card)
    (ε Cε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hCε : 0 < Cε)
    (hCor :
      ∀ (T : Finset (ZMod p)), 2 ≤ T.card →
      ∀ (r : ℕ), 0 < r →
        (r : ℝ) ≤ (1 - ε) * T.card →
        ∀ q : ZMod p,
          sliceMass T r q ≤
            1 / (p : ℝ) +
              Cε * Real.sqrt (Real.log (T.card : ℝ)) /
                ((T.card : ℝ) * Real.sqrt (r : ℝ)))
    (T : Finset (ZMod p)) (hTS : T ⊆ S)
    (hTlower : ε * S.card ≤ (T.card : ℝ))
    (r : ℕ) (hr : 0 < r)
    (hrfrac : (r : ℝ) ≤ (1 - ε) * T.card)
    (q : ZMod p) :
    let Ck := Cε / ε
    sliceMass T r q ≤ chainFactor p S.card Ck r := by
  intro Ck
  show sliceMass T r q ≤ chainFactor p S.card (Cε / ε) r
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hTpos : (0 : ℝ) < T.card := by
    have h1 : (0 : ℝ) < (1 - ε) * T.card := lt_of_lt_of_le (by linarith) hrfrac
    by_contra hcon
    have h2 : (T.card : ℝ) ≤ 0 := not_lt.mp hcon
    nlinarith
  have hT2 : 2 ≤ T.card := by
    have hlt : (r : ℝ) < T.card := by nlinarith
    have hlt' : r < T.card := by exact_mod_cast hlt
    omega
  have hbase := hCor T hT2 r hr hrfrac q
  have hcardTS : T.card ≤ S.card := Finset.card_le_card hTS
  have hSpos : (0 : ℝ) < S.card := by
    have : (2 : ℝ) ≤ S.card := by exact_mod_cast hS
    linarith
  have hlogT : Real.log T.card ≤ Real.log S.card :=
    Real.log_le_log hTpos (by exact_mod_cast hcardTS)
  have hsqrtlog : Real.sqrt (Real.log T.card) ≤ Real.sqrt (Real.log S.card) :=
    Real.sqrt_le_sqrt hlogT
  have hrroot : 0 < Real.sqrt r := Real.sqrt_pos.2 (by linarith)
  have key :
      Cε * Real.sqrt (Real.log T.card) / (T.card * Real.sqrt r) ≤
        Cε / ε * Real.sqrt (Real.log S.card) / (S.card * Real.sqrt r) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : Cε / ε * Real.sqrt (Real.log S.card) * (ε * S.card * Real.sqrt r) ≤
        Cε / ε * Real.sqrt (Real.log S.card) * (T.card * Real.sqrt r) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_right hTlower hrroot.le
    have h2 : Cε / ε * Real.sqrt (Real.log S.card) * (ε * S.card * Real.sqrt r) =
        Cε * Real.sqrt (Real.log S.card) * (S.card * Real.sqrt r) := by
      field_simp
    have h3 : Cε * Real.sqrt (Real.log T.card) * (S.card * Real.sqrt r) ≤
        Cε * Real.sqrt (Real.log S.card) * (S.card * Real.sqrt r) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hsqrtlog hCε.le
    linarith
  unfold chainFactor
  linarith

def incrementPartitionFamily {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (m : Fin k → ℕ) :
    Finset (Fin (k + 1) → Finset (ZMod p)) := by
  classical
  exact Finset.univ.filter fun Δ =>
    (∀ i, Δ i ⊆ S ∧ (Δ i).card = chainGap S.card m i) ∧
    (∀ i j, i ≠ j → Disjoint (Δ i) (Δ j)) ∧
    (∀ x, x ∈ S ↔ ∃ i, x ∈ Δ i)

/-- The chain `∅ = R₀ ⊆ R₁ ⊆ ⋯ ⊆ Rₖ ⊆ Rₖ₊₁ = S`, indexed by `0, …, k + 1`. -/
def extendedChain {p k : ℕ}
    (S : Finset (ZMod p))
    (R : Fin k → Finset (ZMod p)) (j : ℕ) : Finset (ZMod p) :=
  if h0 : j = 0 then ∅
  else if hj : j ≤ k then R ⟨j - 1, by omega⟩
  else S

def chainIncrements {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    (R : Fin k → Finset (ZMod p)) :
    Fin (k + 1) → Finset (ZMod p) :=
  fun i => extendedChain S R (i.val + 1) \ extendedChain S R i.val

def incrementsToChain {p k : ℕ} [NeZero p]
    (Δ : Fin (k + 1) → Finset (ZMod p)) :
    Fin k → Finset (ZMod p) :=
  fun i => (Finset.univ.filter fun j : Fin (k + 1) => j.val ≤ i.val).biUnion Δ

theorem chain_nested_from_mem {p k : ℕ} [NeZero p]
    {S : Finset (ZMod p)} {m : Fin k → ℕ}
    {R : Fin k → Finset (ZMod p)}
    (hR : R ∈ chainFamily S m) :
    ∀ i j, i ≤ j → R i ⊆ R j := by
  exact (Finset.mem_filter.mp hR).2.2

theorem chain_data_from_mem {p k : ℕ} [NeZero p]
    {S : Finset (ZMod p)} {m : Fin k → ℕ}
    {R : Fin k → Finset (ZMod p)}
    (hR : R ∈ chainFamily S m) :
    ∀ i, R i ⊆ S ∧ (R i).card = m i := by
  exact (Finset.mem_filter.mp hR).2.1

/-! ### Bookkeeping for the extended chain -/

private theorem extendedChain_at_zero {p k : ℕ} (S : Finset (ZMod p))
    (R : Fin k → Finset (ZMod p)) :
    extendedChain S R 0 = ∅ := by
  simp [extendedChain]

private theorem extendedChain_at_succ_lt {p k : ℕ} (S : Finset (ZMod p))
    (R : Fin k → Finset (ZMod p)) {i : ℕ} (hi : i < k) :
    extendedChain S R (i + 1) = R ⟨i, hi⟩ := by
  have h : i + 1 ≤ k := hi
  simp [extendedChain, h]

private theorem extendedChain_at_gt {p k : ℕ} (S : Finset (ZMod p))
    (R : Fin k → Finset (ZMod p)) {j : ℕ} (hj : k < j) :
    extendedChain S R j = S := by
  have h0 : j ≠ 0 := by omega
  have h1 : ¬ j ≤ k := by omega
  simp [extendedChain, h0, h1]

private theorem extendedChain_mono {p k : ℕ} [NeZero p]
    {S : Finset (ZMod p)} {m : Fin k → ℕ}
    {R : Fin k → Finset (ZMod p)} (hR : R ∈ chainFamily S m) :
    Monotone (extendedChain S R) := by
  have hdata := chain_data_from_mem hR
  have hnest := chain_nested_from_mem hR
  intro a b hab
  rcases Nat.eq_zero_or_pos a with h0 | ha
  · subst h0
    rw [extendedChain_at_zero]
    exact Finset.empty_subset _
  · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    rcases Nat.lt_or_ge a' k with ha' | ha'
    · rw [extendedChain_at_succ_lt S R ha']
      rcases Nat.lt_or_ge b (k + 1) with hb | hb
      · obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
        rw [extendedChain_at_succ_lt S R (by omega : b' < k)]
        exact hnest _ _ (Fin.mk_le_mk.mpr (by omega))
      · rw [extendedChain_at_gt S R (by omega : k < b)]
        exact (hdata _).1
    · rw [extendedChain_at_gt S R (by omega : k < a' + 1),
        extendedChain_at_gt S R (by omega : k < b)]

private theorem extendedChain_subset {p k : ℕ} [NeZero p]
    {S : Finset (ZMod p)} {m : Fin k → ℕ}
    {R : Fin k → Finset (ZMod p)} (hR : R ∈ chainFamily S m) (j : ℕ) :
    extendedChain S R j ⊆ S := by
  have hj : j ≤ max j k + 1 := by omega
  calc extendedChain S R j ⊆ extendedChain S R (max j k + 1) :=
        extendedChain_mono hR hj
    _ = S := extendedChain_at_gt S R (by omega)

private theorem card_extendedChain {p k : ℕ} [NeZero p]
    {S : Finset (ZMod p)} {m : Fin k → ℕ}
    {R : Fin k → Finset (ZMod p)} (hR : R ∈ chainFamily S m) (j : ℕ) :
    (extendedChain S R j).card = extendedSize S.card m j := by
  rcases Nat.eq_zero_or_pos j with h0 | hj
  · subst h0
    rw [extendedChain_at_zero, extendedSize_at_zero]
    rfl
  · rcases Nat.lt_or_ge j (k + 1) with hjk | hjk
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      rw [extendedChain_at_succ_lt S R (by omega : i < k),
        extendedSize_at_succ_lt S.card m (by omega : i < k)]
      exact (chain_data_from_mem hR _).2
    · rw [extendedChain_at_gt S R (by omega : k < j),
        extendedSize_at_gt S.card m (by omega : k < j)]

private theorem mem_chainIncrements {p k : ℕ} [NeZero p]
    {S : Finset (ZMod p)} {R : Fin k → Finset (ZMod p)}
    {i : Fin (k + 1)} {x : ZMod p} :
    x ∈ chainIncrements S R i ↔
      x ∈ extendedChain S R (i.val + 1) ∧ x ∉ extendedChain S R i.val :=
  Finset.mem_sdiff

/-- In an increasing sequence of finsets starting at `∅`, every element of the
`n`-th set enters at a unique earlier step. -/
private theorem mem_iff_exists_step {α : Type*} {E : ℕ → Finset α}
    (h0 : E 0 = ∅) (hmono : Monotone E) {x : α} {n : ℕ} :
    x ∈ E n ↔ ∃ j, j < n ∧ x ∈ E (j + 1) ∧ x ∉ E j := by
  classical
  constructor
  · intro hx
    have hex : ∃ t, x ∈ E t := ⟨n, hx⟩
    have ht : x ∈ E (Nat.find hex) := Nat.find_spec hex
    have htn : Nat.find hex ≤ n := Nat.find_min' hex hx
    have ht0 : Nat.find hex ≠ 0 := by
      intro h
      rw [h, h0] at ht
      simp at ht
    refine ⟨Nat.find hex - 1, by omega, ?_, ?_⟩
    · rwa [Nat.sub_add_cancel (Nat.pos_of_ne_zero ht0)]
    · exact Nat.find_min hex (by omega)
  · rintro ⟨j, hj, hx, -⟩
    exact hmono (by omega : j + 1 ≤ n) hx

theorem subsetSum_sdiff {p : ℕ} [NeZero p]
    {A B : Finset (ZMod p)} (hAB : A ⊆ B) :
    subsetSum (B \ A) = subsetSum B - subsetSum A := by
  unfold subsetSum
  exact eq_sub_of_add_eq (Finset.sum_sdiff hAB)

theorem chain_prefix_union_eq {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    {m : Fin k → ℕ} {R : Fin k → Finset (ZMod p)}
    (hR : R ∈ chainFamily S m) (i : Fin k) :
    (Finset.univ.filter fun j : Fin (k + 1) => j.val ≤ i.val).biUnion
      (chainIncrements S R) = R i := by
  ext x
  rw [Finset.mem_biUnion]
  have hRi : R i = extendedChain S R (i.val + 1) :=
    (extendedChain_at_succ_lt S R i.isLt).symm
  rw [hRi, mem_iff_exists_step (extendedChain_at_zero S R) (extendedChain_mono hR)]
  constructor
  · rintro ⟨a, ha, hx⟩
    rw [Finset.mem_filter] at ha
    rw [mem_chainIncrements] at hx
    exact ⟨a.val, by omega, hx⟩
  · rintro ⟨j, hj, hx⟩
    refine ⟨⟨j, by omega⟩, ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by simp only; omega⟩
    · rw [mem_chainIncrements]
      exact hx

theorem chain_all_increments_union_eq {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    {m : Fin k → ℕ} {R : Fin k → Finset (ZMod p)}
    (hR : R ∈ chainFamily S m) :
    Finset.univ.biUnion (chainIncrements S R) = S := by
  ext x
  rw [Finset.mem_biUnion]
  have hS : S = extendedChain S R (k + 1) :=
    (extendedChain_at_gt S R (Nat.lt_succ_self k)).symm
  conv_rhs => rw [hS]
  rw [mem_iff_exists_step (extendedChain_at_zero S R) (extendedChain_mono hR)]
  constructor
  · rintro ⟨a, -, hx⟩
    rw [mem_chainIncrements] at hx
    exact ⟨a.val, a.isLt, hx⟩
  · rintro ⟨j, hj, hx⟩
    refine ⟨⟨j, hj⟩, Finset.mem_univ _, ?_⟩
    rw [mem_chainIncrements]
    exact hx

theorem chain_increment_subset {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    {m : Fin k → ℕ} {R : Fin k → Finset (ZMod p)}
    (hR : R ∈ chainFamily S m)
    (i : Fin (k + 1)) :
    chainIncrements S R i ⊆ S :=
  Finset.sdiff_subset.trans (extendedChain_subset hR _)

theorem chain_increment_disjoint_of_lt {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    {m : Fin k → ℕ} {R : Fin k → Finset (ZMod p)}
    (hR : R ∈ chainFamily S m)
    {i j : Fin (k + 1)} (hij : i.val < j.val) :
    Disjoint (chainIncrements S R i) (chainIncrements S R j) := by
  rw [Finset.disjoint_left]
  intro x hxi hxj
  rw [mem_chainIncrements] at hxi hxj
  exact hxj.2 (extendedChain_mono hR (by omega : i.val + 1 ≤ j.val) hxi.1)

theorem chainIncrements_mem {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    (m : Fin k → ℕ) {R : Fin k → Finset (ZMod p)}
    (hR : R ∈ chainFamily S m) :
    chainIncrements S R ∈ incrementPartitionFamily S m := by
  unfold incrementPartitionFamily
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, fun i => ⟨chain_increment_subset S hR i, ?_⟩, ?_, ?_⟩
  · unfold chainIncrements chainGap
    rw [Finset.card_sdiff_of_subset (extendedChain_mono hR (Nat.le_succ _)),
      card_extendedChain hR, card_extendedChain hR]
  · intro i j hij
    rcases Nat.lt_or_gt_of_ne (fun h => hij (Fin.ext h)) with h | h
    · exact chain_increment_disjoint_of_lt S hR h
    · exact (chain_increment_disjoint_of_lt S hR h).symm
  · intro x
    have hU := chain_all_increments_union_eq S hR
    constructor
    · intro hx
      rw [← hU, Finset.mem_biUnion] at hx
      obtain ⟨a, -, ha⟩ := hx
      exact ⟨a, ha⟩
    · rintro ⟨a, ha⟩
      have hx := Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ a, ha⟩
      rwa [hU] at hx

def canonicalChain {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (m : Fin k → ℕ)
    (hm : IsChainSizeTuple S.card m) :
    Fin k → Finset (ZMod p) := by
  classical
  let e : Fin S.card ≃ {x // x ∈ S} :=
    Fintype.equivOfCardEq (by simp)
  exact fun i =>
    (finSegment S.card 0 (m i)
      (Nat.le_of_lt (hm.2 i).2)).image
      (fun j => (e j).1)

private theorem canonicalChain_mem_aux {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (m : Fin k → ℕ)
    (hm : IsChainSizeTuple S.card m) (e : Fin S.card ≃ {x // x ∈ S}) :
    (fun i => (finSegment S.card 0 (m i)
      (Nat.le_of_lt (hm.2 i).2)).image (fun j => (e j).1)) ∈ chainFamily S m := by
  unfold chainFamily
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, fun i => ⟨?_, ?_⟩, fun i j hij => ?_⟩
  · intro x hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hx
    exact (e j).2
  · rw [Finset.card_image_of_injective _ (fun a b h => e.injective (Subtype.ext h)),
      card_finSegment]
    simp
  · intro x hx
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx
    apply Finset.mem_image.mpr
    refine ⟨r, ?_, rfl⟩
    rw [mem_finSegment] at hr ⊢
    exact ⟨hr.1, lt_of_lt_of_le hr.2 (hm.1.monotone hij)⟩

theorem canonicalChain_mem {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (m : Fin k → ℕ)
    (hm : IsChainSizeTuple S.card m) :
    canonicalChain S m hm ∈ chainFamily S m :=
  canonicalChain_mem_aux S m hm _

theorem chainFamily_nonempty {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (m : Fin k → ℕ)
    (hm : IsChainSizeTuple S.card m) :
    (chainFamily S m).Nonempty :=
  ⟨canonicalChain S m hm, canonicalChain_mem S m hm⟩

theorem chain_eq_of_increments_eq {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    {m : Fin k → ℕ}
    {R R' : Fin k → Finset (ZMod p)}
    (hR : R ∈ chainFamily S m) (hR' : R' ∈ chainFamily S m)
    (hEq : chainIncrements S R = chainIncrements S R') :
    R = R' := by
  funext i
  rw [← chain_prefix_union_eq S hR i,
      ← chain_prefix_union_eq S hR' i]
  simp [hEq]

theorem increments_prefix_union_eq {p k : ℕ} [NeZero p]
        {Δ : Fin (k + 1) → Finset (ZMod p)}
    (i : Fin k) :
    incrementsToChain Δ i =
      (Finset.univ.filter fun j : Fin (k + 1) => j.val ≤ i.val).biUnion Δ := rfl

/-- The extended chain of `incrementsToChain Δ` consists of the prefix unions of `Δ`. -/
private theorem extendedChain_incrementsToChain {p k : ℕ} [NeZero p]
    {S : Finset (ZMod p)} {m : Fin k → ℕ}
    {Δ : Fin (k + 1) → Finset (ZMod p)}
    (hΔ : Δ ∈ incrementPartitionFamily S m) (n : ℕ) :
    extendedChain S (incrementsToChain Δ) n =
      (Finset.univ.filter fun j : Fin (k + 1) => j.val < n).biUnion Δ := by
  obtain ⟨-, -, -, hcover⟩ := Finset.mem_filter.mp hΔ
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0
    rw [extendedChain_at_zero]
    ext x
    simp
  · rcases Nat.lt_or_ge n (k + 1) with hnk | hnk
    · obtain ⟨i, rfl⟩ : ∃ i, n = i + 1 := ⟨n - 1, by omega⟩
      rw [extendedChain_at_succ_lt S _ (by omega : i < k)]
      ext x
      simp only [incrementsToChain, Finset.mem_biUnion, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · rintro ⟨j, hj, hx⟩
        exact ⟨j, by omega, hx⟩
      · rintro ⟨j, hj, hx⟩
        exact ⟨j, by omega, hx⟩
    · rw [extendedChain_at_gt S _ (by omega : k < n)]
      ext x
      rw [hcover x, Finset.mem_biUnion]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨i, by omega, hi⟩
      · rintro ⟨i, -, hi⟩
        exact ⟨i, hi⟩

theorem increments_chain_inverse {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (m : Fin k → ℕ)
    {Δ : Fin (k + 1) → Finset (ZMod p)}
    (hΔ : Δ ∈ incrementPartitionFamily S m) :
    chainIncrements S (incrementsToChain Δ) = Δ := by
  obtain ⟨-, -, hdisj, -⟩ := Finset.mem_filter.mp hΔ
  funext i
  ext x
  rw [mem_chainIncrements, extendedChain_incrementsToChain hΔ,
    extendedChain_incrementsToChain hΔ]
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
    not_exists, not_and]
  constructor
  · rintro ⟨⟨a, ha, hxa⟩, hnot⟩
    have hai : a = i := by
      rcases Nat.lt_or_ge a.val i.val with h | h
      · exact absurd hxa (hnot a h)
      · exact Fin.ext (by omega)
    rwa [← hai]
  · intro hx
    refine ⟨⟨i, by omega, hx⟩, fun b hb hxb => ?_⟩
    have hne : b ≠ i := fun h => by rw [h] at hb; omega
    exact Finset.disjoint_left.mp (hdisj b i hne) hxb hx

theorem incrementPartitionFamily_nonempty {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    (m : Fin k → ℕ) (hm : IsChainSizeTuple S.card m) :
    (incrementPartitionFamily S m).Nonempty := by
  let R := canonicalChain S m hm
  exact ⟨chainIncrements S R,
    chainIncrements_mem S m (canonicalChain_mem S m hm)⟩

/-- If an increment partition exists, then the extended sizes are monotone: the
truncated gaps add up to `|S|`, which forces every gap to be a genuine difference. -/
private theorem extendedSize_step_le_of_partition {p k : ℕ} [NeZero p]
    {S : Finset (ZMod p)} {m : Fin k → ℕ}
    {Δ : Fin (k + 1) → Finset (ZMod p)}
    (hΔ : Δ ∈ incrementPartitionFamily S m) {j : ℕ} (hj : j ≤ k) :
    extendedSize S.card m j ≤ extendedSize S.card m (j + 1) := by
  obtain ⟨-, hdata, hdisj, hcover⟩ := Finset.mem_filter.mp hΔ
  have hsumcard : ∑ i : Fin (k + 1), chainGap S.card m i = S.card := by
    have hU : Finset.univ.biUnion Δ = S := by
      ext x
      rw [Finset.mem_biUnion, hcover x]
      simp
    have hc := Finset.card_biUnion (s := Finset.univ) (t := Δ)
      (fun a _ b _ hab => hdisj a b hab)
    rw [hU] at hc
    calc ∑ i : Fin (k + 1), chainGap S.card m i = ∑ i : Fin (k + 1), (Δ i).card :=
          Finset.sum_congr rfl (fun i _ => ((hdata i).2).symm)
      _ = S.card := hc.symm
  have htel : ∑ i : Fin (k + 1),
      ((extendedSize S.card m (i.val + 1) : ℤ) - extendedSize S.card m i.val) = S.card := by
    rw [Fin.sum_univ_eq_sum_range
        (fun n => (extendedSize S.card m (n + 1) : ℤ) - extendedSize S.card m n) (k + 1),
      Finset.sum_range_sub (fun n => (extendedSize S.card m n : ℤ)),
      extendedSize_at_zero, extendedSize_at_gt S.card m (Nat.lt_succ_self k)]
    simp
  have hge : ∀ i : Fin (k + 1),
      0 ≤ (chainGap S.card m i : ℤ) -
        ((extendedSize S.card m (i.val + 1) : ℤ) - extendedSize S.card m i.val) := by
    intro i
    unfold chainGap
    omega
  have hsum0 : ∑ i : Fin (k + 1), ((chainGap S.card m i : ℤ) -
      ((extendedSize S.card m (i.val + 1) : ℤ) - extendedSize S.card m i.val)) = 0 := by
    rw [Finset.sum_sub_distrib, htel, ← Nat.cast_sum, hsumcard, sub_self]
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hge i)).mp hsum0
    ⟨j, by omega⟩ (Finset.mem_univ _)
  unfold chainGap at hzero
  simp only at hzero
  omega

theorem incrementsToChain_mem {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    (m : Fin k → ℕ)
    {Δ : Fin (k + 1) → Finset (ZMod p)}
    (hΔ : Δ ∈ incrementPartitionFamily S m) :
    incrementsToChain Δ ∈ chainFamily S m := by
  obtain ⟨-, hdata, hdisj, -⟩ := Finset.mem_filter.mp hΔ
  have hcard : ∀ n, n ≤ k + 1 →
      ((Finset.univ.filter fun j : Fin (k + 1) => j.val < n).biUnion Δ).card =
        extendedSize S.card m n := by
    intro n
    induction n with
    | zero =>
      intro _
      rw [extendedSize_at_zero]
      simp
    | succ n ih =>
      intro hn
      have hsplit : (Finset.univ.filter fun j : Fin (k + 1) => j.val < n + 1) =
          insert ⟨n, by omega⟩ (Finset.univ.filter fun j : Fin (k + 1) => j.val < n) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Fin.ext_iff]
        omega
      have hdisjn : Disjoint (Δ ⟨n, by omega⟩)
          ((Finset.univ.filter fun j : Fin (k + 1) => j.val < n).biUnion Δ) := by
        rw [Finset.disjoint_biUnion_right]
        intro j hj
        apply hdisj
        intro h
        rw [← h, Finset.mem_filter] at hj
        exact absurd hj.2 (by simp)
      rw [hsplit, Finset.biUnion_insert, Finset.card_union_of_disjoint hdisjn,
        ih (by omega), (hdata _).2]
      have hle := extendedSize_step_le_of_partition hΔ (j := n) (by omega)
      unfold chainGap
      simp only
      omega
  unfold chainFamily
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, fun i => ⟨?_, ?_⟩, fun i j hij => ?_⟩
  · intro x hx
    simp only [incrementsToChain, Finset.mem_biUnion, Finset.mem_filter] at hx
    obtain ⟨a, -, hxa⟩ := hx
    exact (hdata a).1 hxa
  · have h := hcard (i.val + 1) (by omega)
    rw [extendedSize_at_succ_lt S.card m i.isLt] at h
    rw [← h]
    have hfilt : (Finset.univ.filter fun j : Fin (k + 1) => j.val ≤ i.val) =
        Finset.univ.filter fun j : Fin (k + 1) => j.val < i.val + 1 := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    show ((Finset.univ.filter fun j : Fin (k + 1) => j.val ≤ i.val).biUnion Δ).card = _
    rw [hfilt]
  · intro x hx
    simp only [incrementsToChain, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨a, ha, hxa⟩ := hx
    exact ⟨a, le_trans ha (Fin.le_def.mp hij), hxa⟩

theorem chain_increment_bijection {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    (m : Fin k → ℕ) :
    (chainFamily S m).card = (incrementPartitionFamily S m).card := by
  classical
  apply Finset.card_bij
    (fun R _ => chainIncrements S R)
  · intro R hR
    exact chainIncrements_mem S m hR
  · intro R hR R' hR' hEq
    exact chain_eq_of_increments_eq S hR hR' hEq
  · intro Δ hΔ
    refine ⟨incrementsToChain Δ,
      incrementsToChain_mem S m hΔ, ?_⟩
    exact increments_chain_inverse S m hΔ

theorem subsetSum_union_of_disjoint {p : ℕ} [NeZero p]
    {A B : Finset (ZMod p)} (h : Disjoint A B) :
    subsetSum (A ∪ B) = subsetSum A + subsetSum B := by
  unfold subsetSum
  rw [Finset.sum_union h]

theorem subsetSum_biUnion_pairwise_disjoint
    {p ι : ℕ} [NeZero p]
    (I : Finset (Fin ι))
    (A : Fin ι → Finset (ZMod p))
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (A i) (A j)) :
    subsetSum (I.biUnion A) =
      ∑ i ∈ I, subsetSum (A i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [subsetSum]
  | @insert i I hi ih =>
      have hDI :
          Disjoint (A i) (I.biUnion A) := by
        rw [Finset.disjoint_biUnion_right]
        intro j hj
        exact hdisj i (by simp) j (by simp [hj])
          (by intro h; subst j; exact hi hj)
      rw [Finset.biUnion_insert, subsetSum_union_of_disjoint hDI,
        ih (by
          intro a ha b hb hab
          exact hdisj a (by simp [ha]) b (by simp [hb]) hab)]
      simp [hi]

theorem subsetSum_eq_sum_chain_increments {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    {m : Fin k → ℕ} {R : Fin k → Finset (ZMod p)}
    (hR : R ∈ chainFamily S m) (i : Fin k) :
    subsetSum (R i) =
      ∑ j ∈ Finset.univ.filter (fun j : Fin (k + 1) => j.val ≤ i.val),
        subsetSum (chainIncrements S R j) := by
  rw [← chain_prefix_union_eq S hR i]
  apply subsetSum_biUnion_pairwise_disjoint
  intro a ha b hb hab
  by_cases hlt : a.val < b.val
  · exact chain_increment_disjoint_of_lt S hR hlt
  · exact (chain_increment_disjoint_of_lt S hR (by omega)).symm

/-- The targets `0 = z₀, z₁, …, zₖ, zₖ₊₁ = Σ(S)`, indexed by `0, …, k + 1`. -/
def extendedTarget {p k : ℕ}
    (S : Finset (ZMod p)) (z : Fin k → ZMod p) (j : ℕ) : ZMod p :=
  if h0 : j = 0 then 0
  else if hj : j ≤ k then z ⟨j - 1, by omega⟩
  else subsetSum S

def chainGapTarget {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (z : Fin k → ZMod p)
    (i : Fin (k + 1)) : ZMod p :=
  extendedTarget S z (i.val + 1) - extendedTarget S z i.val

private theorem extendedTarget_at_zero {p k : ℕ} (S : Finset (ZMod p))
    (z : Fin k → ZMod p) :
    extendedTarget S z 0 = 0 := by
  simp [extendedTarget]

private theorem extendedTarget_at_succ_lt {p k : ℕ} (S : Finset (ZMod p))
    (z : Fin k → ZMod p) {i : ℕ} (hi : i < k) :
    extendedTarget S z (i + 1) = z ⟨i, hi⟩ := by
  have h : i + 1 ≤ k := hi
  simp [extendedTarget, h]

private theorem extendedTarget_at_gt {p k : ℕ} (S : Finset (ZMod p))
    (z : Fin k → ZMod p) {j : ℕ} (hj : k < j) :
    extendedTarget S z j = subsetSum S := by
  have h0 : j ≠ 0 := by omega
  have h1 : ¬ j ≤ k := by omega
  simp [extendedTarget, h0, h1]

/-- Reindex a sum over the indices `j ≤ i` of `Fin (k + 1)` as a sum over `range (i + 1)`. -/
private theorem sum_filter_le_eq_sum_range {M : Type*} [AddCommMonoid M] {k : ℕ}
    (f : ℕ → M) {i : ℕ} (hi : i < k + 1) :
    ∑ j ∈ Finset.univ.filter (fun j : Fin (k + 1) => j.val ≤ i), f j.val =
      ∑ n ∈ Finset.range (i + 1), f n := by
  have hmap : Finset.range (i + 1) =
      (Finset.univ.filter fun j : Fin (k + 1) => j.val ≤ i).map Fin.valEmbedding := by
    ext n
    simp only [Finset.mem_range, Finset.mem_map, Finset.mem_filter, Finset.mem_univ,
      true_and, Fin.valEmbedding_apply]
    constructor
    · intro hn
      exact ⟨⟨n, by omega⟩, by simp only; omega, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      omega
  rw [hmap, Finset.sum_map]
  rfl

theorem chainGapTarget_prefix_telescopes {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    (z : Fin k → ZMod p) (i : Fin k) :
    ∑ j ∈ Finset.univ.filter (fun j : Fin (k + 1) => j.val ≤ i.val),
      chainGapTarget S z j = z i := by
  have h := sum_filter_le_eq_sum_range (k := k)
    (fun n => extendedTarget S z (n + 1) - extendedTarget S z n) (i := i.val) (by omega)
  beta_reduce at h
  unfold chainGapTarget
  rw [h, Finset.sum_range_sub (fun n => extendedTarget S z n), extendedTarget_at_zero,
    sub_zero, extendedTarget_at_succ_lt S z i.isLt]

theorem chain_sum_event_iff_increment_targets {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    {m : Fin k → ℕ} (R : Fin k → Finset (ZMod p))
    (hR : R ∈ chainFamily S m)
    (z : Fin k → ZMod p) :
    (∀ i, subsetSum (R i) = z i) ↔
      ∀ i : Fin (k + 1),
        subsetSum (chainIncrements S R i) = chainGapTarget S z i := by
  constructor
  · intro hz
    have hall : ∀ n, subsetSum (extendedChain S R n) = extendedTarget S z n := by
      intro n
      rcases Nat.eq_zero_or_pos n with h0 | hn
      · subst h0
        rw [extendedChain_at_zero, extendedTarget_at_zero]
        simp [subsetSum]
      · rcases Nat.lt_or_ge n (k + 1) with hnk | hnk
        · obtain ⟨i, rfl⟩ : ∃ i, n = i + 1 := ⟨n - 1, by omega⟩
          rw [extendedChain_at_succ_lt S R (by omega : i < k),
            extendedTarget_at_succ_lt S z (by omega : i < k)]
          exact hz _
        · rw [extendedChain_at_gt S R (by omega : k < n),
            extendedTarget_at_gt S z (by omega : k < n)]
    intro i
    show subsetSum (extendedChain S R (i.val + 1) \ extendedChain S R i.val) =
      extendedTarget S z (i.val + 1) - extendedTarget S z i.val
    rw [subsetSum_sdiff (extendedChain_mono hR (Nat.le_succ _)), hall, hall]
  · intro hΔ i
    rw [subsetSum_eq_sum_chain_increments S hR i,
      Finset.sum_congr rfl (fun j _ => hΔ j)]
    exact chainGapTarget_prefix_telescopes S z i

def exposureOrder {k : ℕ} (j : Fin (k + 1)) :
    List (Fin (k + 1)) :=
  (List.ofFn fun i : Fin j.val => ⟨i.val,by omega⟩) ++
  (List.ofFn fun i : Fin (k - j.val) =>
    ⟨k - i.val,by omega⟩)

theorem exposureOrder_nodup {k : ℕ} (j : Fin (k + 1)) :
    (exposureOrder j).Nodup := by
  unfold exposureOrder
  rw [List.nodup_append]
  refine ⟨List.nodup_ofFn.mpr ?_, List.nodup_ofFn.mpr ?_, ?_⟩
  · intro a b h
    have h' := congrArg Fin.val h
    exact Fin.ext h'
  · intro a b h
    have h' := congrArg Fin.val h
    have ha := a.isLt
    have hb := b.isLt
    simp only at h'
    exact Fin.ext (by omega)
  · intro x hx y hy hxy
    rw [List.mem_ofFn] at hx hy
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    have h' := congrArg Fin.val hxy
    have ha := a.isLt
    have hb := b.isLt
    simp only at h'
    omega

theorem mem_exposureOrder_iff {k : ℕ} (j : Fin (k + 1))
    (i : Fin (k + 1)) :
    i ∈ exposureOrder j ↔ i ≠ j := by
  unfold exposureOrder
  rw [List.mem_append, List.mem_ofFn, List.mem_ofFn]
  constructor
  · rintro (⟨a, rfl⟩ | ⟨a, rfl⟩) h
    · have h' := congrArg Fin.val h
      have ha := a.isLt
      simp only at h'
      omega
    · have h' := congrArg Fin.val h
      have ha := a.isLt
      simp only at h'
      omega
  · intro hij
    rcases Nat.lt_or_gt_of_ne (fun h => hij (Fin.ext h)) with h | h
    · exact Or.inl ⟨⟨i.val, h⟩, Fin.ext rfl⟩
    · have hik := i.isLt
      exact Or.inr ⟨⟨k - i.val, by omega⟩, Fin.ext (by simp only; omega)⟩

def historyKey {p k : ℕ} [NeZero p]
    (L : Finset (Fin (k + 1)))
    (Δ : Fin (k + 1) → Finset (ZMod p)) :
    Fin (k + 1) → Option (Finset (ZMod p)) :=
  fun i => if i ∈ L then some (Δ i) else none

def exposedUnion {p k : ℕ} [NeZero p]
    (L : Finset (Fin (k + 1)))
    (Δ : Fin (k + 1) → Finset (ZMod p)) :
    Finset (ZMod p) :=
  L.biUnion Δ

def remainingAfter {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    (L : Finset (Fin (k + 1)))
    (Δ : Fin (k + 1) → Finset (ZMod p)) :
    Finset (ZMod p) :=
  S \ exposedUnion L Δ

theorem unexposed_component_subset_remaining {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (m : Fin k → ℕ)
    {Δ : Fin (k + 1) → Finset (ZMod p)}
    (hΔ : Δ ∈ incrementPartitionFamily S m)
    (L : Finset (Fin (k + 1))) {i : Fin (k + 1)}
    (hi : i ∉ L) :
    Δ i ⊆ remainingAfter S L Δ := by
  rcases Finset.mem_filter.mp hΔ with ⟨_,hdata,hdisj,_⟩
  intro x hxi
  apply Finset.mem_sdiff.mpr
  refine ⟨(hdata i).1 hxi,?_⟩
  intro hxU
  simp [exposedUnion] at hxU
  rcases hxU with ⟨j,hjL,hxj⟩
  exact Finset.disjoint_left.mp (hdisj i j (by
    intro h; subst j; exact hi hjL)) hxi hxj

theorem unexposed_component_card_le_remaining {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (m : Fin k → ℕ)
    {Δ : Fin (k + 1) → Finset (ZMod p)}
    (hΔ : Δ ∈ incrementPartitionFamily S m)
    (L : Finset (Fin (k + 1))) {i : Fin (k + 1)}
    (hi : i ∉ L) :
    chainGap S.card m i ≤ (remainingAfter S L Δ).card := by
  have hsub := unexposed_component_subset_remaining S m hΔ L hi
  have hcard := Finset.card_le_card hsub
  rw [(Finset.mem_filter.mp hΔ).2.1 i |>.2] at hcard
  exact hcard

def partitionPermMap {p k : ℕ} [NeZero p]
    (π : Equiv.Perm (ZMod p))
    (Δ : Fin (k + 1) → Finset (ZMod p)) :
    Fin (k + 1) → Finset (ZMod p) :=
  fun i => (Δ i).image π

theorem partitionPermMap_mem {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (m : Fin k → ℕ)
    (π : Equiv.Perm (ZMod p)) (hπS : S.image π = S)
    {Δ : Fin (k + 1) → Finset (ZMod p)}
    (hΔ : Δ ∈ incrementPartitionFamily S m) :
    partitionPermMap π Δ ∈ incrementPartitionFamily S m := by
  obtain ⟨-, hdata, hdisj, hcover⟩ := Finset.mem_filter.mp hΔ
  have hmapS : ∀ y ∈ S, π y ∈ S := by
    intro y hy
    rw [← hπS]
    exact Finset.mem_image_of_mem π hy
  unfold incrementPartitionFamily
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, fun i => ⟨?_, ?_⟩, fun i j hij => ?_, fun x => ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact hmapS y ((hdata i).1 hy)
  · show ((Δ i).image π).card = _
    rw [Finset.card_image_of_injective _ π.injective, (hdata i).2]
  · show Disjoint ((Δ i).image π) ((Δ j).image π)
    rw [Finset.disjoint_image π.injective]
    exact hdisj i j hij
  · constructor
    · intro hxS
      rw [← hπS] at hxS
      obtain ⟨y, hyS, rfl⟩ := Finset.mem_image.mp hxS
      obtain ⟨i, hyi⟩ := (hcover y).1 hyS
      exact ⟨i, Finset.mem_image_of_mem π hyi⟩
    · rintro ⟨i, hxi⟩
      obtain ⟨y, hyi, rfl⟩ := Finset.mem_image.mp hxi
      exact hmapS y ((hdata i).1 hyi)

theorem partitionPermMap_history_fixed {p k : ℕ} [NeZero p]
    (L : Finset (Fin (k + 1)))
    (π : Equiv.Perm (ZMod p))
    {Δ : Fin (k + 1) → Finset (ZMod p)}
    (hfix : ∀ x ∈ exposedUnion L Δ, π x = x) :
    historyKey L (partitionPermMap π Δ) = historyKey L Δ := by
  funext i
  unfold historyKey partitionPermMap
  split_ifs with hi
  · congr 1
    calc (Δ i).image π = (Δ i).image id :=
          Finset.image_congr (fun x hx => hfix x (Finset.mem_biUnion.mpr ⟨i, hi, hx⟩))
      _ = Δ i := Finset.image_id
  · rfl

theorem remaining_invariant_under_history
    {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    (L : Finset (Fin (k + 1)))
    {Δ Γ : Fin (k + 1) → Finset (ZMod p)}
    (hkey : historyKey L Δ = historyKey L Γ) :
    remainingAfter S L Δ = remainingAfter S L Γ := by
  unfold remainingAfter exposedUnion
  congr 1
  apply Finset.biUnion_congr rfl
  intro i hi
  have h := congrFun hkey i
  simp only [historyKey, hi, ↓reduceIte, Option.some.injEq] at h
  exact h

theorem history_component_eq {p k : ℕ} [NeZero p]
    (L : Finset (Fin (k + 1)))
    {Δ Γ : Fin (k + 1) → Finset (ZMod p)}
    (hkey : historyKey L Δ = historyKey L Γ)
    {i : Fin (k + 1)} (hi : i ∈ L) :
    Δ i = Γ i := by
  have h := congrFun hkey i
  simp [historyKey,hi] at h
  exact h

theorem exposedUnion_eq_of_history {p k : ℕ} [NeZero p]
    (L : Finset (Fin (k + 1)))
    {Δ Γ : Fin (k + 1) → Finset (ZMod p)}
    (hkey : historyKey L Δ = historyKey L Γ) :
    exposedUnion L Δ = exposedUnion L Γ := by
  unfold exposedUnion
  apply Finset.biUnion_congr rfl
  intro i hi
  exact history_component_eq L hkey hi

theorem exposed_subset_S {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (m : Fin k → ℕ)
    {Δ : Fin (k + 1) → Finset (ZMod p)}
    (hΔ : Δ ∈ incrementPartitionFamily S m)
    (L : Finset (Fin (k + 1))) :
    exposedUnion L Δ ⊆ S := by
  intro x hx
  simp [exposedUnion] at hx
  rcases hx with ⟨i,hiL,hxi⟩
  exact ((Finset.mem_filter.mp hΔ).2.1 i).1 hxi

theorem exposed_not_remaining {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    {Δ : Fin (k + 1) → Finset (ZMod p)}
    (L : Finset (Fin (k + 1)))
    {x : ZMod p} (hx : x ∈ exposedUnion L Δ) :
    x ∉ remainingAfter S L Δ := by
  intro hxrem
  exact (Finset.mem_sdiff.mp hxrem).2 hx

theorem perm_fix_exposed_of_fix_outside_remaining
    {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    (L : Finset (Fin (k + 1)))
    {Δ : Fin (k + 1) → Finset (ZMod p)}
    (π : Equiv.Perm (ZMod p))
    (hfix : ∀ x ∉ remainingAfter S L Δ, π x = x) :
    ∀ x ∈ exposedUnion L Δ, π x = x := by
  intro x hx
  exact hfix x (exposed_not_remaining S L hx)

theorem perm_fix_outside_S_of_fix_outside_remaining
    {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    (L : Finset (Fin (k + 1)))
    {Δ : Fin (k + 1) → Finset (ZMod p)}
    (π : Equiv.Perm (ZMod p))
    (hfix : ∀ x ∉ remainingAfter S L Δ, π x = x) :
    ∀ x ∉ S, π x = x := by
  intro x hxS
  apply hfix
  intro hxU
  exact hxS (Finset.mem_sdiff.mp hxU).1

theorem component_fiber_equipotent
    {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (m : Fin k → ℕ)
    (L : Finset (Fin (k + 1))) (i : Fin (k + 1))
    (H : Fin (k + 1) → Option (Finset (ZMod p)))
    (Δ₀ : Fin (k + 1) → Finset (ZMod p))
    (hH : historyKey L Δ₀ = H)
    (A B : Finset (ZMod p))
    (hA : A ∈ (remainingAfter S L Δ₀).powersetCard
      (chainGap S.card m i))
    (hB : B ∈ (remainingAfter S L Δ₀).powersetCard
      (chainGap S.card m i)) :
    ((incrementPartitionFamily S m).filter fun Δ =>
      historyKey L Δ = H ∧ Δ i = A).card =
    ((incrementPartitionFamily S m).filter fun Δ =>
      historyKey L Δ = H ∧ Δ i = B).card := by
  -- By symmetry it suffices to prove one inequality for arbitrary `A` and `B`.
  suffices key : ∀ A B : Finset (ZMod p),
      A ∈ (remainingAfter S L Δ₀).powersetCard (chainGap S.card m i) →
      B ∈ (remainingAfter S L Δ₀).powersetCard (chainGap S.card m i) →
      ((incrementPartitionFamily S m).filter fun Δ =>
        historyKey L Δ = H ∧ Δ i = A).card ≤
      ((incrementPartitionFamily S m).filter fun Δ =>
        historyKey L Δ = H ∧ Δ i = B).card from
    le_antisymm (key A B hA hB) (key B A hB hA)
  intro A B hA hB
  obtain ⟨hAU, hAcard⟩ := Finset.mem_powersetCard.mp hA
  obtain ⟨hBU, hBcard⟩ := Finset.mem_powersetCard.mp hB
  -- A permutation of the not-yet-exposed elements carrying `A` to `B`.
  obtain ⟨π, hπA, hπU, hπfix⟩ :=
    exists_perm_maps_finset (remainingAfter S L Δ₀) A B hAU hBU
      (hAcard.trans hBcard.symm)
  have hπS : S.image π = S := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      by_cases hxU : x ∈ remainingAfter S L Δ₀
      · have hπx : π x ∈ (remainingAfter S L Δ₀).image π :=
          Finset.mem_image_of_mem π hxU
        rw [hπU] at hπx
        exact (Finset.mem_sdiff.mp hπx).1
      · rw [hπfix x hxU]
        exact hx
    · rw [Finset.card_image_of_injective _ π.injective]
  apply Finset.card_le_card_of_injOn (partitionPermMap π)
  · intro Δ hΔ
    rw [Finset.mem_coe, Finset.mem_filter] at hΔ ⊢
    obtain ⟨hmem, hkey, hAi⟩ := hΔ
    refine ⟨partitionPermMap_mem S m π hπS hmem, ?_, ?_⟩
    · rw [partitionPermMap_history_fixed L π ?_]
      · exact hkey
      · intro x hx
        apply hπfix
        rw [exposedUnion_eq_of_history L (hkey.trans hH.symm)] at hx
        intro hxU
        exact (Finset.mem_sdiff.mp hxU).2 hx
    · show (Δ i).image π = B
      rw [hAi, hπA]
  · intro Δ _ Γ _ hEq
    funext r
    exact Finset.image_injective π.injective (congrFun hEq r)

/-- Cardinality form of the conditional uniformity of an unexposed increment. -/
private theorem increment_fiber_card_eq
    {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (m : Fin k → ℕ)
    (L : Finset (Fin (k + 1))) (i : Fin (k + 1))
    (hi : i ∉ L)
    (H : Fin (k + 1) → Option (Finset (ZMod p)))
    (Δ₀ : Fin (k + 1) → Finset (ZMod p))
    (hΔ₀ : Δ₀ ∈ incrementPartitionFamily S m)
    (hH : historyKey L Δ₀ = H)
    (q : ZMod p) :
    ((((incrementPartitionFamily S m).filter fun Δ => historyKey L Δ = H).filter
        fun Δ => subsetSum (Δ i) = q).card : ℝ) =
      sliceMass (remainingAfter S L Δ₀) (chainGap S.card m i) q *
        ((incrementPartitionFamily S m).filter fun Δ => historyKey L Δ = H).card := by
  have hmaps : ∀ Δ ∈ (incrementPartitionFamily S m).filter (fun Δ => historyKey L Δ = H),
      Δ i ∈ (remainingAfter S L Δ₀).powersetCard (chainGap S.card m i) := by
    intro Δ hΔ
    obtain ⟨hmem, hkey⟩ := Finset.mem_filter.mp hΔ
    rw [Finset.mem_powersetCard]
    refine ⟨?_, ((Finset.mem_filter.mp hmem).2.1 i).2⟩
    rw [remaining_invariant_under_history S L (hH.trans hkey.symm)]
    exact unexposed_component_subset_remaining S m hmem L hi
  have hΔ₀C : Δ₀ i ∈ (remainingAfter S L Δ₀).powersetCard (chainGap S.card m i) :=
    hmaps Δ₀ (Finset.mem_filter.mpr ⟨hΔ₀, hH⟩)
  have hfib : ∀ A ∈ (remainingAfter S L Δ₀).powersetCard (chainGap S.card m i),
      (((incrementPartitionFamily S m).filter fun Δ => historyKey L Δ = H).filter
        fun Δ => Δ i = A).card =
      ((incrementPartitionFamily S m).filter fun Δ =>
        historyKey L Δ = H ∧ Δ i = Δ₀ i).card := by
    intro A hA
    rw [Finset.filter_filter]
    exact component_fiber_equipotent S m L i H Δ₀ hH A (Δ₀ i) hA hΔ₀C
  have hcpos : 0 < ((incrementPartitionFamily S m).filter fun Δ =>
      historyKey L Δ = H ∧ Δ i = Δ₀ i).card :=
    Finset.card_pos.mpr ⟨Δ₀, Finset.mem_filter.mpr ⟨hΔ₀, hH, rfl⟩⟩
  have h1 : ((incrementPartitionFamily S m).filter fun Δ => historyKey L Δ = H).card =
      ((remainingAfter S L Δ₀).powersetCard (chainGap S.card m i)).card *
        ((incrementPartitionFamily S m).filter fun Δ =>
          historyKey L Δ = H ∧ Δ i = Δ₀ i).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun Δ => Δ i) (fun Δ hΔ => hmaps Δ hΔ),
      Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul]
  have hmaps' : ∀ Δ ∈ (((incrementPartitionFamily S m).filter
        fun Δ => historyKey L Δ = H).filter fun Δ => subsetSum (Δ i) = q),
      Δ i ∈ ((remainingAfter S L Δ₀).powersetCard (chainGap S.card m i)).filter
        fun A => subsetSum A = q := by
    intro Δ hΔ
    obtain ⟨hΔ1, hΔ2⟩ := Finset.mem_filter.mp hΔ
    exact Finset.mem_filter.mpr ⟨hmaps Δ hΔ1, hΔ2⟩
  have h2 : (((incrementPartitionFamily S m).filter fun Δ => historyKey L Δ = H).filter
        fun Δ => subsetSum (Δ i) = q).card =
      (((remainingAfter S L Δ₀).powersetCard (chainGap S.card m i)).filter
        fun A => subsetSum A = q).card *
        ((incrementPartitionFamily S m).filter fun Δ =>
          historyKey L Δ = H ∧ Δ i = Δ₀ i).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun Δ => Δ i) (fun Δ hΔ => hmaps' Δ hΔ)]
    rw [Finset.sum_congr rfl (g := fun _ => ((incrementPartitionFamily S m).filter
        fun Δ => historyKey L Δ = H ∧ Δ i = Δ₀ i).card), Finset.sum_const, smul_eq_mul]
    intro A hA
    obtain ⟨hAC, hAq⟩ := Finset.mem_filter.mp hA
    rw [← hfib A hAC]
    congr 1
    ext Δ
    simp only [Finset.mem_filter]
    constructor
    · intro h
      exact ⟨h.1.1, h.2⟩
    · intro h
      refine ⟨⟨h.1, ?_⟩, h.2⟩
      rw [h.2]
      exact hAq
  unfold sliceMass uniformMass
  rw [h1, h2]
  push_cast
  have hc : (((incrementPartitionFamily S m).filter fun Δ =>
      historyKey L Δ = H ∧ Δ i = Δ₀ i).card : ℝ) ≠ 0 := by
    exact_mod_cast hcpos.ne'
  have hC : (((remainingAfter S L Δ₀).powersetCard (chainGap S.card m i)).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr ⟨_, hΔ₀C⟩).ne'
  field_simp

theorem increment_conditional_uniform_given_history
    {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (m : Fin k → ℕ)
    (L : Finset (Fin (k + 1))) (i : Fin (k + 1))
    (hi : i ∉ L)
    (H : Fin (k + 1) → Option (Finset (ZMod p)))
    (Δ₀ : Fin (k + 1) → Finset (ZMod p))
    (hΔ₀ : Δ₀ ∈ incrementPartitionFamily S m)
    (hH : historyKey L Δ₀ = H)
    (q : ZMod p) :
    uniformConditionalMass (incrementPartitionFamily S m)
      (fun Δ => historyKey L Δ = H)
      (fun Δ => subsetSum (Δ i) = q) =
    sliceMass (remainingAfter S L Δ₀)
      (chainGap S.card m i) q := by
  have hpos : (0 : ℝ) <
      ((incrementPartitionFamily S m).filter fun Δ => historyKey L Δ = H).card := by
    exact_mod_cast Finset.card_pos.mpr ⟨Δ₀, Finset.mem_filter.mpr ⟨hΔ₀, hH⟩⟩
  unfold uniformConditionalMass uniformMass
  rw [increment_fiber_card_eq S m L i hi H Δ₀ hΔ₀ hH q]
  field_simp

def historySatisfies {p k : ℕ} [NeZero p]
    (L : Finset (Fin (k + 1)))
    (target : Fin (k + 1) → ZMod p)
    (H : Fin (k + 1) → Option (Finset (ZMod p))) : Prop :=
  ∀ i ∈ L, ∃ A, H i = some A ∧ subsetSum A = target i

theorem historySatisfies_key_iff {p k : ℕ} [NeZero p]
    (L : Finset (Fin (k + 1)))
    (target : Fin (k + 1) → ZMod p)
    (Δ : Fin (k + 1) → Finset (ZMod p)) :
    historySatisfies L target (historyKey L Δ) ↔
      ∀ i ∈ L, subsetSum (Δ i) = target i := by
  constructor
  · intro h i hi
    rcases h i hi with ⟨A,hA,hSum⟩
    simp [historyKey,hi] at hA
    simpa [hA] using hSum
  · intro h i hi
    exact ⟨Δ i, by simp [historyKey,hi], h i hi⟩

theorem two_unexposed_gaps_sum_le_remaining
    {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (m : Fin k → ℕ)
    {Δ : Fin (k + 1) → Finset (ZMod p)}
    (hΔ : Δ ∈ incrementPartitionFamily S m)
    (L : Finset (Fin (k + 1)))
    {i j : Fin (k + 1)} (hi : i ∉ L) (hj : j ∉ L)
    (hij : i ≠ j) :
    chainGap S.card m i + chainGap S.card m j ≤
      (remainingAfter S L Δ).card := by
  have hiSub := unexposed_component_subset_remaining S m hΔ L hi
  have hjSub := unexposed_component_subset_remaining S m hΔ L hj
  have hdisj := (Finset.mem_filter.mp hΔ).2.2.1 i j hij
  have hunion :
      Δ i ∪ Δ j ⊆ remainingAfter S L Δ :=
    Finset.union_subset hiSub hjSub
  have hcard := Finset.card_le_card hunion
  rw [Finset.card_union_of_disjoint hdisj,
      ((Finset.mem_filter.mp hΔ).2.1 i).2,
      ((Finset.mem_filter.mp hΔ).2.1 j).2] at hcard
  exact hcard

theorem remainingAfter_subset {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (L : Finset (Fin (k + 1)))
    (Δ : Fin (k + 1) → Finset (ZMod p)) :
    remainingAfter S L Δ ⊆ S :=
  Finset.sdiff_subset

/-- Summing a fiberwise bound over the fibers of a statistic. -/
private theorem card_filter_le_of_fiberwise {α β : Type*} [DecidableEq β]
    (G : Finset α) (key : α → β) (E : α → Prop) [DecidablePred E] (c : ℝ)
    (h : ∀ H ∈ G.image key,
      (((G.filter fun a => key a = H).filter E).card : ℝ) ≤
        c * (G.filter fun a => key a = H).card) :
    ((G.filter E).card : ℝ) ≤ c * G.card := by
  have hmaps : ∀ a ∈ G.filter E, key a ∈ G.image key :=
    fun a ha => Finset.mem_image_of_mem _ (Finset.mem_filter.mp ha).1
  have hmaps' : ∀ a ∈ G, key a ∈ G.image key :=
    fun a ha => Finset.mem_image_of_mem _ ha
  rw [Finset.card_eq_sum_card_fiberwise (fun a ha => hmaps a ha),
    Finset.card_eq_sum_card_fiberwise (fun a ha => hmaps' a ha)]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro H hH
  have hH' := h H hH
  rwa [Finset.filter_comm] at hH'

/-- One exposure step: conditioning on any event determined by the increments indexed
by `L`, the next increment `i ∉ L` attains a prescribed sum with probability at most
`b i`. -/
private theorem increment_step_card_bound {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (m : Fin k → ℕ)
    (j : Fin (k + 1)) (b : Fin (k + 1) → ℝ)
    (hstep :
      ∀ i : Fin (k + 1), i ≠ j →
        ∀ U : Finset (ZMod p), U ⊆ S →
          chainGap S.card m i + chainGap S.card m j ≤ U.card →
          ∀ q : ZMod p,
            sliceMass U (chainGap S.card m i) q ≤ b i)
    (L : Finset (Fin (k + 1))) {i : Fin (k + 1)}
    (hiL : i ∉ L) (hjL : j ∉ L) (hij : i ≠ j)
    (P : (Fin (k + 1) → Option (Finset (ZMod p))) → Prop) [DecidablePred P]
    (t : ZMod p) :
    ((((incrementPartitionFamily S m).filter fun Δ => P (historyKey L Δ)).filter
        fun Δ => subsetSum (Δ i) = t).card : ℝ) ≤
      b i * ((incrementPartitionFamily S m).filter fun Δ => P (historyKey L Δ)).card := by
  apply card_filter_le_of_fiberwise _ (historyKey L) _ (b i)
  intro H hH
  obtain ⟨Δ₀, hΔ₀G, hkey⟩ := Finset.mem_image.mp hH
  obtain ⟨hΔ₀, hPΔ₀⟩ := Finset.mem_filter.mp hΔ₀G
  have e1 : (((incrementPartitionFamily S m).filter fun Δ => P (historyKey L Δ)).filter
        fun Δ => historyKey L Δ = H) =
      (incrementPartitionFamily S m).filter fun Δ => historyKey L Δ = H := by
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro Δ _
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      rw [h, ← hkey]
      exact hPΔ₀
  rw [e1, increment_fiber_card_eq S m L i hiL H Δ₀ hΔ₀ hkey t]
  have hslice := hstep i hij (remainingAfter S L Δ₀) (remainingAfter_subset S L Δ₀)
    (two_unexposed_gaps_sum_le_remaining S m hΔ₀ L hiL hjL hij) t
  exact mul_le_mul_of_nonneg_right hslice (Nat.cast_nonneg _)

/-- Sequential exposure of the increments indexed by a finset `L` not containing `j`
(cardinality form). -/
private theorem increment_event_finset_card_bound
    {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (m : Fin k → ℕ)
    (j : Fin (k + 1))
    (target : Fin (k + 1) → ZMod p)
    (b : Fin (k + 1) → ℝ) (hb : ∀ i, 0 ≤ b i)
    (hstep :
      ∀ i : Fin (k + 1), i ≠ j →
        ∀ U : Finset (ZMod p), U ⊆ S →
          chainGap S.card m i + chainGap S.card m j ≤ U.card →
          ∀ q : ZMod p,
            sliceMass U (chainGap S.card m i) q ≤ b i)
    (L : Finset (Fin (k + 1))) (hjL : j ∉ L) :
    (((incrementPartitionFamily S m).filter fun Δ =>
        ∀ i ∈ L, subsetSum (Δ i) = target i).card : ℝ) ≤
      (∏ i ∈ L, b i) * (incrementPartitionFamily S m).card := by
  classical
  induction L using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, one_mul]
    exact_mod_cast Finset.card_filter_le _ _
  | @insert i L hiL ih =>
    have hjL' : j ∉ L := fun h => hjL (Finset.mem_insert_of_mem h)
    have hij : i ≠ j := fun h => hjL (h ▸ Finset.mem_insert_self i L)
    have hevent : ((incrementPartitionFamily S m).filter fun Δ =>
          ∀ l ∈ insert i L, subsetSum (Δ l) = target l) =
        ((incrementPartitionFamily S m).filter fun Δ =>
          historySatisfies L target (historyKey L Δ)).filter
            fun Δ => subsetSum (Δ i) = target i := by
      rw [Finset.filter_filter]
      apply Finset.filter_congr
      intro Δ _
      rw [historySatisfies_key_iff, Finset.forall_mem_insert]
      exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
    have hprev : ((incrementPartitionFamily S m).filter fun Δ =>
          historySatisfies L target (historyKey L Δ)) =
        (incrementPartitionFamily S m).filter fun Δ =>
          ∀ l ∈ L, subsetSum (Δ l) = target l := by
      apply Finset.filter_congr
      intro Δ _
      exact historySatisfies_key_iff L target Δ
    rw [hevent, Finset.prod_insert hiL]
    calc _ ≤ b i * (((incrementPartitionFamily S m).filter fun Δ =>
            historySatisfies L target (historyKey L Δ)).card : ℝ) :=
          increment_step_card_bound S m j b hstep L hiL hjL' hij
            (historySatisfies L target) (target i)
      _ = b i * (((incrementPartitionFamily S m).filter fun Δ =>
            ∀ l ∈ L, subsetSum (Δ l) = target l).card : ℝ) := by
          rw [hprev]
      _ ≤ b i * ((∏ l ∈ L, b l) * (incrementPartitionFamily S m).card) :=
          mul_le_mul_of_nonneg_left (ih hjL') (hb i)
      _ = b i * (∏ l ∈ L, b l) * (incrementPartitionFamily S m).card := by ring

theorem increment_event_list_bound
    {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (m : Fin k → ℕ)
    (j : Fin (k + 1))
    (target : Fin (k + 1) → ZMod p)
    (b : Fin (k + 1) → ℝ) (hb : ∀ i, 0 ≤ b i)
    (hstep :
      ∀ i : Fin (k + 1), i ≠ j →
        ∀ U : Finset (ZMod p), U ⊆ S →
          chainGap S.card m i + chainGap S.card m j ≤ U.card →
          ∀ q : ZMod p,
            sliceMass U (chainGap S.card m i) q ≤ b i)
    (L : List (Fin (k + 1))) (hLnodup : L.Nodup)
    (hjL : j ∉ L) :
    uniformMass (incrementPartitionFamily S m)
      (fun Δ => ∀ i ∈ L, subsetSum (Δ i) = target i) ≤
        (L.map b).prod := by
  have hjL' : j ∉ L.toFinset := by
    rw [List.mem_toFinset]
    exact hjL
  have hcard := increment_event_finset_card_bound S m j target b hb hstep L.toFinset hjL'
  rw [list_prod_eq_finset_prod_of_nodup L hLnodup b]
  have hfilt : ((incrementPartitionFamily S m).filter fun Δ =>
        ∀ i ∈ L, subsetSum (Δ i) = target i) =
      (incrementPartitionFamily S m).filter fun Δ =>
        ∀ i ∈ L.toFinset, subsetSum (Δ i) = target i := by
    apply Finset.filter_congr
    intro Δ _
    simp only [List.mem_toFinset]
  unfold uniformMass
  rw [hfilt]
  exact div_le_of_le_mul₀ (Nat.cast_nonneg _)
    (Finset.prod_nonneg fun i _ => hb i) hcard

/-- Sequential exposure of all increments except j. -/
theorem incrementPartition_product_bound {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (m : Fin k → ℕ)
    (j : Fin (k + 1))
    (b : Fin (k + 1) → ℝ) (hb : ∀ i, 0 ≤ b i)
    (hstep :
      ∀ i : Fin (k + 1), i ≠ j →
        ∀ U : Finset (ZMod p), U ⊆ S →
          chainGap S.card m i + chainGap S.card m j ≤ U.card →
          ∀ q : ZMod p,
            sliceMass U (chainGap S.card m i) q ≤ b i)
    (target : Fin (k + 1) → ZMod p) :
    uniformMass (incrementPartitionFamily S m)
      (fun Δ => ∀ i, i ≠ j → subsetSum (Δ i) = target i) ≤
        ∏ i ∈ Finset.univ.erase j, b i := by
  have hcard := increment_event_finset_card_bound S m j target b hb hstep
    (Finset.univ.erase j) (Finset.notMem_erase j _)
  have hfilt : ((incrementPartitionFamily S m).filter fun Δ =>
        ∀ i, i ≠ j → subsetSum (Δ i) = target i) =
      (incrementPartitionFamily S m).filter fun Δ =>
        ∀ i ∈ Finset.univ.erase j, subsetSum (Δ i) = target i := by
    apply Finset.filter_congr
    intro Δ _
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
  unfold uniformMass
  rw [hfilt]
  exact div_le_of_le_mul₀ (Nat.cast_nonneg _)
    (Finset.prod_nonneg fun i _ => hb i) hcard

theorem chainMass_fixed_gap_product_bound {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (m : Fin k → ℕ)
    (j : Fin (k + 1))
    (b : Fin (k + 1) → ℝ) (hb : ∀ i, 0 ≤ b i)
    (hstep :
      ∀ i : Fin (k + 1), i ≠ j →
        ∀ U : Finset (ZMod p), U ⊆ S →
          chainGap S.card m i + chainGap S.card m j ≤ U.card →
          ∀ q : ZMod p,
            sliceMass U (chainGap S.card m i) q ≤ b i)
    (z : Fin k → ZMod p) :
    chainMass S m z ≤
      ∏ i ∈ Finset.univ.erase j, b i := by
  classical
  unfold chainMass
  have hmass :
      uniformMass (chainFamily S m)
        (fun R => ∀ i, subsetSum (R i) = z i) =
      uniformMass (incrementPartitionFamily S m)
        (fun Δ => ∀ i, subsetSum (Δ i) = chainGapTarget S z i) := by
    apply uniformMass_bij
      (chainFamily S m) (incrementPartitionFamily S m)
      (fun R => chainIncrements S R)
    · intro R hR
      exact chainIncrements_mem S m hR
    · intro R hR R' hR' hEq
      exact chain_eq_of_increments_eq S hR hR' hEq
    · intro Δ hΔ
      exact ⟨incrementsToChain Δ,
        incrementsToChain_mem S m hΔ,
        increments_chain_inverse S m hΔ⟩
    · intro R hR
      exact chain_sum_event_iff_increment_targets S R hR z
  rw [hmass]
  have hmono :
      uniformMass (incrementPartitionFamily S m)
          (fun Δ => ∀ i, subsetSum (Δ i) = chainGapTarget S z i) ≤
        uniformMass (incrementPartitionFamily S m)
          (fun Δ => ∀ i, i ≠ j →
            subsetSum (Δ i) = chainGapTarget S z i) := by
    apply uniformMass_mono_on
    intro Δ hΔ hall i hij
    exact hall i
  exact le_trans hmono
    (incrementPartition_product_bound S m j b hb hstep
      (chainGapTarget S z))

/-- Corollary 4.2. -/
theorem corollary42 : Corollary42Statement := by
  intro k hk
  have hε0 : (0 : ℝ) < 1 / (k + 1 : ℝ) := by positivity
  have hε1 : 1 / (k + 1 : ℝ) < 1 := by
    rw [div_lt_one (by positivity)]
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  obtain ⟨Cε, hCε, hCor⟩ := corollary14 (1 / (k + 1 : ℝ)) hε0 hε1
  have hCk : 0 < Cε / (1 / (k + 1 : ℝ)) := div_pos hCε hε0
  refine ⟨Cε / (1 / (k + 1 : ℝ)), hCk, ?_⟩
  intro p hp
  have : NeZero p := ⟨hp.ne_zero⟩
  intro S hS m hm z
  obtain ⟨j, hj⟩ := Section4.exists_large_chain_gap m hm
  have hgapj : 1 / (k + 1 : ℝ) * S.card ≤ chainGap S.card m j := by
    have : 1 / (k + 1 : ℝ) * S.card = (S.card : ℝ) / (k + 1 : ℝ) := by ring
    rw [this]
    exact hj
  have hprod :
      chainMass S m z ≤
        ∏ i ∈ Finset.univ.erase j,
          chainFactor p S.card (Cε / (1 / (k + 1 : ℝ))) (chainGap S.card m i) := by
    apply chainMass_fixed_gap_product_bound S m j
      (fun i => chainFactor p S.card (Cε / (1 / (k + 1 : ℝ))) (chainGap S.card m i))
      (fun i => chainFactor_nonneg _ hCk.le)
    intro i hij T hTS hsum q
    have hgap : 0 < chainGap S.card m i := chainGap_pos hk m hm i
    have hTle : (T.card : ℝ) ≤ S.card := by exact_mod_cast Finset.card_le_card hTS
    have hsumR : (chainGap S.card m i : ℝ) + chainGap S.card m j ≤ T.card := by
      exact_mod_cast hsum
    have hgapi0 : (0 : ℝ) ≤ chainGap S.card m i := Nat.cast_nonneg _
    have hTlower : 1 / (k + 1 : ℝ) * S.card ≤ (T.card : ℝ) := by linarith
    have hfrac : (chainGap S.card m i : ℝ) ≤ (1 - 1 / (k + 1 : ℝ)) * T.card := by
      have hscaled : 1 / (k + 1 : ℝ) * T.card ≤ 1 / (k + 1 : ℝ) * S.card :=
        mul_le_mul_of_nonneg_left hTle hε0.le
      nlinarith
    exact chain_factor_from_cor14 S hS (1 / (k + 1 : ℝ)) Cε hε0 hε1 hCε
      (fun U hU r hr hrf q' => hCor p hp U hU r hr hrf q') T hTS hTlower
      (chainGap S.card m i) hgap hfrac q
  calc chainMass S m z
      ≤ ∏ i ∈ Finset.univ.erase j,
          chainFactor p S.card (Cε / (1 / (k + 1 : ℝ))) (chainGap S.card m i) := hprod
    _ ≤ ∑ r : Fin (k + 1), ∏ i ∈ Finset.univ.erase r,
          chainFactor p S.card (Cε / (1 / (k + 1 : ℝ))) (chainGap S.card m i) :=
        Finset.single_le_sum
          (f := fun r => ∏ i ∈ Finset.univ.erase r,
            chainFactor p S.card (Cε / (1 / (k + 1 : ℝ))) (chainGap S.card m i))
          (fun r _ => Finset.prod_nonneg fun i _ => chainFactor_nonneg _ hCk.le)
          (Finset.mem_univ j)
    _ = chainUpperBound p S.card (Cε / (1 / (k + 1 : ℝ))) m := rfl

/-- A fixed positive constant C_k witnessing Corollary 4.2. -/
def chainConstant (k : ℕ) : ℝ := by
  classical
  by_cases hk : 0 < k
  · exact Classical.choose (corollary42 k hk)
  · exact 1

theorem chainConstant_pos (k : ℕ) : 0 < chainConstant k := by
  classical
  unfold chainConstant
  split
  · rename_i hk
    exact (Classical.choose_spec (corollary42 k hk)).1
  · norm_num

theorem chainConstant_spec (k : ℕ) (hk : 0 < k) :
    ∀ (p : ℕ) (hp : p.Prime),
      letI : NeZero p := ⟨hp.ne_zero⟩
      ∀ (S : Finset (ZMod p)), 2 ≤ S.card →
      ∀ (m : Fin k → ℕ), IsChainSizeTuple S.card m →
      ∀ z : Fin k → ZMod p,
        chainMass S m z ≤
          chainUpperBound p S.card (chainConstant k) m := by
  classical
  unfold chainConstant
  simp only [hk, ↓reduceDIte]
  exact (Classical.choose_spec (corollary42 k hk)).2

theorem chainMass_one_eq_sliceMass {p r : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (z : ZMod p) :
    chainMass S (fun _ : Fin 1 => r) (fun _ : Fin 1 => z) =
      sliceMass S r z := by
  unfold chainMass sliceMass
  apply uniformMass_bij (chainFamily S fun _ : Fin 1 => r) (S.powersetCard r)
    (fun R => R 0)
  · intro R hR
    exact Finset.mem_powersetCard.mpr (chain_data_from_mem hR 0)
  · intro R _ R' _ h
    funext i
    rw [Subsingleton.elim i 0]
    exact h
  · intro A hA
    refine ⟨fun _ => A, ?_, rfl⟩
    unfold chainFamily
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, fun _ => Finset.mem_powersetCard.mp hA,
      fun _ _ _ => Finset.Subset.refl _⟩
  · intro R _
    constructor
    · intro h
      exact h 0
    · intro h i
      rw [Subsingleton.elim i 0]
      exact h

/-- The k=1 form used repeatedly in Section 5. -/
theorem corollary42_one_bound {p r : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hS : 2 ≤ S.card)
    (hr : 0 < r) (hrS : r < S.card) (z : ZMod p) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    sliceMass S r z ≤
      (1 / (p : ℝ) +
        chainConstant 1 * Real.sqrt (Real.log (S.card : ℝ)) /
          ((S.card : ℝ) * Real.sqrt (r : ℝ))) +
      (1 / (p : ℝ) +
        chainConstant 1 * Real.sqrt (Real.log (S.card : ℝ)) /
          ((S.card : ℝ) * Real.sqrt ((S.card - r : ℕ) : ℝ))) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hm : IsChainSizeTuple S.card (fun _ : Fin 1 => r) := by
    refine ⟨fun a b hab => ?_, fun _ => ⟨hr, hrS⟩⟩
    exact absurd hab (by rw [Subsingleton.elim a b]; exact lt_irrefl b)
  have h := chainConstant_spec 1 one_pos p hp S hS (fun _ : Fin 1 => r) hm
    (fun _ : Fin 1 => z)
  rw [chainMass_one_eq_sliceMass S z] at h
  refine le_trans h (le_of_eq ?_)
  have g0 : chainGap S.card (fun _ : Fin 1 => r) 0 = r := by
    simp [chainGap, extendedSize]
  have g1 : chainGap S.card (fun _ : Fin 1 => r) 1 = S.card - r := by
    simp [chainGap, extendedSize]
  have e0 : (Finset.univ.erase (0 : Fin 2)) = {1} := by decide
  have e1 : (Finset.univ.erase (1 : Fin 2)) = {0} := by decide
  unfold chainUpperBound
  rw [Fin.sum_univ_two, e0, e1, Finset.prod_singleton, Finset.prod_singleton, g0, g1]
  unfold chainFactor
  ring

end

end GrahamRearrangement
