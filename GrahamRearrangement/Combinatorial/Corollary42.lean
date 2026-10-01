module

public import GrahamRearrangement.Combinatorial.Corollary14

@[expose] public section

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Corollary 4.2
-/

noncomputable section

theorem chainGap_pos {k n : ℕ} (hk : 0 < k)
    (m : Fin k → ℕ) (hm : IsChainSizeTuple n m)
    (i : Fin (k + 1)) :
    0 < chainGap n m i := by
  sorry

theorem chainFactor_nonneg {p n gap : ℕ} (C : ℝ)
    (hC : 0 ≤ C) :
    0 ≤ chainFactor p n C gap := by
  unfold chainFactor
  positivity

theorem chain_factor_from_cor14 {p k : ℕ} [NeZero p] (hp : p.Prime)
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
  sorry

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

theorem subsetSum_sdiff {p : ℕ} [NeZero p]
    {A B : Finset (ZMod p)} (hAB : A ⊆ B) :
    subsetSum (B \ A) = subsetSum B - subsetSum A := by
  sorry

theorem chain_prefix_union_eq {p k : ℕ} [NeZero p]
    (hk : 0 < k) (S : Finset (ZMod p))
    {m : Fin k → ℕ} {R : Fin k → Finset (ZMod p)}
    (hR : R ∈ chainFamily S m) (i : Fin k) :
    (Finset.univ.filter fun j : Fin (k + 1) => j.val ≤ i.val).biUnion
      (chainIncrements S R) = R i := by
  sorry

theorem chain_all_increments_union_eq {p k : ℕ} [NeZero p]
    (hk : 0 < k) (S : Finset (ZMod p))
    {m : Fin k → ℕ} {R : Fin k → Finset (ZMod p)}
    (hR : R ∈ chainFamily S m) :
    Finset.univ.biUnion (chainIncrements S R) = S := by
  sorry

theorem chain_increment_subset {p k : ℕ} [NeZero p]
    (hk : 0 < k) (S : Finset (ZMod p))
    {m : Fin k → ℕ} {R : Fin k → Finset (ZMod p)}
    (hR : R ∈ chainFamily S m)
    (i : Fin (k + 1)) :
    chainIncrements S R i ⊆ S := by
  sorry

theorem chain_increment_disjoint_of_lt {p k : ℕ} [NeZero p]
    (hk : 0 < k) (S : Finset (ZMod p))
    {m : Fin k → ℕ} {R : Fin k → Finset (ZMod p)}
    (hR : R ∈ chainFamily S m)
    {i j : Fin (k + 1)} (hij : i.val < j.val) :
    Disjoint (chainIncrements S R i) (chainIncrements S R j) := by
  sorry

theorem chainIncrements_mem {p k : ℕ} [NeZero p]
    (hk : 0 < k) (S : Finset (ZMod p))
    (m : Fin k → ℕ) {R : Fin k → Finset (ZMod p)}
    (hR : R ∈ chainFamily S m) :
    chainIncrements S R ∈ incrementPartitionFamily S m := by
  sorry

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

theorem canonicalChain_mem {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (m : Fin k → ℕ)
    (hm : IsChainSizeTuple S.card m) :
    canonicalChain S m hm ∈ chainFamily S m := by
  sorry

theorem chainFamily_nonempty {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (m : Fin k → ℕ)
    (hm : IsChainSizeTuple S.card m) :
    (chainFamily S m).Nonempty :=
  ⟨canonicalChain S m hm, canonicalChain_mem S m hm⟩

theorem chain_eq_of_increments_eq {p k : ℕ} [NeZero p]
    (hk : 0 < k) (S : Finset (ZMod p))
    {m : Fin k → ℕ}
    {R R' : Fin k → Finset (ZMod p)}
    (hR : R ∈ chainFamily S m) (hR' : R' ∈ chainFamily S m)
    (hEq : chainIncrements S R = chainIncrements S R') :
    R = R' := by
  funext i
  rw [← chain_prefix_union_eq hk S hR i,
      ← chain_prefix_union_eq hk S hR' i]
  simp [hEq]

theorem increments_prefix_union_eq {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (m : Fin k → ℕ)
    {Δ : Fin (k + 1) → Finset (ZMod p)}
    (hΔ : Δ ∈ incrementPartitionFamily S m)
    (i : Fin k) :
    incrementsToChain Δ i =
      (Finset.univ.filter fun j : Fin (k + 1) => j.val ≤ i.val).biUnion Δ := rfl

theorem increments_chain_inverse {p k : ℕ} [NeZero p]
    (hk : 0 < k) (S : Finset (ZMod p)) (m : Fin k → ℕ)
    (hm : IsChainSizeTuple S.card m)
    {Δ : Fin (k + 1) → Finset (ZMod p)}
    (hΔ : Δ ∈ incrementPartitionFamily S m) :
    chainIncrements S (incrementsToChain Δ) = Δ := by
  sorry

theorem incrementPartitionFamily_nonempty {p k : ℕ} [NeZero p]
    (hk : 0 < k) (S : Finset (ZMod p))
    (m : Fin k → ℕ) (hm : IsChainSizeTuple S.card m) :
    (incrementPartitionFamily S m).Nonempty := by
  let R := canonicalChain S m hm
  exact ⟨chainIncrements S R,
    chainIncrements_mem hk S m (canonicalChain_mem S m hm)⟩

theorem incrementsToChain_mem {p k : ℕ} [NeZero p]
    (hk : 0 < k) (S : Finset (ZMod p))
    (m : Fin k → ℕ)
    {Δ : Fin (k + 1) → Finset (ZMod p)}
    (hΔ : Δ ∈ incrementPartitionFamily S m) :
    incrementsToChain Δ ∈ chainFamily S m := by
  sorry

theorem chain_increment_bijection {p k : ℕ} [NeZero p]
    (hk : 0 < k) (S : Finset (ZMod p))
    (m : Fin k → ℕ) (hm : IsChainSizeTuple S.card m) :
    (chainFamily S m).card = (incrementPartitionFamily S m).card := by
  classical
  apply Finset.card_bij
    (fun R _ => chainIncrements S R)
  · intro R hR
    exact chainIncrements_mem hk S m hR
  · intro R hR R' hR' hEq
    exact chain_eq_of_increments_eq hk S hR hR' hEq
  · intro Δ hΔ
    refine ⟨incrementsToChain Δ,
      incrementsToChain_mem hk S m hΔ, ?_⟩
    exact increments_chain_inverse hk S m hm hΔ

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
    (hk : 0 < k) (S : Finset (ZMod p))
    {m : Fin k → ℕ} {R : Fin k → Finset (ZMod p)}
    (hR : R ∈ chainFamily S m) (i : Fin k) :
    subsetSum (R i) =
      ∑ j ∈ Finset.univ.filter (fun j : Fin (k + 1) => j.val ≤ i.val),
        subsetSum (chainIncrements S R j) := by
  rw [← chain_prefix_union_eq hk S hR i]
  apply subsetSum_biUnion_pairwise_disjoint
  intro a ha b hb hab
  by_cases hlt : a.val < b.val
  · exact chain_increment_disjoint_of_lt hk S hR hlt
  · exact (chain_increment_disjoint_of_lt hk S hR (by omega)).symm

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

theorem chainGapTarget_prefix_telescopes {p k : ℕ} [NeZero p]
    (hk : 0 < k) (S : Finset (ZMod p))
    (z : Fin k → ZMod p) (i : Fin k) :
    ∑ j ∈ Finset.univ.filter (fun j : Fin (k + 1) => j.val ≤ i.val),
      chainGapTarget S z j = z i := by
  sorry

theorem chain_sum_event_iff_increment_targets {p k : ℕ} [NeZero p]
    (hk : 0 < k) (S : Finset (ZMod p))
    {m : Fin k → ℕ} (R : Fin k → Finset (ZMod p))
    (hR : R ∈ chainFamily S m)
    (z : Fin k → ZMod p) :
    (∀ i, subsetSum (R i) = z i) ↔
      ∀ i : Fin (k + 1),
        subsetSum (chainIncrements S R i) = chainGapTarget S z i := by
  sorry

def exposureOrder {k : ℕ} (j : Fin (k + 1)) :
    List (Fin (k + 1)) :=
  (List.ofFn fun i : Fin j.val => ⟨i.val,by omega⟩) ++
  (List.ofFn fun i : Fin (k - j.val) =>
    ⟨k - i.val,by omega⟩)

theorem exposureOrder_nodup {k : ℕ} (j : Fin (k + 1)) :
    (exposureOrder j).Nodup := by
  sorry

theorem mem_exposureOrder_iff {k : ℕ} (j : Fin (k + 1))
    (i : Fin (k + 1)) :
    i ∈ exposureOrder j ↔ i ≠ j := by
  sorry

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
  sorry

theorem partitionPermMap_history_fixed {p k : ℕ} [NeZero p]
    (L : Finset (Fin (k + 1)))
    (π : Equiv.Perm (ZMod p))
    {Δ : Fin (k + 1) → Finset (ZMod p)}
    (hfix : ∀ x ∈ exposedUnion L Δ, π x = x) :
    historyKey L (partitionPermMap π Δ) = historyKey L Δ := by
  sorry

theorem remaining_invariant_under_history
    {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    (L : Finset (Fin (k + 1)))
    {Δ Γ : Fin (k + 1) → Finset (ZMod p)}
    (hkey : historyKey L Δ = historyKey L Γ) :
    remainingAfter S L Δ = remainingAfter S L Γ := by
  sorry

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
    (S : Finset (ZMod p)) (m : Fin k → ℕ)
    {Δ : Fin (k + 1) → Finset (ZMod p)}
    (hΔ : Δ ∈ incrementPartitionFamily S m)
    (L : Finset (Fin (k + 1)))
    {x : ZMod p} (hx : x ∈ exposedUnion L Δ) :
    x ∉ remainingAfter S L Δ := by
  intro hxrem
  exact (Finset.mem_sdiff.mp hxrem).2 hx

theorem perm_fix_exposed_of_fix_outside_remaining
    {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (m : Fin k → ℕ)
    (L : Finset (Fin (k + 1)))
    {Δ : Fin (k + 1) → Finset (ZMod p)}
    (hΔ : Δ ∈ incrementPartitionFamily S m)
    (π : Equiv.Perm (ZMod p))
    (hfix : ∀ x ∉ remainingAfter S L Δ, π x = x) :
    ∀ x ∈ exposedUnion L Δ, π x = x := by
  intro x hx
  exact hfix x (exposed_not_remaining S m hΔ L hx)

theorem perm_fix_outside_S_of_fix_outside_remaining
    {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (m : Fin k → ℕ)
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
    (hi : i ∉ L)
    (H : Fin (k + 1) → Option (Finset (ZMod p)))
    (Δ₀ : Fin (k + 1) → Finset (ZMod p))
    (hΔ₀ : Δ₀ ∈ incrementPartitionFamily S m)
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
  sorry

theorem increment_conditional_uniform_given_history
    {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (m : Fin k → ℕ)
    (hm : IsChainSizeTuple S.card m)
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
  sorry

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

theorem increment_event_list_bound
    {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (m : Fin k → ℕ)
    (hm : IsChainSizeTuple S.card m)
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
  sorry

/-- Sequential exposure of all increments except j. -/
theorem incrementPartition_product_bound {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (m : Fin k → ℕ)
    (hm : IsChainSizeTuple S.card m)
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
  sorry

theorem chainMass_fixed_gap_product_bound {p k : ℕ} [NeZero p]
    (hk : 0 < k)
    (S : Finset (ZMod p)) (m : Fin k → ℕ)
    (hm : IsChainSizeTuple S.card m)
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
      exact chainIncrements_mem hk S m hR
    · intro R hR R' hR' hEq
      exact chain_eq_of_increments_eq hk S hR hR' hEq
    · intro Δ hΔ
      exact ⟨incrementsToChain Δ,
        incrementsToChain_mem hk S m hΔ,
        increments_chain_inverse hk S m hm hΔ⟩
    · intro R hR
      exact chain_sum_event_iff_increment_targets hk S R hR z
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
    (incrementPartition_product_bound S m hm j b hb hstep
      (chainGapTarget S z))

/-- Corollary 4.2. -/
theorem corollary42 : Corollary42Statement := by
  sorry

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
  simp only [dif_pos hk]
  exact (Classical.choose_spec (corollary42 k hk)).2

theorem chainMass_one_eq_sliceMass {p r : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (z : ZMod p) :
    chainMass S (fun _ : Fin 1 => r) (fun _ : Fin 1 => z) =
      sliceMass S r z := by
  sorry

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
  sorry

end

end GrahamRearrangement
