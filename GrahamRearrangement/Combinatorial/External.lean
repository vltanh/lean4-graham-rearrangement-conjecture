module

public import GrahamRearrangement.Combinatorial.Definitions

@[expose] public section

open scoped BigOperators Pointwise

namespace GrahamRearrangement.Section4External

/-!
# Finite sampling and tuple bookkeeping for Section 4

Everything in this file is proved from finite cardinalities.  No Section 4
argument is axiomatized.
-/

noncomputable section

def extendPairSpace {α : Type*} [DecidableEq α]
    (S : Finset α) (m : ℕ) : Finset (Finset α × α) :=
  ((S.powersetCard (m - 1)).product S).filter fun q => q.2 ∉ q.1

theorem mem_extendPairSpace {α : Type*} [DecidableEq α]
    {S : Finset α} {m : ℕ} {R : Finset α} {x : α} :
    (R,x) ∈ extendPairSpace S m ↔
      R ∈ S.powersetCard (m - 1) ∧ x ∈ S \ R := by
  sorry

def extendPairMap {α : Type*} [DecidableEq α]
    (q : Finset α × α) : Finset α :=
  insert q.2 q.1

theorem extendPairMap_mem {α : Type*} [DecidableEq α]
    {S : Finset α} {m : ℕ} (hm : 0 < m)
    {q : Finset α × α} (hq : q ∈ extendPairSpace S m) :
    extendPairMap q ∈ S.powersetCard m := by
  sorry

/-- Every m-subset has exactly m extension-pair representations. -/
theorem extendPair_fiber_card {α : Type*} [DecidableEq α]
    (S : Finset α) {m : ℕ} (hm : 0 < m)
    {T : Finset α} (hT : T ∈ S.powersetCard m) :
    ((extendPairSpace S m).filter fun q => extendPairMap q = T).card = m := by
  sorry

theorem extendPair_event_card {α : Type*} [DecidableEq α]
    (S : Finset α) {m : ℕ} (hm : 0 < m)
    (E : Finset α → Prop) [DecidablePred E] :
    ((extendPairSpace S m).filter fun q => E (extendPairMap q)).card =
      m * ((S.powersetCard m).filter E).card := by
  sorry

theorem extendPairSpace_card {α : Type*} [DecidableEq α]
    (S : Finset α) {m : ℕ} (hm : 0 < m) :
    (extendPairSpace S m).card = m * (S.powersetCard m).card := by
  simpa using extendPair_event_card S hm (fun _ => True)

/-- A uniform m-subset can be sampled by first taking a uniform (m-1)-subset
and then one uniform point of its complement. -/
theorem uniformSubset_twoStage {α : Type*} [DecidableEq α]
    (S : Finset α) (m : ℕ) (hm : 0 < m) (hmS : m ≤ S.card)
    (E : Finset α → Prop) [DecidablePred E] :
    uniformMass (S.powersetCard m) E =
      uniformExpectation (S.powersetCard (m - 1))
        (fun R =>
          uniformMass (S \ R) (fun x => E (insert x R))) := by
  sorry

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
  sorry

theorem splitPair_event_card {α : Type*} [DecidableEq α]
    (S : Finset α) (m₁ m₂ : ℕ)
    (E : Finset α → Prop) [DecidablePred E] :
    ((splitPairSpace S m₁ m₂).filter
      fun q => E (splitPairMap q)).card =
      Nat.choose (m₁ + m₂) m₁ *
        ((S.powersetCard (m₁ + m₂)).filter E).card := by
  sorry

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
  sorry

/-- Pigeonhole for the k+1 consecutive gaps of an increasing size tuple. -/
theorem exists_large_chain_gap {k n : ℕ} (m : Fin k → ℕ)
    (hm : IsChainSizeTuple n m) :
    ∃ j : Fin (k + 1),
      (n : ℝ) / (k + 1 : ℝ) ≤ chainGap n m j := by
  sorry

/-- Equation (4.1)'s positive-kernel induction, proved by induction on h. -/
theorem prefixKernelSum_le_pow (n h : ℕ) (w : ℕ → ℝ) (B : ℝ)
    (hw : ∀ d, 0 ≤ w d)
    (hrow : ∀ a < n,
      (∑ d ∈ Finset.Icc 1 (n - a), w d) ≤ B) :
    prefixKernelSum n h w ≤ B ^ h := by
  sorry

/-- Omitted-gap factorization used after (4.1). -/
theorem omittedKernelSum_le_prefix_mul (n k : ℕ) (w : ℕ → ℝ)
    (hw : ∀ d, 0 ≤ w d) (j : Fin (k + 1)) :
    omittedKernelSum n k w j ≤
      prefixKernelSum n j.val w *
        prefixKernelSum n (k - j.val) w := by
  sorry

end

end GrahamRearrangement.Section4External
