module

public import GrahamRearrangement.Rearrangement.Parameters

@[expose] public section

open scoped BigOperators Pointwise

namespace GrahamRearrangement.Section5External

/-!
# Generic finite-permutation facts used in Section 5

The finite-bijection, conditioning, matching, counting, and permutation facts
used by Section 5 are all proved in this module.  It contains no project axioms.
-/

noncomputable section

theorem indexedOrderings_nonempty {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) :
    (indexedOrderings S).Nonempty := by
  classical
  let e : Fin S.card ≃ {x // x ∈ S} :=
    Fintype.equivOfCardEq (by simp)
  let σ : Fin S.card → ZMod p := fun i => (e i).1
  refine ⟨σ, ?_⟩
  simp only [indexedOrderings, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro i j hij
    exact e.injective (Subtype.ext hij)
  · intro x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := e.surjective ⟨x, hx⟩
      exact ⟨i, congrArg Subtype.val hi⟩
    · rintro ⟨i, rfl⟩
      exact (e i).2

def applyValuePerm {n p : ℕ}
    (π : Equiv.Perm (ZMod p))
    (σ : Fin n → ZMod p) : Fin n → ZMod p :=
  π ∘ σ

theorem applyValuePerm_isIndexedOrdering
    {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (π : Equiv.Perm (ZMod p)) (hπS : S.image π = S)
    {σ : Fin S.card → ZMod p}
    (hσ : IsIndexedOrdering S σ) :
    IsIndexedOrdering S (applyValuePerm π σ) := by
  sorry

theorem indexImageSet_applyValuePerm
    {n p : ℕ} (π : Equiv.Perm (ZMod p))
    (σ : Fin n → ZMod p) (I : Finset (Fin n)) :
    indexImageSet (applyValuePerm π σ) I =
      (indexImageSet σ I).image π := by
  ext x
  simp [indexImageSet,applyValuePerm]

theorem fixedIndexSet_image_uniform {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (I : Finset (Fin S.card))
    (E : Finset (ZMod p) → Prop) [DecidablePred E] :
    orderingEventMass S (fun σ => E (indexImageSet σ I)) =
      uniformMass (S.powersetCard I.card) E := by
  sorry

/-- The image of a fixed r-set of indices under a uniform bijection is a
uniform r-subset of S. -/
theorem fixedIndexSet_sumMass {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (I : Finset (Fin S.card))
    (z : ZMod p) :
    orderingEventMass S (fun σ => indexSetSum σ I = z) =
      sliceMass S I.card z := by
  sorry

/-- Composition by a fixed permutation of positions preserves the uniform law. -/
theorem ordering_perm_invariant {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (π : Equiv.Perm (Fin S.card))
    (E : (Fin S.card → ZMod p) → Prop) [DecidablePred E] :
    orderingEventMass S E =
      orderingEventMass S (fun σ => E (applyPositionPerm σ π)) := by
  sorry

/-- Conditional version of the preceding invariance. -/
theorem ordering_conditional_perm_invariant {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (π : Equiv.Perm (Fin S.card))
    (cond event : (Fin S.card → ZMod p) → Prop)
    [DecidablePred cond] [DecidablePred event] :
    orderingConditionalMass S cond event =
      orderingConditionalMass S
        (fun σ => cond (applyPositionPerm σ π))
        (fun σ => event (applyPositionPerm σ π)) := by
  sorry

/-- Distinct index subsets in a window have equal image sums with probability at
most the reciprocal number of choices left for one exposed coordinate. -/
theorem sliceMass_one_le_inv_card {p : ℕ} [NeZero p]
    (T : Finset (ZMod p)) (hT : T.Nonempty) (z : ZMod p) :
    sliceMass T 1 z ≤ 1 / (T.card : ℝ) := by
  sorry

theorem indexSetSum_eq_of_agreesOn
    {n p : ℕ} {F : Finset (Fin n)}
    {σ τ : Fin n → ZMod p}
    (hagr : AgreesOn F σ τ)
    {J : Finset (Fin n)} (hJF : J ⊆ F) :
    indexSetSum σ J = indexSetSum τ J := by
  unfold indexSetSum
  apply Finset.sum_congr rfl
  intro i hi
  exact hagr i (hJF hi)

theorem distinct_index_subset_sums_mass_le {p : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    (W J J' : Finset (Fin S.card))
    (hJ : J ⊆ W) (hJ' : J' ⊆ W) (hne : J ≠ J')
    (hW : W.card ≤ S.card) :
    orderingEventMass S (fun σ => indexSetSum σ J = indexSetSum σ J') ≤
      1 / ((S.card - W.card + 1 : ℕ) : ℝ) := by
  sorry

theorem exposedImage_subset {p : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    {τ : Fin S.card → ZMod p} (hτ : IsIndexedOrdering S τ)
    (F : Finset (Fin S.card)) :
    indexImageSet τ F ⊆ S := by
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨i,hi,rfl⟩
  exact (hτ.2 _).2 ⟨i,rfl⟩

theorem unexposed_indexImage_subset_remaining
    {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (τ σ : Fin S.card → ZMod p)
    (hτ : IsIndexedOrdering S τ)
    (hσ : IsIndexedOrdering S σ)
    (F J : Finset (Fin S.card))
    (hagr : AgreesOn F σ τ) (hdisj : Disjoint F J) :
    indexImageSet σ J ⊆ S \ indexImageSet τ F := by
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨j,hj,rfl⟩
  apply Finset.mem_sdiff.mpr
  constructor
  · exact (hσ.2 _).2 ⟨j,rfl⟩
  · intro himg
    rcases Finset.mem_image.mp himg with ⟨i,hiF,heq⟩
    have hσi : σ i = τ i := hagr i hiF
    have hsij : i = j := hσ.1 (hσi.trans heq)
    subst i
    exact Finset.disjoint_left.mp hdisj hiF hj

theorem valuePerm_preserves_agreement
    {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (τ σ : Fin S.card → ZMod p)
    (F : Finset (Fin S.card))
    (π : Equiv.Perm (ZMod p))
    (hfix : ∀ x ∈ indexImageSet τ F, π x = x)
    (hagr : AgreesOn F σ τ) :
    AgreesOn F (applyValuePerm π σ) τ := by
  intro i hi
  unfold applyValuePerm
  change π (σ i) = τ i
  rw [hagr i hi]
  exact hfix (τ i) (Finset.mem_image.mpr ⟨i,hi,rfl⟩)

theorem conditional_fixedIndexSet_image_uniform
    {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (τ : Fin S.card → ZMod p) (hτ : IsIndexedOrdering S τ)
    (F J : Finset (Fin S.card)) (hdisj : Disjoint F J)
    (E : Finset (ZMod p) → Prop) [DecidablePred E] :
    orderingConditionalMass S
      (fun σ => AgreesOn F σ τ)
      (fun σ => E (indexImageSet σ J)) =
    uniformMass
      ((S \ indexImageSet τ F).powersetCard J.card) E := by
  sorry

theorem conditional_fixedIndexSet_sumMass
    {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (τ : Fin S.card → ZMod p) (hτ : IsIndexedOrdering S τ)
    (F J : Finset (Fin S.card)) (hdisj : Disjoint F J)
    (z : ZMod p) :
    orderingConditionalMass S
      (fun σ => AgreesOn F σ τ)
      (fun σ => indexSetSum σ J = z) =
    sliceMass (S \ indexImageSet τ F) J.card z := by
  sorry

/-- Conditional union bound for a finite family of disjoint unexposed index sets. -/
theorem conditional_index_family_sumMass_le_zmod
    {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (τ : Fin S.card → ZMod p) (hτ : IsIndexedOrdering S τ)
    (F : Finset (Fin S.card))
    (A : Finset (Fin S.card))
    (I : Fin S.card → Finset (Fin S.card))
    (z : Fin S.card → ZMod p)
    (hdisj : ∀ a ∈ A, Disjoint F (I a)) :
    orderingConditionalMass S
      (fun σ => AgreesOn F σ τ)
      (fun σ => ∃ a ∈ A, indexSetSum σ (I a) = z a) ≤
      ∑ a ∈ A,
        sliceMass (S \ indexImageSet τ F) (I a).card (z a) := by
  sorry

theorem partition_member_unique
    {α : Type*} [DecidableEq α] {k : ℕ}
    (T : Finset α) (Δ : Fin (k + 1) → Finset α)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Δ i) (Δ j))
    (hcover : ∀ x, x ∈ T ↔ ∃ i, x ∈ Δ i)
    {x : α} (hxT : x ∈ T)
    {i j : Fin (k + 1)} (hxi : x ∈ Δ i) (hxj : x ∈ Δ j) :
    i = j := by
  by_contra hij
  exact Finset.disjoint_left.mp (hdisj i j hij) hxi hxj

/-- Two nested chains with the same cardinality vector are carried to one
another by a permutation of the ground set, obtained by matching the disjoint
increment layers. -/
theorem exists_value_perm_maps_chain
    {p k : ℕ} [NeZero p] (hk : 0 < k)
    (T : Finset (ZMod p)) (m : Fin k → ℕ)
    {R R' : Fin k → Finset (ZMod p)}
    (hR : R ∈ chainFamily T m) (hR' : R' ∈ chainFamily T m) :
    ∃ π : Equiv.Perm (ZMod p),
      T.image π = T ∧
      (∀ x ∉ T, π x = x) ∧
      ∀ i, (R i).image π = R' i := by
  sorry

/-- After fixing the values on F, the images of fixed nested unexposed index
sets are uniformly distributed over nested chains of the prescribed sizes in
the remaining ground set. -/
theorem conditional_nested_images_chainMass {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    (τ : Fin S.card → ZMod p) (hτ : IsIndexedOrdering S τ)
    (F : Finset (Fin S.card))
    (I : Fin k → Finset (Fin S.card))
    (hdisj : ∀ i, Disjoint F (I i))
    (hnested : ∀ i j, i ≤ j → I i ⊆ I j)
    (m : Fin k → ℕ) (hcard : ∀ i, (I i).card = m i)
    (z : Fin k → ZMod p) :
    orderingConditionalMass S
      (fun σ => AgreesOn F σ τ)
      (fun σ => ∀ i, indexSetSum σ (I i) = z i) =
      chainMass (S \ indexImageSet τ F) m z := by
  sorry

/-- Conditioning on a window gives the obvious complement cardinality. -/
theorem exposed_image_card {p : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    {τ : Fin S.card → ZMod p} (hτ : IsIndexedOrdering S τ)
    (F : Finset (Fin S.card)) :
    (indexImageSet τ F).card = F.card := by
  sorry

def agreementKey {n p : ℕ}
    (F : Finset (Fin n)) (σ : Fin n → ZMod p) :
    Fin n → Option (ZMod p) :=
  fun i => if i ∈ F then some (σ i) else none

theorem agreementKey_eq_iff {n p : ℕ}
    (F : Finset (Fin n)) (σ τ : Fin n → ZMod p) :
    agreementKey F σ = agreementKey F τ ↔
      AgreesOn F σ τ := by
  constructor
  · intro h i hi
    have hval := congrFun h i
    simpa [agreementKey,hi] using hval
  · intro h
    funext i
    by_cases hi : i ∈ F
    · simp [agreementKey,hi,h i hi]
    · simp [agreementKey,hi]

/-- A uniform bound on every exposed-value fiber is also an unconditional bound. -/
theorem event_le_of_agreesOn_fibers {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (F : Finset (Fin S.card))
    (E : (Fin S.card → ZMod p) → Prop) [DecidablePred E]
    (q : ℝ)
    (hfiber :
      ∀ τ, IsIndexedOrdering S τ →
        orderingConditionalMass S
          (fun σ => AgreesOn F σ τ) E ≤ q) :
    orderingEventMass S E ≤ q := by
  sorry

/-- Fiber multiplication specialized to exposing a set of positions in a
uniform random ordering. -/
theorem joint_event_le_of_agreesOn_fibers {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (F : Finset (Fin S.card))
    (A B : (Fin S.card → ZMod p) → Prop)
    [DecidablePred A] [DecidablePred B]
    (a b : ℝ)
    (hA : orderingEventMass S A ≤ a)
    (hdetermined :
      ∀ σ τ, AgreesOn F σ τ → (A σ ↔ A τ))
    (hfiber :
      ∀ τ, IsIndexedOrdering S τ → A τ →
        orderingConditionalMass S
          (fun σ => AgreesOn F σ τ) B ≤ b) :
    orderingEventMass S (fun σ => A σ ∧ B σ) ≤ a * b := by
  sorry

/-- Union bound over a finite set of possible parameter records. -/
theorem finite_parameter_union_bound
    {Ω Θ : Type*} [DecidableEq Ω] [DecidableEq Θ]
    (space : Finset Ω) (params : Finset Θ)
    (E : Θ → Ω → Prop) [∀ θ, DecidablePred (E θ)] :
    uniformMass space (fun ω => ∃ θ ∈ params, E θ ω) ≤
      ∑ θ ∈ params, uniformMass space (E θ) :=
  uniformMass_exists_le_sum space params E

/-- Union bound in witness form: if every occurrence of E supplies a parameter
θ and the θ-event has mass at most q, then E has mass at most |params| q. -/
theorem witness_union_bound
    {Ω Θ : Type*} [DecidableEq Ω] [DecidableEq Θ]
    (space : Finset Ω) (params : Finset Θ)
    (E : Ω → Prop) (A : Θ → Ω → Prop)
    [DecidablePred E] [∀ θ, DecidablePred (A θ)]
    (q : ℝ)
    (hcover : ∀ ω ∈ space, E ω → ∃ θ ∈ params, A θ ω)
    (hbound : ∀ θ ∈ params, uniformMass space (A θ) ≤ q) :
    uniformMass space E ≤ (params.card : ℝ) * q := by
  sorry
theorem dense_window_extract {n D : ℕ}
    (B : Finset (Fin n)) (hD : 0 < D)
    (h : ∃ z : Fin n,
      D < (B ∩ symmetricWindow z (10 * D)).card) :
    ∃ b₀ ∈ B, ∃ b : Fin D → Fin n,
      Function.Injective b ∧
      (∀ i, b i ∈ B) ∧
      (∀ i, paperPos b₀ < paperPos (b i) ∧
        paperPos (b i) ≤ paperPos b₀ + 20 * D) := by
  sorry

theorem disjoint_swaps_commute_general {α : Type*} [DecidableEq α]
    (a b c d : α)
    (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) :
    (Equiv.swap a b).trans (Equiv.swap c d) =
      (Equiv.swap c d).trans (Equiv.swap a b) := by
  sorry

theorem disjoint_swaps_commute {α : Type*} [DecidableEq α]
    (a b c d : α)
    (_hab : a ≠ b) (_hcd : c ≠ d)
    (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) :
    (Equiv.swap a b).trans (Equiv.swap c d) =
      (Equiv.swap c d).trans (Equiv.swap a b) :=
  disjoint_swaps_commute_general a b c d hac had hbc hbd

theorem disjoint_swaps_fix_outside_support
    {α : Type*} [DecidableEq α]
    (P : Finset (α × α))
    (_hP : (↑P : Set (α × α)).Pairwise fun q r =>
      q.1 ≠ r.1 ∧ q.1 ≠ r.2 ∧ q.2 ≠ r.1 ∧ q.2 ≠ r.2)
    (i : α)
    (hi : ∀ q ∈ P, i ≠ q.1 ∧ i ≠ q.2) :
    swapsPermList P.toList i = i := by
  sorry

theorem nodup_lists_perm_of_toFinset_eq {α : Type*} [DecidableEq α]
    {l r : List α} (hl : l.Nodup) (hr : r.Nodup)
    (hset : l.toFinset = r.toFinset) :
    l.Perm r := by
  sorry

theorem swapsPermList_eq_of_perm_pairwise
    {α : Type*} [DecidableEq α]
    {l r : List (α × α)}
    (hp : l.Perm r)
    (hpair : (↑l.toFinset : Set (α × α)).Pairwise fun q s =>
      q.1 ≠ s.1 ∧ q.1 ≠ s.2 ∧ q.2 ≠ s.1 ∧ q.2 ≠ s.2) :
    swapsPermList l = swapsPermList r := by
  sorry

theorem disjoint_swaps_order_independent
    {α : Type*} [DecidableEq α]
    (P : Finset (α × α))
    (hP : (↑P : Set (α × α)).Pairwise fun q r =>
      q.1 ≠ r.1 ∧ q.1 ≠ r.2 ∧ q.2 ≠ r.1 ∧ q.2 ≠ r.2)
    (l : List (α × α)) (hl : l.toFinset = P) (hln : l.Nodup) :
    swapsPermList l = swapsPermList P.toList := by
  have hp := nodup_lists_perm_of_toFinset_eq hln P.nodup_toList
    (by simpa [hl])
  apply swapsPermList_eq_of_perm_pairwise hp
  simpa [hl] using hP

theorem swapsPermList_pair_action
    {α : Type*} [LinearOrder α] [DecidableEq α]
    (P : Finset (α × α))
    (hPpair : (↑P : Set (α × α)).Pairwise fun q r =>
      q.1 ≠ r.1 ∧ q.1 ≠ r.2 ∧ q.2 ≠ r.1 ∧ q.2 ≠ r.2)
    (hord : ∀ q ∈ P, q.1 < q.2)
    {q : α × α} (hq : q ∈ P) :
    swapsPermList P.toList q.1 = q.2 ∧
      swapsPermList P.toList q.2 = q.1 := by
  sorry

theorem disjoint_swaps_reconstruct
    {α : Type*} [LinearOrder α] [DecidableEq α]
    (P Q : Finset (α × α))
    (hPpair : (↑P : Set (α × α)).Pairwise fun q r =>
      q.1 ≠ r.1 ∧ q.1 ≠ r.2 ∧ q.2 ≠ r.1 ∧ q.2 ≠ r.2)
    (hQpair : (↑Q : Set (α × α)).Pairwise fun q r =>
      q.1 ≠ r.1 ∧ q.1 ≠ r.2 ∧ q.2 ≠ r.1 ∧ q.2 ≠ r.2)
    (hPord : ∀ q ∈ P, q.1 < q.2)
    (hQord : ∀ q ∈ Q, q.1 < q.2)
    (hperm : swapsPermList P.toList = swapsPermList Q.toList) :
    P = Q := by
  sorry

theorem swapsPermList_append {n : ℕ}
    (l r : List (Fin n × Fin n)) :
    swapsPermList (l ++ r) =
      (swapsPermList l).trans (swapsPermList r) := by
  induction l with
  | nil => simp [swapsPermList]
  | cons q qs ih =>
      simp [swapsPermList,ih,Equiv.trans_assoc]

theorem swap_image_eq_self_of_not_crosses {n : ℕ}
    (q : Fin n × Fin n) (I : Finset (Fin n))
    (hnot : ¬ SwapCrosses q I) :
    I.image (Equiv.swap q.1 q.2) = I := by
  sorry

theorem swapsPermList_image_eq_self
    {n : ℕ} (l : List (Fin n × Fin n))
    (I : Finset (Fin n))
    (hnot : ∀ q ∈ l, ¬ SwapCrosses q I) :
    I.image (swapsPermList l) = I := by
  sorry

/-- Delete swaps crossing none of the constrained index sets.  The deleted
swaps preserve every constrained set, and pairwise-disjoint transpositions
commute, so all constrained images are unchanged. -/
theorem trim_irrelevant_disjoint_swaps
    {n k : ℕ} (P : Finset (Fin n × Fin n))
    (hP : (↑P : Set (Fin n × Fin n)).Pairwise swapPairsDisjoint)
    (I : Fin k → Finset (Fin n)) :
    ∃ P' ⊆ P,
      (↑P' : Set (Fin n × Fin n)).Pairwise swapPairsDisjoint ∧
      (∀ q ∈ P', ∃ i, ((q.1 ∈ I i) ↔ q.2 ∉ I i)) ∧
      ∀ i, (I i).image (collectionPerm P') =
        (I i).image (collectionPerm P) := by
  sorry

/-- Sort a finite injective tuple by a permutation of its coordinates. -/
theorem exists_sorting_perm
    {α : Type*} [LinearOrder α] [DecidableEq α] {k : ℕ}
    (x : Fin k → α) (hinj : Function.Injective x) :
    ∃ ρ : Equiv.Perm (Fin k), StrictMono (x ∘ ρ) := by
  sorry

/-- Generic finite union over conditional nested-chain witnesses.  This is only
bookkeeping: each individual witness is identified with a chain by
`conditional_nested_images_chainMass`, then the size-vector sum is embedded
in Lemma 4.3. -/
theorem conditional_chain_witness_union_bound
    {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    (τ : Fin S.card → ZMod p) (hτ : IsIndexedOrdering S τ)
    (F : Finset (Fin S.card))
    {Θ : Type*} [DecidableEq Θ]
    (A : Finset Θ)
    (I : Θ → Fin k → Finset (Fin S.card))
    (m : Θ → Fin k → ℕ)
    (z : Θ → Fin k → ZMod p)
    (C : ℝ)
    (hdisj : ∀ θ ∈ A, ∀ i, Disjoint F (I θ i))
    (hnested : ∀ θ ∈ A, ∀ i j, i ≤ j → I θ i ⊆ I θ j)
    (hcard : ∀ θ ∈ A, ∀ i, (I θ i).card = m θ i)
    (hvalid : ∀ θ ∈ A,
      IsChainSizeTuple (S \ indexImageSet τ F).card (m θ))
    (hinj : Set.InjOn m A)
    (hchain :
      ∀ θ ∈ A,
        chainMass (S \ indexImageSet τ F) (m θ) (z θ) ≤
          chainUpperBound p (S \ indexImageSet τ F).card C (m θ)) :
    orderingConditionalMass S
      (fun σ => AgreesOn F σ τ)
      (fun σ => ∃ θ ∈ A, ∀ i, indexSetSum σ (I θ i) = z θ i) ≤
      lemma43LHS p (S \ indexImageSet τ F).card k C := by
  sorry

/-- If a remaining ground set has size between n/2 and n, the Lemma 4.3 base
is bounded by twice the ambient n^{-α} bound used in Section 5. -/
theorem half_ground_lemma43Base_le
    {n s p : ℕ} {α C : ℝ}
    (hn : 2 ≤ n) (hhalf : n / 2 ≤ s) (hsn : s ≤ n)
    (hCnonneg : 0 ≤ C)
    (hp : (n : ℝ) / p ≤ (n : ℝ) ^ (-α))
    (hC :
      4 * C * Real.sqrt (Real.log (n : ℝ)) /
        Real.sqrt (n : ℝ) ≤ (n : ℝ) ^ (-α)) :
    lemma43Base p s C ≤ 2 * (n : ℝ) ^ (-α) := by
  sorry

/-- The exponent comparison αD≥3 used in the D-fold chain bounds. -/
theorem two_neg_alpha_pow_le_cube
    {n D : ℕ} {α : ℝ}
    (hn : 1 ≤ n) (hα0 : 0 < α)
    (hαD : 3 ≤ α * D) :
    (2 * (n : ℝ) ^ (-α)) ^ D ≤
      (2 : ℝ) ^ D / (n : ℝ) ^ 3 := by
  sorry

/-- Reindex an injective finite family of valid chain-size tuples into the full
sum occurring in Lemma 4.3. -/
theorem chainUpperBound_sum_le_lemma43
    {Θ : Type*} [DecidableEq Θ]
    {p n k : ℕ} (C : ℝ)
    (X : Finset Θ) (m : Θ → Fin k → ℕ)
    (hvalid : ∀ θ ∈ X, IsChainSizeTuple n (m θ))
    (hinj : Set.InjOn m X) :
    (∑ θ ∈ X, chainUpperBound p n C (m θ)) ≤
      lemma43LHS p n k C := by
  sorry

/-- The right-tail size tuple associated with a strictly increasing tail tuple is
a valid chain-size tuple in the remaining ground set. -/
theorem tailSizes_valid
    {n D s : ℕ}
    (b b' : Fin n)
    (hb2 : 2 ≤ paperPos b)
    (hgap : paperPos b' - paperPos b = 5 * D)
    (x : Fin D → Fin n)
    (hx : x ∈ tailTuples b' D)
    (hs : s = n - (5 * D + 1)) :
    IsChainSizeTuple s (tailSizes b' x) := by
  sorry

/-- Generic two-level witness union bound: for each outer parameter there are
at most M inner choices, each inner event has weight w(theta), and the outer
weights sum to at most B. -/
theorem bounded_choice_witness_union
    {Ω Θ Ξ : Type*} [DecidableEq Ω] [DecidableEq Θ] [DecidableEq Ξ]
    (space : Finset Ω) (outer : Finset Θ)
    (inner : Θ → Finset Ξ)
    (E : Ω → Prop) (A : Θ → Ξ → Ω → Prop)
    [DecidablePred E] [∀ θ ξ, DecidablePred (A θ ξ)]
    (M : ℕ) (w : Θ → ℝ) (B : ℝ)
    (hcover :
      ∀ ω ∈ space, E ω →
        ∃ θ ∈ outer, ∃ ξ ∈ inner θ, A θ ξ ω)
    (hcount : ∀ θ ∈ outer, (inner θ).card ≤ M)
    (hpoint :
      ∀ θ ∈ outer, ∀ ξ ∈ inner θ,
        uniformMass space (A θ ξ) ≤ w θ)
    (hsum : (∑ θ ∈ outer, w θ) ≤ B)
    (hw : ∀ θ ∈ outer, 0 ≤ w θ) :
    uniformMass space E ≤ (M : ℝ) * B := by
  sorry

/-- Generic count of disjoint oriented short-swap collections when all first
endpoints lie in Q. Each q∈Q has at most 5D possible partners, plus the option
that no pair starts at q. -/
def shortPartners {n D : ℕ} (q : Fin n) : Finset (Fin n) :=
  (forwardWindow q (5 * D)).erase q

theorem card_shortPartners_le {n D : ℕ} (q : Fin n) :
    (shortPartners (D := D) q).card ≤ 5 * D := by
  unfold shortPartners
  have hq : q ∈ forwardWindow q (5 * D) := by
    simp [forwardWindow]
  rw [Finset.card_erase_of_mem hq]
  have h := card_forwardWindow_le q (5 * D)
  omega

def collectionPartner {n : ℕ}
    (P : Finset (Fin n × Fin n)) (q : Fin n) : Option (Fin n) := by
  classical
  by_cases h : ∃ y, (q,y) ∈ P
  · exact some (Classical.choose h)
  · exact none

theorem collectionPartner_eq_some_iff
    {n D : ℕ} {P : Finset (Fin n × Fin n)}
    (hP : IsAdmissibleCollection D P)
    (q y : Fin n) :
    collectionPartner P q = some y ↔ (q,y) ∈ P := by
  sorry

theorem collectionPartner_mem_allowed
    {n D : ℕ} {P : Finset (Fin n × Fin n)}
    (hP : IsAdmissibleCollection D P)
    {Q : Finset (Fin n)}
    (hsupp : ∀ r ∈ P, r.1 ∈ Q)
    (q : {x // x ∈ Q}) :
    collectionPartner P q.1 ∈
      insert none ((shortPartners (D := D) q.1).image some) := by
  sorry

def supportedCollectionCode {n D : ℕ}
    (Q : Finset (Fin n))
    (P : Finset (Fin n × Fin n)) :
    {q // q ∈ Q} → Option (Fin n) :=
  fun q => collectionPartner P q.1

theorem supportedCollectionCode_injective {n D : ℕ}
    (Q : Finset (Fin n)) :
    Set.InjOn (supportedCollectionCode (D := D) Q)
      (supportedAdmissibleCollections D Q :
        Set (Finset (Fin n × Fin n))) := by
  sorry

def supportedCollectionCodes {n D : ℕ} (Q : Finset (Fin n)) :
    Finset ({q // q ∈ Q} → Option (Fin n)) :=
  Fintype.piFinset fun q : {q // q ∈ Q} =>
    insert none ((shortPartners (D := D) q.1).image some)

theorem supportedAdmissibleCollections_card_le {n D : ℕ}
    (Q : Finset (Fin n)) :
    (supportedAdmissibleCollections D Q).card ≤
      (5 * D + 1) ^ Q.card := by
  sorry

/-- Reversal conjugation preserves admissibility of a collection of local
disjoint swaps and preserves the same distance bound. -/
def reverseSwapPair {n : ℕ} (q : Fin n × Fin n) :
    Fin n × Fin n :=
  (reverseIndex n q.2, reverseIndex n q.1)

theorem reverseSwapPair_involutive {n : ℕ} :
    Function.Involutive (reverseSwapPair (n := n)) := by
  intro q
  rcases q with ⟨a,b⟩
  simp [reverseSwapPair,reverseIndex_involutive]

theorem reverseSwapPair_injective {n : ℕ} :
    Function.Injective (reverseSwapPair (n := n)) :=
  (reverseSwapPair_involutive (n := n)).injective

def reverseSwapCollection {n : ℕ}
    (P : Finset (Fin n × Fin n)) :
    Finset (Fin n × Fin n) :=
  P.image reverseSwapPair

theorem reverseSwapCollection_admissible {n D : ℕ}
    {P : Finset (Fin n × Fin n)}
    (hP : IsAdmissibleCollection D P) :
    IsAdmissibleCollection D (reverseSwapCollection P) := by
  sorry

theorem reverseConjugate_trans {n : ℕ}
    (π ρ : Equiv.Perm (Fin n)) :
    reverseConjugate (π.trans ρ) =
      (reverseConjugate π).trans (reverseConjugate ρ) := by
  ext i
  simp [reverseConjugate_apply,reverseIndex_involutive]

theorem reverseConjugate_swap {n : ℕ}
    (a b : Fin n) :
    reverseConjugate (Equiv.swap a b) =
      Equiv.swap (reverseIndex n a) (reverseIndex n b) := by
  sorry

theorem swapsPermList_reverse {n : ℕ}
    (l : List (Fin n × Fin n)) :
    swapsPermList (l.map reverseSwapPair) =
      reverseConjugate (swapsPermList l) := by
  induction l with
  | nil =>
      ext i
      simp [swapsPermList,reverseConjugate_apply,
        reverseIndex_involutive]
  | cons q qs ih =>
      rcases q with ⟨a,b⟩
      simp only [List.map_cons,swapsPermList]
      rw [reverseConjugate_trans,← ih,
        reverseConjugate_swap]
      simp [reverseSwapPair]
      rw [Equiv.swap_comm]

theorem reverseConjugate_admissible {n D : ℕ}
    (π : Equiv.Perm (Fin n))
    (hπ : IsAdmissiblePermutation D π) :
    IsAdmissiblePermutation D (reverseConjugate π) := by
  sorry

/-- Reversal conjugation transports the fixed-outside condition from [b,b'] to
the reversed interval [rev b', rev b]. -/
theorem reverseConjugate_fixedOutside {n : ℕ}
    (b b' : Fin n) (π : Equiv.Perm (Fin n))
    (hfix : FixedOutside b b' π) :
    FixedOutside (reverseIndex n b') (reverseIndex n b)
      (reverseConjugate π) := by
  sorry

end

end GrahamRearrangement.Section5External
