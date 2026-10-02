module

public import GrahamRearrangement.Rearrangement.Parameters

@[expose] public section

open scoped BigOperators Pointwise

namespace GrahamRearrangement.Section5

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
  constructor
  · exact π.injective.comp hσ.1
  · intro x
    constructor
    · intro hx
      rw [← hπS] at hx
      rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
      rcases (hσ.2 y).1 hy with ⟨i, hi⟩
      exact ⟨i, by simp [applyValuePerm, hi]⟩
    · rintro ⟨i, rfl⟩
      have h : π (σ i) ∈ S.image π :=
        Finset.mem_image_of_mem π ((hσ.2 _).2 ⟨i, rfl⟩)
      rw [hπS] at h
      exact h

theorem indexImageSet_applyValuePerm
    {n p : ℕ} (π : Equiv.Perm (ZMod p))
    (σ : Fin n → ZMod p) (I : Finset (Fin n)) :
    indexImageSet (applyValuePerm π σ) I =
      (indexImageSet σ I).image π := by
  ext x
  simp [indexImageSet,applyValuePerm]

/-- Membership in the finite sample space of indexed orderings. -/
theorem mem_indexedOrderings_iff {p : ℕ} [NeZero p]
    {S : Finset (ZMod p)} {σ : Fin S.card → ZMod p} :
    σ ∈ indexedOrderings S ↔ IsIndexedOrdering S σ := by
  classical
  unfold indexedOrderings
  simp

theorem applyValuePerm_symm_apply {n p : ℕ}
    (π : Equiv.Perm (ZMod p)) (σ : Fin n → ZMod p) :
    applyValuePerm π.symm (applyValuePerm π σ) = σ := by
  funext i
  simp [applyValuePerm]

theorem applyValuePerm_apply_symm {n p : ℕ}
    (π : Equiv.Perm (ZMod p)) (σ : Fin n → ZMod p) :
    applyValuePerm π (applyValuePerm π.symm σ) = σ := by
  funext i
  simp [applyValuePerm]

theorem image_symm_of_image_eq {α : Type*} [DecidableEq α]
    (π : Equiv.Perm α) {A B : Finset α} (h : A.image π = B) :
    B.image π.symm = A := by
  rw [← h, Finset.image_image]
  simp

/-- A value permutation which preserves the sample space and carries one fiber
of a statistic into another (and whose inverse does the converse) shows that
the two fibers have the same size. -/
theorem card_fiber_eq_of_valuePerm {Γ : Type*} [DecidableEq Γ] {n p : ℕ}
    (Ω : Finset (Fin n → ZMod p)) (stat : (Fin n → ZMod p) → Γ)
    (π : Equiv.Perm (ZMod p)) (R R' : Γ)
    (hΩ : ∀ σ ∈ Ω, applyValuePerm π σ ∈ Ω)
    (hΩ' : ∀ σ ∈ Ω, applyValuePerm π.symm σ ∈ Ω)
    (hstat : ∀ σ ∈ Ω, stat σ = R → stat (applyValuePerm π σ) = R')
    (hstat' : ∀ σ ∈ Ω, stat σ = R' → stat (applyValuePerm π.symm σ) = R) :
    (Ω.filter fun σ => stat σ = R).card =
      (Ω.filter fun σ => stat σ = R').card := by
  apply Finset.card_nbij' (applyValuePerm π) (applyValuePerm π.symm)
  · intro σ hσ
    have hσ' := Finset.mem_filter.mp hσ
    exact Finset.mem_filter.mpr ⟨hΩ σ hσ'.1, hstat σ hσ'.1 hσ'.2⟩
  · intro σ hσ
    have hσ' := Finset.mem_filter.mp hσ
    exact Finset.mem_filter.mpr ⟨hΩ' σ hσ'.1, hstat' σ hσ'.1 hσ'.2⟩
  · intro σ _
    exact applyValuePerm_symm_apply π σ
  · intro σ _
    exact applyValuePerm_apply_symm π σ

theorem exposedImage_subset {p : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    {τ : Fin S.card → ZMod p} (hτ : IsIndexedOrdering S τ)
    (F : Finset (Fin S.card)) :
    indexImageSet τ F ⊆ S := by
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨i,hi,rfl⟩
  exact (hτ.2 _).2 ⟨i,rfl⟩

/-- An indexed ordering is injective, so the image of a set `F` of positions has `|F|` elements. -/
theorem exposed_image_card {p : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    {τ : Fin S.card → ZMod p} (hτ : IsIndexedOrdering S τ)
    (F : Finset (Fin S.card)) :
    (indexImageSet τ F).card = F.card := by
  unfold indexImageSet
  exact Finset.card_image_of_injective _ hτ.1

theorem unexposed_indexImage_subset_remaining
    {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (τ σ : Fin S.card → ZMod p)
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

/-- A value permutation preserving the unexposed values and fixing everything
else maps the conditional sample space into itself. -/
theorem valuePerm_mem_agreeSpace {p : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    (τ : Fin S.card → ZMod p)
    (F : Finset (Fin S.card))
    (π : Equiv.Perm (ZMod p))
    (hπT : (S \ indexImageSet τ F).image π = S \ indexImageSet τ F)
    (hπout : ∀ x ∉ S \ indexImageSet τ F, π x = x)
    {σ : Fin S.card → ZMod p}
    (hσ : σ ∈ (indexedOrderings S).filter fun σ => AgreesOn F σ τ) :
    applyValuePerm π σ ∈
      (indexedOrderings S).filter fun σ => AgreesOn F σ τ := by
  classical
  have hσ' := Finset.mem_filter.mp hσ
  have hσord : IsIndexedOrdering S σ := mem_indexedOrderings_iff.mp hσ'.1
  have hfix : ∀ x ∈ indexImageSet τ F, π x = x := by
    intro x hx
    apply hπout x
    intro hxT
    exact (Finset.mem_sdiff.mp hxT).2 hx
  have hsub : S.image π ⊆ S := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hxS, rfl⟩
    by_cases hxE : x ∈ indexImageSet τ F
    · rw [hfix x hxE]
      exact hxS
    · have hxT : x ∈ S \ indexImageSet τ F := Finset.mem_sdiff.mpr ⟨hxS, hxE⟩
      have hπx : π x ∈ (S \ indexImageSet τ F).image π :=
        Finset.mem_image_of_mem π hxT
      rw [hπT] at hπx
      exact (Finset.mem_sdiff.mp hπx).1
  have hπS : S.image π = S := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [Finset.card_image_of_injective _ π.injective]
  exact Finset.mem_filter.mpr
    ⟨mem_indexedOrderings_iff.mpr
        (applyValuePerm_isIndexedOrdering S π hπS hσord),
      valuePerm_preserves_agreement S τ σ F π hfix hσ'.2⟩

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
  classical
  set Ω := (indexedOrderings S).filter fun σ => AgreesOn F σ τ with hΩdef
  set T := S \ indexImageSet τ F with hTdef
  have hτΩ : τ ∈ Ω :=
    Finset.mem_filter.mpr ⟨mem_indexedOrderings_iff.mpr hτ, fun _ _ => rfl⟩
  have hmap : ∀ σ ∈ Ω, indexImageSet σ J ∈ T.powersetCard J.card := by
    intro σ hσ
    have hσ' := Finset.mem_filter.mp hσ
    have hσord : IsIndexedOrdering S σ := mem_indexedOrderings_iff.mp hσ'.1
    apply Finset.mem_powersetCard.mpr
    exact ⟨unexposed_indexImage_subset_remaining S τ σ hσord F J hσ'.2 hdisj,
      Finset.card_image_of_injective _ hσord.1⟩
  have heq : ∀ R ∈ T.powersetCard J.card, ∀ R' ∈ T.powersetCard J.card,
      (Ω.filter fun σ => indexImageSet σ J = R).card =
        (Ω.filter fun σ => indexImageSet σ J = R').card := by
    intro R hR R' hR'
    obtain ⟨π, hπR, hπT, hπout⟩ := exists_perm_maps_finset T R R'
      (Finset.mem_powersetCard.mp hR).1 (Finset.mem_powersetCard.mp hR').1
      (by rw [(Finset.mem_powersetCard.mp hR).2,
        (Finset.mem_powersetCard.mp hR').2])
    apply card_fiber_eq_of_valuePerm Ω (fun σ => indexImageSet σ J) π R R'
    · intro σ hσ
      exact valuePerm_mem_agreeSpace S τ F π hπT hπout hσ
    · intro σ hσ
      exact valuePerm_mem_agreeSpace S τ F π.symm
        (image_symm_of_image_eq π hπT)
        (fun x hx => perm_symm_fixes_of_fixes π (hπout x hx)) hσ
    · intro σ _ h
      rw [indexImageSet_applyValuePerm, h, hπR]
    · intro σ _ h
      rw [indexImageSet_applyValuePerm, h, image_symm_of_image_eq π hπR]
  unfold orderingConditionalMass uniformConditionalMass
  exact uniformMass_statistic_of_pairwise_equal_fibers Ω (T.powersetCard J.card)
    (fun σ => indexImageSet σ J) hmap ⟨_, hmap τ hτΩ⟩ ⟨τ, hτΩ⟩ heq E

/-- Agreement on the empty set of positions is no condition at all. -/
theorem agreeSpace_empty {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (τ : Fin S.card → ZMod p) :
    ((indexedOrderings S).filter fun σ => AgreesOn ∅ σ τ) =
      indexedOrderings S := by
  apply Finset.filter_true_of_mem
  intro σ _ i hi
  simp at hi

theorem fixedIndexSet_image_uniform {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (I : Finset (Fin S.card))
    (E : Finset (ZMod p) → Prop) [DecidablePred E] :
    orderingEventMass S (fun σ => E (indexImageSet σ I)) =
      uniformMass (S.powersetCard I.card) E := by
  classical
  obtain ⟨τ, hτmem⟩ := indexedOrderings_nonempty S
  have hτ : IsIndexedOrdering S τ := mem_indexedOrderings_iff.mp hτmem
  have h := conditional_fixedIndexSet_image_uniform S τ hτ ∅ I
    (Finset.disjoint_empty_left I) E
  unfold orderingConditionalMass uniformConditionalMass at h
  rw [agreeSpace_empty] at h
  have hS : S \ indexImageSet τ ∅ = S := by simp [indexImageSet]
  rw [hS] at h
  exact h

theorem conditional_fixedIndexSet_sumMass
    {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (τ : Fin S.card → ZMod p) (hτ : IsIndexedOrdering S τ)
    (F J : Finset (Fin S.card)) (hdisj : Disjoint F J)
    (z : ZMod p) :
    orderingConditionalMass S
      (fun σ => AgreesOn F σ τ)
      (fun σ => indexSetSum σ J = z) =
    sliceMass (S \ indexImageSet τ F) J.card z := by
  rw [sliceMass, ← conditional_fixedIndexSet_image_uniform
      S τ hτ F J hdisj (fun R => subsetSum R = z)]
  unfold orderingConditionalMass uniformConditionalMass
  apply uniformMass_congr
  intro σ hσ
  have hσord : IsIndexedOrdering S σ :=
    mem_indexedOrderings_iff.mp (Finset.mem_filter.mp hσ).1
  rw [indexSetSum_eq_subsetSum_image hσord.1 J]

/-- The image of a fixed r-set of indices under a uniform bijection is a
uniform r-subset of S. -/
theorem fixedIndexSet_sumMass {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (I : Finset (Fin S.card))
    (z : ZMod p) :
    orderingEventMass S (fun σ => indexSetSum σ I = z) =
      sliceMass S I.card z := by
  rw [sliceMass, ← fixedIndexSet_image_uniform S I
      (fun R => subsetSum R = z)]
  unfold orderingEventMass
  apply uniformMass_congr
  intro σ hσmem
  have hσ : IsIndexedOrdering S σ := mem_indexedOrderings_iff.mp hσmem
  rw [indexSetSum_eq_subsetSum_image hσ.1 I]

/-- Composition with a permutation of positions preserves being an indexed
ordering. -/
theorem isIndexedOrdering_applyPositionPerm
    {p : ℕ} {S : Finset (ZMod p)}
    {σ : Fin S.card → ZMod p}
    (hσ : IsIndexedOrdering S σ)
    (π : Equiv.Perm (Fin S.card)) :
    IsIndexedOrdering S (applyPositionPerm σ π) := by
  constructor
  · intro i j hij
    exact π.injective (hσ.1 hij)
  · intro x
    rw [hσ.2]
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨π.symm j, by simpa [applyPositionPerm] using hj⟩
    · rintro ⟨i, hi⟩
      exact ⟨π i, by simpa [applyPositionPerm] using hi⟩

theorem applyPositionPerm_apply_symm {n p : ℕ}
    (σ : Fin n → ZMod p) (π : Equiv.Perm (Fin n)) :
    applyPositionPerm (applyPositionPerm σ π.symm) π = σ := by
  funext i
  simp [applyPositionPerm]

theorem applyPositionPerm_symm_apply {n p : ℕ}
    (σ : Fin n → ZMod p) (π : Equiv.Perm (Fin n)) :
    applyPositionPerm (applyPositionPerm σ π) π.symm = σ := by
  funext i
  simp [applyPositionPerm]

/-- Composition by a fixed permutation of positions preserves the uniform law. -/
theorem ordering_perm_invariant {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (π : Equiv.Perm (Fin S.card))
    (E : (Fin S.card → ZMod p) → Prop) [DecidablePred E] :
    orderingEventMass S E =
      orderingEventMass S (fun σ => E (applyPositionPerm σ π)) := by
  unfold orderingEventMass
  apply uniformMass_bij (indexedOrderings S) (indexedOrderings S)
    (fun σ => applyPositionPerm σ π.symm)
  · intro σ hσ
    exact mem_indexedOrderings_iff.mpr
      (isIndexedOrdering_applyPositionPerm (mem_indexedOrderings_iff.mp hσ) π.symm)
  · intro σ _ τ _ h
    have h' := congrArg (fun ρ => applyPositionPerm ρ π) h
    simpa only [applyPositionPerm_apply_symm] using h'
  · intro τ hτ
    exact ⟨applyPositionPerm τ π, mem_indexedOrderings_iff.mpr
      (isIndexedOrdering_applyPositionPerm (mem_indexedOrderings_iff.mp hτ) π),
      applyPositionPerm_symm_apply τ π⟩
  · intro σ _
    rw [applyPositionPerm_apply_symm]

/-- Conditional version of the preceding invariance. -/
theorem ordering_conditional_perm_invariant {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (π : Equiv.Perm (Fin S.card))
    (cond event : (Fin S.card → ZMod p) → Prop)
    [DecidablePred cond] [DecidablePred event] :
    orderingConditionalMass S cond event =
      orderingConditionalMass S
        (fun σ => cond (applyPositionPerm σ π))
        (fun σ => event (applyPositionPerm σ π)) := by
  unfold orderingConditionalMass uniformConditionalMass
  apply uniformMass_bij _ _ (fun σ => applyPositionPerm σ π.symm)
  · intro σ hσ
    have hσ' := Finset.mem_filter.mp hσ
    refine Finset.mem_filter.mpr ⟨mem_indexedOrderings_iff.mpr
      (isIndexedOrdering_applyPositionPerm (mem_indexedOrderings_iff.mp hσ'.1) π.symm),
      ?_⟩
    simp only [applyPositionPerm_apply_symm]
    exact hσ'.2
  · intro σ _ τ _ h
    have h' := congrArg (fun ρ => applyPositionPerm ρ π) h
    simpa only [applyPositionPerm_apply_symm] using h'
  · intro τ hτ
    have hτ' := Finset.mem_filter.mp hτ
    exact ⟨applyPositionPerm τ π, Finset.mem_filter.mpr ⟨mem_indexedOrderings_iff.mpr
      (isIndexedOrdering_applyPositionPerm (mem_indexedOrderings_iff.mp hτ'.1) π), hτ'.2⟩,
      applyPositionPerm_symm_apply τ π⟩
  · intro σ _
    simp only [applyPositionPerm_apply_symm]

/-- A uniformly random one-element subset of a nonempty set `T` has sum `z` with
probability at most `1/|T|`. -/
theorem sliceMass_one_le_inv_card {p : ℕ} [NeZero p]
    (T : Finset (ZMod p)) (hT : T.Nonempty) (z : ZMod p) :
    sliceMass T 1 z ≤ 1 / (T.card : ℝ) := by
  classical
  unfold sliceMass uniformMass
  have hden : (0 : ℝ) < T.card := by exact_mod_cast hT.card_pos
  have hsub : (T.powersetCard 1).filter (fun R => subsetSum R = z) ⊆ {{z}} := by
    intro R hR
    rcases Finset.mem_filter.mp hR with ⟨hpow, hsum⟩
    rcases Finset.card_eq_one.mp (Finset.mem_powersetCard.mp hpow).2 with ⟨x, rfl⟩
    have hxz : x = z := by simpa [subsetSum] using hsum
    subst hxz
    simp
  have hnum : ((T.powersetCard 1).filter fun R => subsetSum R = z).card ≤ 1 :=
    le_trans (Finset.card_le_card hsub) (by simp)
  rw [Finset.card_powersetCard, Nat.choose_one_right]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hnum) hden.le

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
  unfold orderingConditionalMass uniformConditionalMass
  calc
    _ ≤ ∑ a ∈ A,
          uniformMass ((indexedOrderings S).filter
            (fun σ => AgreesOn F σ τ))
            (fun σ => indexSetSum σ (I a) = z a) := by
        convert uniformMass_exists_le_sum _ A (fun a σ => indexSetSum σ (I a) = z a)
    _ = _ := by
        apply Finset.sum_congr rfl
        intro a ha
        have h := conditional_fixedIndexSet_sumMass S τ hτ F (I a) (hdisj a ha) (z a)
        unfold orderingConditionalMass uniformConditionalMass at h
        exact h

theorem partition_member_unique
    {α : Type*} [DecidableEq α] {k : ℕ}
    (Δ : Fin (k + 1) → Finset α)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Δ i) (Δ j))
    {x : α}
    {i j : Fin (k + 1)} (hxi : x ∈ Δ i) (hxj : x ∈ Δ j) :
    i = j := by
  by_contra hij
  exact Finset.disjoint_left.mp (hdisj i j hij) hxi hxj

/-- Two nested chains with the same cardinality vector are carried to one
another by a permutation of the ground set, obtained by matching the disjoint
increment layers. -/
theorem exists_value_perm_maps_chain
    {p k : ℕ} [NeZero p]
    (T : Finset (ZMod p)) (m : Fin k → ℕ)
    {R R' : Fin k → Finset (ZMod p)}
    (hR : R ∈ chainFamily T m) (hR' : R' ∈ chainFamily T m) :
    ∃ π : Equiv.Perm (ZMod p),
      T.image π = T ∧
      (∀ x ∉ T, π x = x) ∧
      ∀ i, (R i).image π = R' i := by
  classical
  have hRd := (Finset.mem_filter.mp hR).2
  have hR'd := (Finset.mem_filter.mp hR').2
  obtain ⟨π, hπT, hπR, hπout⟩ := exists_perm_maps_nested_family T k R R'
    (fun i => (hRd.1 i).1) (fun i => (hR'd.1 i).1) hRd.2 hR'd.2
    (fun i => by rw [(hRd.1 i).2, (hR'd.1 i).2])
  exact ⟨π, hπT, hπout, hπR⟩

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
  classical
  set Ω := (indexedOrderings S).filter fun σ => AgreesOn F σ τ with hΩdef
  set T := S \ indexImageSet τ F with hTdef
  let stat : (Fin S.card → ZMod p) → Fin k → Finset (ZMod p) :=
    fun σ i => indexImageSet σ (I i)
  have hτΩ : τ ∈ Ω :=
    Finset.mem_filter.mpr ⟨mem_indexedOrderings_iff.mpr hτ, fun _ _ => rfl⟩
  have hmap : ∀ σ ∈ Ω, stat σ ∈ chainFamily T m := by
    intro σ hσ
    have hσ' := Finset.mem_filter.mp hσ
    have hσord : IsIndexedOrdering S σ := mem_indexedOrderings_iff.mp hσ'.1
    unfold chainFamily
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i => ⟨?_, ?_⟩,
      fun i j hij => ?_⟩
    · exact unexposed_indexImage_subset_remaining S τ σ hσord F (I i) hσ'.2
        (hdisj i)
    · rw [← hcard i]
      exact Finset.card_image_of_injective _ hσord.1
    · exact Finset.image_subset_image (hnested i j hij)
  have heq : ∀ R ∈ chainFamily T m, ∀ R' ∈ chainFamily T m,
      (Ω.filter fun σ => stat σ = R).card =
        (Ω.filter fun σ => stat σ = R').card := by
    intro R hR R' hR'
    have hRd := (Finset.mem_filter.mp hR).2
    have hR'd := (Finset.mem_filter.mp hR').2
    obtain ⟨π, hπT, hπR, hπout⟩ := exists_perm_maps_nested_family T k R R'
      (fun i => (hRd.1 i).1) (fun i => (hR'd.1 i).1) hRd.2 hR'd.2
      (fun i => by rw [(hRd.1 i).2, (hR'd.1 i).2])
    apply card_fiber_eq_of_valuePerm Ω stat π R R'
    · intro σ hσ
      exact valuePerm_mem_agreeSpace S τ F π hπT hπout hσ
    · intro σ hσ
      exact valuePerm_mem_agreeSpace S τ F π.symm
        (image_symm_of_image_eq π hπT)
        (fun x hx => perm_symm_fixes_of_fixes π (hπout x hx)) hσ
    · intro σ _ h
      funext i
      have hi := congrFun h i
      simp only [stat] at hi ⊢
      rw [indexImageSet_applyValuePerm, hi, hπR]
    · intro σ _ h
      funext i
      have hi := congrFun h i
      simp only [stat] at hi ⊢
      rw [indexImageSet_applyValuePerm, hi, image_symm_of_image_eq π (hπR i)]
  have huniform := uniformMass_statistic_of_pairwise_equal_fibers Ω (chainFamily T m)
    stat hmap ⟨_, hmap τ hτΩ⟩ ⟨τ, hτΩ⟩ heq (fun R => ∀ i, subsetSum (R i) = z i)
  unfold orderingConditionalMass uniformConditionalMass chainMass
  rw [← huniform]
  apply uniformMass_congr
  intro σ hσ
  have hσord : IsIndexedOrdering S σ :=
    mem_indexedOrderings_iff.mp (Finset.mem_filter.mp hσ).1
  simp only [stat, indexSetSum_eq_subsetSum_image hσord.1]

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

/-- Fibers of the agreement key are exactly agreement classes. -/
theorem filter_agreementKey_eq {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (F : Finset (Fin S.card))
    (space : Finset (Fin S.card → ZMod p))
    (τ : Fin S.card → ZMod p) :
    (space.filter fun σ => agreementKey F σ = agreementKey F τ) =
      space.filter fun σ => AgreesOn F σ τ := by
  apply Finset.filter_congr
  intro σ _
  exact agreementKey_eq_iff F σ τ

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
  classical
  obtain ⟨τ₀, hτ₀mem⟩ := indexedOrderings_nonempty S
  have hq0 : 0 ≤ q :=
    le_trans (uniformMass_nonneg _ _) (hfiber τ₀ (mem_indexedOrderings_iff.mp hτ₀mem))
  have h := uniformConditionalMass_le_of_fibers (indexedOrderings S) (agreementKey F)
    (fun _ => True) E q hq0 (by
      intro κ _
      by_cases hnon :
          ((indexedOrderings S).filter fun σ => agreementKey F σ = κ).Nonempty
      · obtain ⟨τ, hτfib⟩ := hnon
        have hτ' := Finset.mem_filter.mp hτfib
        have hτ : IsIndexedOrdering S τ := mem_indexedOrderings_iff.mp hτ'.1
        unfold uniformConditionalMass
        rw [← hτ'.2, filter_agreementKey_eq]
        exact hfiber τ hτ
      · unfold uniformConditionalMass
        rw [Finset.not_nonempty_iff_eq_empty.mp hnon]
        simp [uniformMass, hq0])
  unfold uniformConditionalMass at h
  unfold orderingEventMass
  rw [Finset.filter_true_of_mem (fun _ _ => trivial)] at h
  exact h

/-- Fiber multiplication specialized to exposing a set of positions in a
uniform random ordering.

The hypothesis `0 ≤ b` is needed: if `A` never occurs then `hfiber` is vacuous,
the left side is `0`, and `a * b` would be negative for `a > 0 > b`.  When it is
omitted it is discharged by `positivity`. -/
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
          (fun σ => AgreesOn F σ τ) B ≤ b)
    (hb : 0 ≤ b := by positivity) :
    orderingEventMass S (fun σ => A σ ∧ B σ) ≤ a * b := by
  classical
  have ha0 : 0 ≤ a := le_trans (uniformMass_nonneg _ _) hA
  unfold orderingEventMass at hA ⊢
  rw [uniformMass_chain_rule]
  have hcond : uniformConditionalMass (indexedOrderings S) A B ≤ b := by
    set spaceA := (indexedOrderings S).filter A with hspaceA
    have htotal := uniformConditionalMass_le_of_fibers spaceA (agreementKey F)
      (fun _ => True) B b hb (by
        intro κ _
        by_cases hnon : (spaceA.filter fun σ => agreementKey F σ = κ).Nonempty
        · obtain ⟨τ, hτfib⟩ := hnon
          have hτ' := Finset.mem_filter.mp hτfib
          have hτA := Finset.mem_filter.mp hτ'.1
          have hτ : IsIndexedOrdering S τ := mem_indexedOrderings_iff.mp hτA.1
          unfold uniformConditionalMass
          rw [← hτ'.2, filter_agreementKey_eq]
          have hset : (spaceA.filter fun σ => AgreesOn F σ τ) =
              (indexedOrderings S).filter fun σ => AgreesOn F σ τ := by
            ext σ
            simp only [hspaceA, Finset.mem_filter]
            constructor
            · rintro ⟨⟨h1, _⟩, h3⟩
              exact ⟨h1, h3⟩
            · rintro ⟨h1, h3⟩
              exact ⟨⟨h1, (hdetermined σ τ h3).2 hτA.2⟩, h3⟩
          rw [hset]
          exact hfiber τ hτ hτA.2
        · unfold uniformConditionalMass
          rw [Finset.not_nonempty_iff_eq_empty.mp hnon]
          simp [uniformMass, hb])
    unfold uniformConditionalMass at htotal ⊢
    rw [Finset.filter_true_of_mem (fun _ _ => trivial)] at htotal
    exact htotal
  exact mul_le_mul hA hcond (uniformMass_nonneg _ _) ha0

/-- Distinct index subsets: the case where some index lies in `J` but not in
`J'`.  Expose all other positions of the window; the remaining value is uniform
on the unexposed values, and exactly one of them makes the sums equal. -/
theorem distinct_index_subset_sums_mass_le_aux {p : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    (W J J' : Finset (Fin S.card))
    (hJ : J ⊆ W) (hJ' : J' ⊆ W)
    {i : Fin S.card} (hiJ : i ∈ J) (hiJ' : i ∉ J')
    (hWcard : W.card ≤ S.card) :
    orderingEventMass S (fun σ => indexSetSum σ J = indexSetSum σ J') ≤
      1 / ((S.card - W.card + 1 : ℕ) : ℝ) := by
  classical
  have hiW : i ∈ W := hJ hiJ
  have hWpos : 0 < W.card := Finset.card_pos.mpr ⟨i, hiW⟩
  apply event_le_of_agreesOn_fibers S (W.erase i)
  intro τ hτ
  have hTcard : (S \ indexImageSet τ (W.erase i)).card = S.card - W.card + 1 := by
    rw [Finset.card_sdiff_of_subset (exposedImage_subset S hτ _),
      exposed_image_card S hτ, Finset.card_erase_of_mem hiW]
    omega
  have hdisj : Disjoint (W.erase i) {i} := by simp
  have hJer : J.erase i ⊆ W.erase i := Finset.erase_subset_erase i hJ
  have hJ'F : J' ⊆ W.erase i := fun x hx =>
    Finset.mem_erase.mpr ⟨fun h => hiJ' (h ▸ hx), hJ' hx⟩
  calc
    orderingConditionalMass S (fun σ => AgreesOn (W.erase i) σ τ)
        (fun σ => indexSetSum σ J = indexSetSum σ J')
      = orderingConditionalMass S (fun σ => AgreesOn (W.erase i) σ τ)
          (fun σ => indexSetSum σ {i} =
            indexSetSum τ J' - indexSetSum τ (J.erase i)) := by
        unfold orderingConditionalMass uniformConditionalMass
        apply uniformMass_congr
        intro σ hσ
        have hagr := (Finset.mem_filter.mp hσ).2
        have h1 : indexSetSum σ J = σ i + indexSetSum τ (J.erase i) := by
          rw [← indexSetSum_eq_of_agreesOn hagr hJer]
          unfold indexSetSum
          rw [Finset.add_sum_erase J σ hiJ]
        have h2 : indexSetSum σ J' = indexSetSum τ J' :=
          indexSetSum_eq_of_agreesOn hagr hJ'F
        have h3 : indexSetSum σ {i} = σ i := by simp [indexSetSum]
        rw [h1, h2, h3]
        constructor
        · intro h
          linear_combination h
        · intro h
          linear_combination h
    _ = sliceMass (S \ indexImageSet τ (W.erase i)) 1
          (indexSetSum τ J' - indexSetSum τ (J.erase i)) := by
        rw [conditional_fixedIndexSet_sumMass S τ hτ (W.erase i) {i} hdisj,
          Finset.card_singleton]
    _ ≤ 1 / ((S \ indexImageSet τ (W.erase i)).card : ℝ) :=
        sliceMass_one_le_inv_card _ (Finset.card_pos.mp (by omega)) _
    _ = 1 / ((S.card - W.card + 1 : ℕ) : ℝ) := by rw [hTcard]

theorem distinct_index_subset_sums_mass_le {p : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    (W J J' : Finset (Fin S.card))
    (hJ : J ⊆ W) (hJ' : J' ⊆ W) (hne : J ≠ J')
    (hW : W.card ≤ S.card) :
    orderingEventMass S (fun σ => indexSetSum σ J = indexSetSum σ J') ≤
      1 / ((S.card - W.card + 1 : ℕ) : ℝ) := by
  classical
  by_cases h : J ⊆ J'
  · have hex : ∃ i ∈ J', i ∉ J := by
      by_contra h'
      simp only [not_exists, not_and, not_not] at h'
      exact hne (Finset.Subset.antisymm h h')
    obtain ⟨i, hiJ', hiJ⟩ := hex
    have hsym := distinct_index_subset_sums_mass_le_aux S W J' J hJ' hJ hiJ' hiJ hW
    unfold orderingEventMass at hsym ⊢
    rw [uniformMass_congr (indexedOrderings S)
      (fun σ => indexSetSum σ J = indexSetSum σ J')
      (fun σ => indexSetSum σ J' = indexSetSum σ J) (fun σ _ => eq_comm)]
    exact hsym
  · obtain ⟨i, hiJ, hiJ'⟩ := Finset.not_subset.mp h
    exact distinct_index_subset_sums_mass_le_aux S W J J' hJ hJ' hiJ hiJ' hW

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
  calc
    uniformMass space E
      ≤ uniformMass space (fun ω => ∃ θ ∈ params, A θ ω) :=
        uniformMass_mono_on space _ _ hcover
    _ ≤ ∑ θ ∈ params, uniformMass space (A θ) :=
        finite_parameter_union_bound space params A
    _ ≤ ∑ _θ ∈ params, q := Finset.sum_le_sum hbound
    _ = (params.card : ℝ) * q := by simp

/-- More than D bad right endpoints in a symmetric window of radius 10D yield a
least point b₀ and D further distinct points in the following 20D window. -/
theorem dense_window_extract {n D : ℕ}
    (B : Finset (Fin n)) (hD : 0 < D)
    (h : ∃ z : Fin n,
      D < (B ∩ symmetricWindow z (10 * D)).card) :
    ∃ b₀ ∈ B, ∃ b : Fin D → Fin n,
      Function.Injective b ∧
      (∀ i, b i ∈ B) ∧
      (∀ i, paperPos b₀ < paperPos (b i) ∧
        paperPos (b i) ≤ paperPos b₀ + 20 * D) := by
  classical
  obtain ⟨z, hz⟩ := h
  set T := B ∩ symmetricWindow z (10 * D) with hTdef
  have hT : T.Nonempty := Finset.card_pos.mp (lt_trans hD hz)
  have hb₀T : T.min' hT ∈ T := T.min'_mem hT
  have hUcard : D ≤ (T.erase (T.min' hT)).card := by
    rw [Finset.card_erase_of_mem hb₀T]
    omega
  obtain ⟨b, hbinj, hbU⟩ := exists_injective_fin_enum (T.erase (T.min' hT)) D hUcard
  refine ⟨T.min' hT, (Finset.mem_inter.mp hb₀T).1, b, hbinj,
    fun i => (Finset.mem_inter.mp (Finset.mem_of_mem_erase (hbU i))).1, ?_⟩
  intro i
  have hbiT : b i ∈ T := Finset.mem_of_mem_erase (hbU i)
  have hbine : b i ≠ T.min' hT := Finset.ne_of_mem_erase (hbU i)
  have hlt : T.min' hT < b i := lt_of_le_of_ne (T.min'_le _ hbiT) (Ne.symm hbine)
  have hb0W := (Finset.mem_inter.mp hb₀T).2
  have hbiW := (Finset.mem_inter.mp hbiT).2
  simp only [symmetricWindow, Finset.mem_filter, Finset.mem_univ, true_and] at hb0W hbiW
  unfold Nat.dist at hb0W hbiW
  have hlt' : (T.min' hT).val < (b i).val := hlt
  unfold paperPos
  omega

theorem disjoint_swaps_commute_general {α : Type*} [DecidableEq α]
    (a b c d : α)
    (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) :
    (Equiv.swap a b).trans (Equiv.swap c d) =
      (Equiv.swap c d).trans (Equiv.swap a b) := by
  ext x
  simp only [Equiv.trans_apply, Equiv.swap_apply_def]
  split_ifs <;> simp_all

theorem disjoint_swaps_commute {α : Type*} [DecidableEq α]
    (a b c d : α)
    (_hab : a ≠ b) (_hcd : c ≠ d)
    (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) :
    (Equiv.swap a b).trans (Equiv.swap c d) =
      (Equiv.swap c d).trans (Equiv.swap a b) :=
  disjoint_swaps_commute_general a b c d hac had hbc hbd

/-- A composition of swaps fixes every point lying outside all of the swapped
pairs. -/
theorem swapsPermList_apply_eq_self_of_forall_ne {α : Type*} [DecidableEq α]
    (l : List (α × α)) (i : α)
    (hi : ∀ q ∈ l, i ≠ q.1 ∧ i ≠ q.2) :
    swapsPermList l i = i := by
  induction l with
  | nil => rfl
  | cons q qs ih =>
      have hq := hi q (by simp)
      simp only [swapsPermList, Equiv.trans_apply]
      rw [Equiv.swap_apply_of_ne_of_ne hq.1 hq.2]
      exact ih (fun r hr => hi r (by simp [hr]))

theorem disjoint_swaps_fix_outside_support
    {α : Type*} [DecidableEq α]
    (P : Finset (α × α))
    (_hP : (↑P : Set (α × α)).Pairwise fun q r =>
      q.1 ≠ r.1 ∧ q.1 ≠ r.2 ∧ q.2 ≠ r.1 ∧ q.2 ≠ r.2)
    (i : α)
    (hi : ∀ q ∈ P, i ≠ q.1 ∧ i ≠ q.2) :
    swapsPermList P.toList i = i :=
  swapsPermList_apply_eq_self_of_forall_ne P.toList i
    (fun q hq => hi q (Finset.mem_toList.mp hq))

theorem nodup_lists_perm_of_toFinset_eq {α : Type*} [DecidableEq α]
    {l r : List α} (hl : l.Nodup) (hr : r.Nodup)
    (hset : l.toFinset = r.toFinset) :
    l.Perm r := by
  apply (List.perm_ext_iff_of_nodup hl hr).2
  intro x
  rw [← List.mem_toFinset, hset, List.mem_toFinset]

theorem swapsPermList_eq_of_perm_pairwise
    {α : Type*} [DecidableEq α]
    {l r : List (α × α)}
    (hp : l.Perm r)
    (hpair : (↑l.toFinset : Set (α × α)).Pairwise fun q s =>
      q.1 ≠ s.1 ∧ q.1 ≠ s.2 ∧ q.2 ≠ s.1 ∧ q.2 ≠ s.2) :
    swapsPermList l = swapsPermList r := by
  revert hpair
  induction hp with
  | nil => intro _; rfl
  | @cons a l₁ l₂ _ ih =>
      intro hpair
      have hsub : (↑l₁.toFinset : Set (α × α)).Pairwise fun q s =>
          q.1 ≠ s.1 ∧ q.1 ≠ s.2 ∧ q.2 ≠ s.1 ∧ q.2 ≠ s.2 :=
        hpair.mono (by
          rw [List.toFinset_cons, Finset.coe_insert]
          exact Set.subset_insert _ _)
      simp only [swapsPermList]
      rw [ih hsub]
  | swap x y l =>
      intro hpair
      by_cases hxy : y = x
      · subst hxy
        rfl
      have hd := hpair (by simp) (by simp) hxy
      have hcomm := disjoint_swaps_commute_general
        y.1 y.2 x.1 x.2 hd.1 hd.2.1 hd.2.2.1 hd.2.2.2
      simp only [swapsPermList]
      rw [← Equiv.trans_assoc, hcomm, Equiv.trans_assoc]
  | trans h₁ _ ih₁ ih₂ =>
      intro hpair
      have hset := List.toFinset_eq_of_perm _ _ h₁
      exact (ih₁ hpair).trans (ih₂ (by rw [← hset]; exact hpair))

theorem disjoint_swaps_order_independent
    {α : Type*} [DecidableEq α]
    (P : Finset (α × α))
    (hP : (↑P : Set (α × α)).Pairwise fun q r =>
      q.1 ≠ r.1 ∧ q.1 ≠ r.2 ∧ q.2 ≠ r.1 ∧ q.2 ≠ r.2)
    (l : List (α × α)) (hl : l.toFinset = P) (hln : l.Nodup) :
    swapsPermList l = swapsPermList P.toList := by
  have hp := nodup_lists_perm_of_toFinset_eq hln P.nodup_toList
    (by simp [hl])
  apply swapsPermList_eq_of_perm_pairwise hp
  simpa [hl] using hP

theorem swapsPermList_pair_action
    {α : Type*} [LinearOrder α] [DecidableEq α]
    (P : Finset (α × α))
    (hPpair : (↑P : Set (α × α)).Pairwise fun q r =>
      q.1 ≠ r.1 ∧ q.1 ≠ r.2 ∧ q.2 ≠ r.1 ∧ q.2 ≠ r.2)
    {q : α × α} (hq : q ∈ P) :
    swapsPermList P.toList q.1 = q.2 ∧
      swapsPermList P.toList q.2 = q.1 := by
  have hln : (q :: (P.erase q).toList).Nodup := by
    refine List.nodup_cons.mpr ⟨?_, (P.erase q).nodup_toList⟩
    rw [Finset.mem_toList]
    exact Finset.notMem_erase q P
  have hset : (q :: (P.erase q).toList).toFinset = P := by
    rw [List.toFinset_cons, Finset.toList_toFinset, Finset.insert_erase hq]
  have horder := disjoint_swaps_order_independent P hPpair _ hset hln
  have hrest : ∀ r ∈ (P.erase q).toList,
      (q.1 ≠ r.1 ∧ q.1 ≠ r.2) ∧ (q.2 ≠ r.1 ∧ q.2 ≠ r.2) := by
    intro r hr
    rw [Finset.mem_toList] at hr
    have hd := hPpair hq (Finset.mem_of_mem_erase hr)
      (Ne.symm (Finset.ne_of_mem_erase hr))
    exact ⟨⟨hd.1, hd.2.1⟩, ⟨hd.2.2.1, hd.2.2.2⟩⟩
  have hfix1 : swapsPermList (P.erase q).toList q.1 = q.1 :=
    swapsPermList_apply_eq_self_of_forall_ne _ _ (fun r hr => (hrest r hr).1)
  have hfix2 : swapsPermList (P.erase q).toList q.2 = q.2 :=
    swapsPermList_apply_eq_self_of_forall_ne _ _ (fun r hr => (hrest r hr).2)
  rw [← horder]
  simp only [swapsPermList, Equiv.trans_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_right]
  exact ⟨hfix2, hfix1⟩

/-- If a point is moved by a composition of swaps, it lies in one of the
swapped pairs. -/
theorem exists_pair_of_swapsPermList_ne
    {α : Type*} [DecidableEq α]
    (P : Finset (α × α)) {x : α}
    (hx : swapsPermList P.toList x ≠ x) :
    ∃ r ∈ P, x = r.1 ∨ x = r.2 := by
  by_contra hnone
  simp only [not_exists, not_and, not_or] at hnone
  exact hx (swapsPermList_apply_eq_self_of_forall_ne P.toList x
    (fun r hr => hnone r (Finset.mem_toList.mp hr)))

/-- One inclusion of the reconstruction statement. -/
theorem disjoint_swaps_reconstruct_subset
    {α : Type*} [LinearOrder α] [DecidableEq α]
    (P Q : Finset (α × α))
    (hPpair : (↑P : Set (α × α)).Pairwise fun q r =>
      q.1 ≠ r.1 ∧ q.1 ≠ r.2 ∧ q.2 ≠ r.1 ∧ q.2 ≠ r.2)
    (hQpair : (↑Q : Set (α × α)).Pairwise fun q r =>
      q.1 ≠ r.1 ∧ q.1 ≠ r.2 ∧ q.2 ≠ r.1 ∧ q.2 ≠ r.2)
    (hPord : ∀ q ∈ P, q.1 < q.2)
    (hQord : ∀ q ∈ Q, q.1 < q.2)
    (hperm : swapsPermList P.toList = swapsPermList Q.toList) :
    P ⊆ Q := by
  intro q hq
  have hmoveQ : swapsPermList Q.toList q.1 = q.2 := by
    rw [← hperm]
    exact (swapsPermList_pair_action P hPpair hq).1
  have hqlt := hPord q hq
  obtain ⟨r, hr, hr1 | hr2⟩ := exists_pair_of_swapsPermList_ne Q
    (x := q.1) (by rw [hmoveQ]; exact ne_of_gt hqlt)
  · have hactQ := (swapsPermList_pair_action Q hQpair hr).1
    rw [← hr1, hmoveQ] at hactQ
    have heq : q = r := Prod.ext hr1 hactQ
    exact heq ▸ hr
  · have hactQ := (swapsPermList_pair_action Q hQpair hr).2
    rw [← hr2, hmoveQ] at hactQ
    have hrlt := hQord r hr
    rw [← hactQ, ← hr2] at hrlt
    exact absurd hrlt (not_lt_of_gt hqlt)

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
    P = Q :=
  Finset.Subset.antisymm
    (disjoint_swaps_reconstruct_subset P Q hPpair hQpair hPord hQord hperm)
    (disjoint_swaps_reconstruct_subset Q P hQpair hPpair hQord hPord hperm.symm)

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
  unfold SwapCrosses at hnot
  have h12 : q.1 ∈ I ↔ q.2 ∈ I := by tauto
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    rw [Equiv.swap_apply_def]
    split_ifs with h1 h2
    · exact h12.mp (h1 ▸ hx)
    · exact h12.mpr (h2 ▸ hx)
    · exact hx
  · rw [Finset.card_image_of_injective _ (Equiv.injective _)]

theorem swapsPermList_image_eq_self
    {n : ℕ} (l : List (Fin n × Fin n))
    (I : Finset (Fin n))
    (hnot : ∀ q ∈ l, ¬ SwapCrosses q I) :
    I.image (swapsPermList l) = I := by
  induction l with
  | nil => simp [swapsPermList]
  | cons q qs ih =>
      have hqnot := hnot q (by simp)
      have hnot' : ∀ r ∈ qs, ¬ SwapCrosses r I :=
        fun r hr => hnot r (by simp [hr])
      rw [show swapsPermList (q :: qs) =
          (Equiv.swap q.1 q.2).trans (swapsPermList qs) from rfl,
        Equiv.coe_trans, ← Finset.image_image,
        swap_image_eq_self_of_not_crosses q I hqnot]
      exact ih hnot'

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
  classical
  let crosses : Fin n × Fin n → Prop := fun q => ∃ i, SwapCrosses q (I i)
  set P' := P.filter crosses with hP'def
  set R := P.filter fun q => ¬ crosses q with hRdef
  have hP'sub : P' ⊆ P := Finset.filter_subset _ _
  refine ⟨P', hP'sub, hP.mono (Finset.coe_subset.mpr hP'sub), ?_, ?_⟩
  · intro q hq
    rcases (Finset.mem_filter.mp hq).2 with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    unfold SwapCrosses at hi
    tauto
  · intro i
    have hRfix : (I i).image (collectionPerm R) = I i := by
      unfold collectionPerm
      apply swapsPermList_image_eq_self R.toList (I i)
      intro q hq hcross
      exact (Finset.mem_filter.mp (Finset.mem_toList.mp hq)).2 ⟨i, hcross⟩
    have hlistSet : (R.toList ++ P'.toList).toFinset = P := by
      rw [List.toFinset_append, Finset.toList_toFinset, Finset.toList_toFinset,
        hRdef, hP'def, Finset.union_comm, Finset.filter_union_filter_not_eq]
    have hlistNodup : (R.toList ++ P'.toList).Nodup := by
      apply List.Nodup.append R.nodup_toList P'.nodup_toList
      intro q hqR hqP
      rw [Finset.mem_toList] at hqR hqP
      exact (Finset.mem_filter.mp hqR).2 (Finset.mem_filter.mp hqP).2
    have horder : swapsPermList (R.toList ++ P'.toList) = collectionPerm P := by
      unfold collectionPerm
      exact disjoint_swaps_order_independent P hP _ hlistSet hlistNodup
    rw [← horder, swapsPermList_append, Equiv.coe_trans, ← Finset.image_image]
    unfold collectionPerm at hRfix
    rw [hRfix]
    rfl

/-- Sort a finite injective tuple by a permutation of its coordinates. -/
theorem exists_sorting_perm
    {α : Type*} [LinearOrder α] [DecidableEq α] {k : ℕ}
    (x : Fin k → α) (hinj : Function.Injective x) :
    ∃ ρ : Equiv.Perm (Fin k), StrictMono (x ∘ ρ) :=
  ⟨Tuple.sort x, (Tuple.monotone_sort x).strictMono_of_injective
    (hinj.comp (Tuple.sort x).injective)⟩

/-- With a nonnegative constant, every Corollary 4.2 bound is nonnegative. -/
theorem chainUpperBound_nonneg {k : ℕ} (p n : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (m : Fin k → ℕ) :
    0 ≤ chainUpperBound p n C m := by
  unfold chainUpperBound
  apply Finset.sum_nonneg
  intro j _
  apply Finset.prod_nonneg
  intro i _
  unfold chainFactor
  positivity

/-- Reindex an injective finite family of valid chain-size tuples into the full
sum occurring in Lemma 4.3.

The hypothesis `0 ≤ C` is needed: the terms of the Lemma 4.3 sum not hit by the
family are dropped, which requires them to be nonnegative (for `X = ∅` and
`C` very negative the right side is negative).  When it is omitted it is
discharged by `positivity`. -/
theorem chainUpperBound_sum_le_lemma43
    {Θ : Type*} [DecidableEq Θ]
    {p n k : ℕ} (C : ℝ)
    (X : Finset Θ) (m : Θ → Fin k → ℕ)
    (hvalid : ∀ θ ∈ X, IsChainSizeTuple n (m θ))
    (hinj : Set.InjOn m X)
    (hC : 0 ≤ C := by positivity) :
    (∑ θ ∈ X, chainUpperBound p n C (m θ)) ≤
      lemma43LHS p n k C := by
  classical
  unfold lemma43LHS lemma43Summand
  rw [← Finset.sum_image (f := fun μ => chainUpperBound p n C μ) hinj]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro μ hμ
    rcases Finset.mem_image.mp hμ with ⟨θ, hθ, rfl⟩
    unfold chainSizeTuples
    exact Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun i =>
      Finset.mem_range.mpr ((hvalid θ hθ).2 i).2, hvalid θ hθ⟩
  · intro μ _ _
    exact chainUpperBound_nonneg p n hC μ

/-- Generic finite union over conditional nested-chain witnesses.  This is only
bookkeeping: each individual witness is identified with a chain by
`conditional_nested_images_chainMass`, then the size-vector sum is embedded
in Lemma 4.3.

The hypothesis `0 ≤ C` is needed for the same reason as in
`chainUpperBound_sum_le_lemma43` (take `A = ∅`).  When it is omitted it is
discharged by `positivity`. -/
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
          chainUpperBound p (S \ indexImageSet τ F).card C (m θ))
    (hC : 0 ≤ C := by positivity) :
    orderingConditionalMass S
      (fun σ => AgreesOn F σ τ)
      (fun σ => ∃ θ ∈ A, ∀ i, indexSetSum σ (I θ i) = z θ i) ≤
      lemma43LHS p (S \ indexImageSet τ F).card k C := by
  unfold orderingConditionalMass uniformConditionalMass
  calc
    _ ≤ ∑ θ ∈ A,
          uniformMass ((indexedOrderings S).filter
            (fun σ => AgreesOn F σ τ))
            (fun σ => ∀ i, indexSetSum σ (I θ i) = z θ i) := by
        convert uniformMass_exists_le_sum _ A
          (fun θ σ => ∀ i, indexSetSum σ (I θ i) = z θ i)
    _ = ∑ θ ∈ A,
          chainMass (S \ indexImageSet τ F) (m θ) (z θ) := by
        apply Finset.sum_congr rfl
        intro θ hθ
        have h := conditional_nested_images_chainMass
          S τ hτ F (I θ) (hdisj θ hθ) (hnested θ hθ)
          (m θ) (hcard θ hθ) (z θ)
        unfold orderingConditionalMass uniformConditionalMass at h
        exact h
    _ ≤ ∑ θ ∈ A,
          chainUpperBound p (S \ indexImageSet τ F).card C (m θ) :=
        Finset.sum_le_sum hchain
    _ ≤ lemma43LHS p (S \ indexImageSet τ F).card k C :=
        chainUpperBound_sum_le_lemma43 C A m hvalid hinj hC

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
  unfold lemma43Base
  have hs1 : 1 ≤ s := by omega
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs1
  have hnR : (0 : ℝ) < n := by positivity
  have h4s : (n : ℝ) ≤ 4 * s := by
    have h : n ≤ 4 * s := by omega
    exact_mod_cast h
  have hsp : (s : ℝ) / p ≤ (n : ℝ) / p :=
    div_le_div_of_nonneg_right (by exact_mod_cast hsn) (Nat.cast_nonneg p)
  have hlog : Real.sqrt (Real.log s) ≤ Real.sqrt (Real.log n) := by
    apply Real.sqrt_le_sqrt
    exact Real.log_le_log (by linarith) (by exact_mod_cast hsn)
  have hroot : Real.sqrt n ≤ 2 * Real.sqrt s := by
    have h2 : (2 : ℝ) * Real.sqrt s = Real.sqrt (4 * s) := by
      rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    rw [h2]
    exact Real.sqrt_le_sqrt h4s
  have hsroot : 0 < Real.sqrt s := Real.sqrt_pos.mpr (by linarith)
  have hnroot : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnR
  have hterm : 2 * C * Real.sqrt (Real.log s) / Real.sqrt s ≤
      4 * C * Real.sqrt (Real.log n) / Real.sqrt n := by
    rw [div_le_div_iff₀ hsroot hnroot]
    have h1 : 0 ≤ C * Real.sqrt (Real.log s) :=
      mul_nonneg hCnonneg (Real.sqrt_nonneg _)
    calc 2 * C * Real.sqrt (Real.log s) * Real.sqrt n
        = 2 * (C * Real.sqrt (Real.log s)) * Real.sqrt n := by ring
      _ ≤ 2 * (C * Real.sqrt (Real.log s)) * (2 * Real.sqrt s) := by gcongr
      _ = 4 * (C * Real.sqrt (Real.log s)) * Real.sqrt s := by ring
      _ ≤ 4 * (C * Real.sqrt (Real.log n)) * Real.sqrt s := by gcongr
      _ = 4 * C * Real.sqrt (Real.log n) * Real.sqrt s := by ring
  linarith

/-- The exponent comparison αD≥3 used in the D-fold chain bounds. -/
theorem two_neg_alpha_pow_le_cube
    {n D : ℕ} {α : ℝ}
    (hn : 1 ≤ n)
    (hαD : 3 ≤ α * D) :
    (2 * (n : ℝ) ^ (-α)) ^ D ≤
      (2 : ℝ) ^ D / (n : ℝ) ^ 3 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  rw [mul_pow, div_eq_mul_one_div ((2 : ℝ) ^ D)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [← Real.rpow_natCast ((n : ℝ) ^ (-α)), ← Real.rpow_mul hn0.le]
  have h3 : (1 : ℝ) / (n : ℝ) ^ 3 = (n : ℝ) ^ (-(3 : ℝ)) := by
    rw [Real.rpow_neg hn0.le, one_div]
    norm_cast
  rw [h3]
  apply Real.rpow_le_rpow_of_exponent_le hnR
  linarith

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
  have hx' := (Finset.mem_filter.mp hx).2
  obtain ⟨hmono, habove⟩ := hx'
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have hxij : (x i).val < (x j).val := hmono hij
    have hi := habove i
    have hj := habove j
    simp only [tailSizes, paperPos] at hi hj ⊢
    omega
  · have hi := habove i
    have hxlt := (x i).isLt
    have hD : 0 < D := Fin.pos i
    simp only [tailSizes, paperPos] at hi hb2 hgap ⊢
    subst hs
    omega

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
  classical
  have hinner : ∀ θ ∈ outer,
      uniformMass space (fun ω => ∃ ξ ∈ inner θ, A θ ξ ω) ≤ (M : ℝ) * w θ := by
    intro θ hθ
    calc
      uniformMass space (fun ω => ∃ ξ ∈ inner θ, A θ ξ ω)
        ≤ ∑ ξ ∈ inner θ, uniformMass space (A θ ξ) :=
          uniformMass_exists_le_sum space (inner θ) (A θ)
      _ ≤ ∑ _ξ ∈ inner θ, w θ := Finset.sum_le_sum (hpoint θ hθ)
      _ = (inner θ).card * w θ := by simp
      _ ≤ (M : ℝ) * w θ :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcount θ hθ) (hw θ hθ)
  calc
    uniformMass space E
      ≤ uniformMass space
          (fun ω => ∃ θ ∈ outer, ∃ ξ ∈ inner θ, A θ ξ ω) :=
        uniformMass_mono_on space _ _ hcover
    _ ≤ ∑ θ ∈ outer,
          uniformMass space (fun ω => ∃ ξ ∈ inner θ, A θ ξ ω) := by
        convert uniformMass_exists_le_sum space outer
          (fun θ ω => ∃ ξ ∈ inner θ, A θ ξ ω)
    _ ≤ ∑ θ ∈ outer, (M : ℝ) * w θ := Finset.sum_le_sum hinner
    _ = (M : ℝ) * ∑ θ ∈ outer, w θ := by rw [Finset.mul_sum]
    _ ≤ (M : ℝ) * B := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg M)

/-- The possible partners `r ∈ {q+1, …, q+5D}` of a first endpoint `q` of a short swap
(at most `5D` of them); used to count the admissible swap collections whose first endpoints
lie in a given set. -/
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
  classical
  unfold collectionPartner
  by_cases h : ∃ z, (q, z) ∈ P
  · rw [dite_eq_left h]
    have hz := Classical.choose_spec h
    constructor
    · intro hy
      rw [← Option.some.inj hy]
      exact hz
    · intro hy
      congr 1
      by_contra hne
      have hpairs := hP.1 (Finset.mem_coe.mpr hz) (Finset.mem_coe.mpr hy)
        (fun heq => hne (congrArg Prod.snd heq))
      exact hpairs.1 rfl
  · rw [dite_eq_right h]
    constructor
    · intro hy
      cases hy
    · intro hy
      exact absurd ⟨y, hy⟩ h

theorem collectionPartner_mem_allowed
    {n D : ℕ} {P : Finset (Fin n × Fin n)}
    (hP : IsAdmissibleCollection D P)
    {Q : Finset (Fin n)}
    (q : {x // x ∈ Q}) :
    collectionPartner P q.1 ∈
      insert none ((shortPartners (D := D) q.1).image some) := by
  classical
  cases h : collectionPartner P q.1 with
  | none => exact Finset.mem_insert_self _ _
  | some y =>
      have hqy : (q.1, y) ∈ P := (collectionPartner_eq_some_iff hP q.1 y).1 h
      have hadm := hP.2 (q.1, y) hqy
      have hmem : y ∈ shortPartners (D := D) q.1 := by
        unfold shortPartners forwardWindow
        simp only [paperPos] at hadm
        rw [Finset.mem_erase, Finset.mem_filter]
        refine ⟨?_, Finset.mem_univ _, ?_, ?_⟩
        · intro hyq
          rw [hyq] at hadm
          omega
        · omega
        · omega
      exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem some hmem)

def supportedCollectionCode {n : ℕ}
    (Q : Finset (Fin n))
    (P : Finset (Fin n × Fin n)) :
    {q // q ∈ Q} → Option (Fin n) :=
  fun q => collectionPartner P q.1

/-- Each pair of a supported admissible collection is recorded by its code. -/
theorem mem_of_supportedCollectionCode_eq {n D : ℕ}
    {Q : Finset (Fin n)} {P P' : Finset (Fin n × Fin n)}
    (hP : P ∈ supportedAdmissibleCollections D Q)
    (hP' : P' ∈ supportedAdmissibleCollections D Q)
    (hcode : supportedCollectionCode Q P =
      supportedCollectionCode Q P')
    {r : Fin n × Fin n} (hr : r ∈ P) : r ∈ P' := by
  classical
  have hPm := (Finset.mem_filter.mp hP).2
  have hP'm := (Finset.mem_filter.mp hP').2
  have hfun := congrFun hcode ⟨r.1, hPm.2 r hr⟩
  simp only [supportedCollectionCode] at hfun
  rw [(collectionPartner_eq_some_iff hPm.1 r.1 r.2).2 hr] at hfun
  exact (collectionPartner_eq_some_iff hP'm.1 r.1 r.2).1 hfun.symm

theorem supportedCollectionCode_injective {n D : ℕ}
    (Q : Finset (Fin n)) :
    Set.InjOn (supportedCollectionCode Q)
      (supportedAdmissibleCollections D Q :
        Set (Finset (Fin n × Fin n))) := by
  intro P hP P' hP' hcode
  ext r
  exact ⟨fun hr => mem_of_supportedCollectionCode_eq hP hP' hcode hr,
    fun hr => mem_of_supportedCollectionCode_eq hP' hP hcode.symm hr⟩

def supportedCollectionCodes {n D : ℕ} (Q : Finset (Fin n)) :
    Finset ({q // q ∈ Q} → Option (Fin n)) :=
  Fintype.piFinset fun q : {q // q ∈ Q} =>
    insert none ((shortPartners (D := D) q.1).image some)

theorem supportedAdmissibleCollections_card_le {n D : ℕ}
    (Q : Finset (Fin n)) :
    (supportedAdmissibleCollections D Q).card ≤
      (5 * D + 1) ^ Q.card := by
  classical
  calc (supportedAdmissibleCollections D Q).card
      = ((supportedAdmissibleCollections D Q).image
          (supportedCollectionCode Q)).card :=
        (Finset.card_image_of_injOn (supportedCollectionCode_injective Q)).symm
    _ ≤ (supportedCollectionCodes (D := D) Q).card := by
        apply Finset.card_le_card
        intro c hc
        rcases Finset.mem_image.mp hc with ⟨P, hP, rfl⟩
        have hPm := (Finset.mem_filter.mp hP).2
        exact Fintype.mem_piFinset.mpr
          (fun q => collectionPartner_mem_allowed hPm.1 q)
    _ = ∏ q : {q // q ∈ Q},
          (insert none ((shortPartners (D := D) q.1).image some)).card :=
        Fintype.card_piFinset _
    _ ≤ ∏ _q : {q // q ∈ Q}, (5 * D + 1) := by
        apply Finset.prod_le_prod
        intro q _
        calc (insert none ((shortPartners (D := D) q.1).image some)).card
            ≤ ((shortPartners (D := D) q.1).image some).card + 1 :=
              Finset.card_insert_le _ _
          _ ≤ (shortPartners (D := D) q.1).card + 1 := by
              gcongr
              exact Finset.card_image_le
          _ ≤ 5 * D + 1 := by
              gcongr
              exact card_shortPartners_le q.1
    _ = (5 * D + 1) ^ Q.card := by simp

/-- The image of a swap pair `(q, r)` under the reversal of positions (`i ↦ n + 1 − i` in the
paper's numbering), with its entries exchanged, so that a pair with `q < r` again has its
smaller entry first. -/
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
  classical
  constructor
  · intro q hq r hr hqr
    rcases Finset.mem_image.mp (Finset.mem_coe.mp hq) with ⟨q₀, hq₀, rfl⟩
    rcases Finset.mem_image.mp (Finset.mem_coe.mp hr) with ⟨r₀, hr₀, rfl⟩
    have hq0r0 : q₀ ≠ r₀ := fun h => hqr (h ▸ rfl)
    have hd := hP.1 (Finset.mem_coe.mpr hq₀) (Finset.mem_coe.mpr hr₀) hq0r0
    unfold reverseSwapPair swapPairsDisjoint
    simp only [ne_eq, EmbeddingLike.apply_eq_iff_eq]
    exact ⟨hd.2.2.2, hd.2.2.1, hd.2.1, hd.1⟩
  · intro q hq
    rcases Finset.mem_image.mp hq with ⟨r, hr, rfl⟩
    have hadm := hP.2 r hr
    unfold reverseSwapPair
    simp only [paperPos, reverseIndex_apply_val] at hadm ⊢
    have h1 := r.1.isLt
    have h2 := r.2.isLt
    omega

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
  have hsymm : (reverseIndex n).symm = reverseIndex n := Equiv.ext fun _ => rfl
  have h := Equiv.symm_trans_swap_trans a b (reverseIndex n)
  rw [hsymm] at h
  unfold reverseConjugate
  rw [← Equiv.trans_assoc]
  exact h

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
  classical
  rcases hπ with ⟨P, hPadm, hPπ⟩
  refine ⟨reverseSwapCollection P, reverseSwapCollection_admissible hPadm, ?_⟩
  have hlist : (P.toList.map reverseSwapPair).toFinset = reverseSwapCollection P := by
    ext q
    simp [reverseSwapCollection]
  have hnodup : (P.toList.map reverseSwapPair).Nodup :=
    P.nodup_toList.map reverseSwapPair_injective
  rw [← collectionPerm_order_independent (reverseSwapCollection_admissible hPadm)
      (P.toList.map reverseSwapPair) hlist hnodup, swapsPermList_reverse]
  unfold collectionPerm at hPπ
  rw [hPπ]

/-- Reversal conjugation transports the fixed-outside condition from [b,b'] to
the reversed interval [rev b', rev b]. -/
theorem reverseConjugate_fixedOutside {n : ℕ}
    (b b' : Fin n) (π : Equiv.Perm (Fin n))
    (hfix : FixedOutside b b' π) :
    FixedOutside (reverseIndex n b') (reverseIndex n b)
      (reverseConjugate π) := by
  intro i hi
  have hrev : paperPos (reverseIndex n i) < paperPos b ∨
      paperPos b' < paperPos (reverseIndex n i) := by
    simp only [paperPos, reverseIndex_apply_val] at hi ⊢
    have := i.isLt
    have := b.isLt
    have := b'.isLt
    omega
  rw [reverseConjugate_apply, hfix (reverseIndex n i) hrev,
    reverseIndex_involutive]

end

end GrahamRearrangement.Section5
