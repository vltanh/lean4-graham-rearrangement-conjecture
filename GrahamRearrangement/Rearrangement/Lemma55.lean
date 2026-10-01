module

public import GrahamRearrangement.Rearrangement.Lemma52

@[expose] public section

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Lemma 5.5
-/

noncomputable section

theorem card_interestingLeftSupport_le
    {n D : ℕ} (hD : 7 ≤ D)
    (b : Fin n) (x : Fin D → Fin n) :
    (interestingLeftSupport b x).card ≤ 7 * D ^ 2 := by
  sorry

theorem permuted_interval_sum_eq
    {n p : ℕ} (σ : Fin n → ZMod p)
    (π ρ : Equiv.Perm (Fin n)) (a b : Fin n)
    (hab : a.val ≤ b.val) :
    indexedIntervalSum
        (applyPositionPerm (applyPositionPerm σ π) ρ) a b =
      indexSetSum σ
        ((indexInterval a b).image ρ |>.image π) := by
  rw [← indexSetSum_indexInterval]
  unfold indexSetSum applyPositionPerm
  rw [Finset.sum_image]
  · rw [Finset.sum_image]
    · rfl
    · intro i hi j hj h
      exact ρ.injective h
  · intro i hi j hj h
    exact π.injective h

theorem lemma55_reduce_to_interesting
    {n p D : ℕ}
    (σ : Fin n → ZMod p)
    (b b' : Fin n)
    (u x : Fin D → Fin n)
    (πi : Fin D → Equiv.Perm (Fin n))
    (hπ :
      ∃ π : Equiv.Perm (Fin n),
        IsAdmissiblePermutation D π ∧
        ∀ i,
          indexedIntervalSum
            (applyPositionPerm
              (applyPositionPerm σ π) (πi i))
            (u i) (x i) = 0) :
    ∃ π ∈ interestingPermutations D
        (fun i => constraintSet u x πi i),
      ∀ i,
        indexedIntervalSum
          (applyPositionPerm
            (applyPositionPerm σ π) (πi i))
          (u i) (x i) = 0 := by
  sorry

theorem constraintSet_mem_above_window {n D : ℕ}
    (b b' : Fin n)
    (u x : Fin D → Fin n)
    (hu : ∀ i,
      paperPos b ≤ paperPos (u i) ∧
        paperPos (u i) ≤ paperPos b')
    (πi : Fin D → Equiv.Perm (Fin n))
    (hfix : ∀ i, FixedOutside b b' (πi i))
    (i : Fin D) (z : Fin n)
    (hz : paperPos b' < paperPos z) :
    z ∈ constraintSet u x πi i ↔
      z ∈ indexInterval (u i) (x i) := by
  constructor
  · intro h
    rcases Finset.mem_image.1 h with ⟨w, hw, hπw⟩
    have hzfix : πi i z = z :=
      hfix i z (Or.inr hz)
    have hwz : w = z := by
      apply (πi i).injective
      rw [hπw, hzfix]
    simpa [hwz] using hw
  · intro h
    refine Finset.mem_image.2 ⟨z, h, ?_⟩
    exact hfix i z (Or.inr hz)

theorem constraintSet_not_mem_below_window {n D : ℕ}
    (b b' : Fin n)
    (u x : Fin D → Fin n)
    (hu : ∀ i,
      paperPos b ≤ paperPos (u i) ∧
        paperPos (u i) ≤ paperPos b')
    (πi : Fin D → Equiv.Perm (Fin n))
    (hfix : ∀ i, FixedOutside b b' (πi i))
    (i : Fin D) (z : Fin n)
    (hz : paperPos z < paperPos b) :
    z ∉ constraintSet u x πi i := by
  intro h
  rcases Finset.mem_image.1 h with ⟨w, hw, hπw⟩
  have hzfix : πi i z = z :=
    hfix i z (Or.inl hz)
  have hwz : w = z := by
    apply (πi i).injective
    rw [hπw, hzfix]
  subst w
  have hw' := (Finset.mem_filter.1 hw).2.1
  have hui := (hu i).1
  simp [paperPos] at hw' hui hz
  omega

theorem interesting_crossing_forces_tail_start
    {n D : ℕ}
    (hD : 0 < D)
    (b b' : Fin n)
    (hgap : paperPos b' - paperPos b = 5 * D)
    (u x : Fin D → Fin n)
    (hu : ∀ i,
      paperPos b ≤ paperPos (u i) ∧
        paperPos (u i) ≤ paperPos b')
    (πi : Fin D → Equiv.Perm (Fin n))
    (hfix : ∀ i, FixedOutside b b' (πi i))
    (q : Fin n × Fin n) (i : Fin D)
    (hlen :
      paperPos q.1 < paperPos q.2 ∧
        paperPos q.2 - paperPos q.1 ≤ 5 * D)
    (hcross : SwapCrosses q (constraintSet u x πi i))
    (hnotlocal : q.1 ∉ symmetricWindow b (5 * D)) :
    q.1 ∈ backwardWindow (x i) (5 * D) := by
  sorry

theorem interesting_left_support
    {n D : ℕ}
    (hD : 0 < D)
    (b b' : Fin n)
    (hgap : paperPos b' - paperPos b = 5 * D)
    (u x : Fin D → Fin n)
    (hu : ∀ i,
      paperPos b ≤ paperPos (u i) ∧
        paperPos (u i) ≤ paperPos b')
    (πi : Fin D → Equiv.Perm (Fin n))
    (hfix : ∀ i, FixedOutside b b' (πi i))
    {π : Equiv.Perm (Fin n)}
    (hπ : π ∈ interestingPermutations D
      (fun i => constraintSet u x πi i)) :
    ∃ P : Finset (Fin n × Fin n),
      IsAdmissibleCollection D P ∧
      collectionPerm P = π ∧
      ∀ q ∈ P, q.1 ∈ interestingLeftSupport b x := by
  sorry

def chosenInterestingCollection {n k : ℕ} (D : ℕ)
    (I : Fin k → Finset (Fin n))
    (π : Equiv.Perm (Fin n)) :
    Finset (Fin n × Fin n) := by
  classical
  by_cases h : IsInterestingPermutation D I π
  · exact Classical.choose h
  · exact ∅

theorem chosenInterestingCollection_spec {n k : ℕ}
    (D : ℕ) (I : Fin k → Finset (Fin n))
    {π : Equiv.Perm (Fin n)}
    (hπ : π ∈ interestingPermutations D I) :
    IsAdmissibleCollection D
        (chosenInterestingCollection D I π) ∧
      collectionPerm (chosenInterestingCollection D I π) = π ∧
      ∀ q ∈ chosenInterestingCollection D I π,
        ∃ i, SwapCrosses q (I i) := by
  sorry

theorem chosenInterestingCollection_injective {n k : ℕ}
    (D : ℕ) (I : Fin k → Finset (Fin n)) :
    Set.InjOn (chosenInterestingCollection D I)
      (interestingPermutations D I : Set (Equiv.Perm (Fin n))) := by
  intro π hπ ρ hρ hEq
  have hπspec :=
    (chosenInterestingCollection_spec D I
      (show π ∈ interestingPermutations D I from hπ)).2.1
  have hρspec :=
    (chosenInterestingCollection_spec D I
      (show ρ ∈ interestingPermutations D I from hρ)).2.1
  rw [← hπspec, ← hρspec, hEq]

theorem interestingPermutations_card_le
    {n D : ℕ}
    (hD7 : 7 ≤ D)
    (b b' : Fin n)
    (hgap : paperPos b' - paperPos b = 5 * D)
    (u x : Fin D → Fin n)
    (hu : ∀ i,
      paperPos b ≤ paperPos (u i) ∧
        paperPos (u i) ≤ paperPos b')
    (πi : Fin D → Equiv.Perm (Fin n))
    (hfix : ∀ i, FixedOutside b b' (πi i)) :
    (interestingPermutations D
      (fun i => constraintSet u x πi i)).card ≤
        D ^ (14 * D ^ 2) := by
  classical
  let I : Fin D → Finset (Fin n) :=
    fun i => constraintSet u x πi i
  let Q := interestingLeftSupport b x
  let f := chosenInterestingCollection D I
  have hfinj :
      Set.InjOn f
        (interestingPermutations D I : Set (Equiv.Perm (Fin n))) :=
    chosenInterestingCollection_injective D I
  have hsupport :
      ∀ π ∈ interestingPermutations D I,
        f π ∈ supportedAdmissibleCollections D Q := by
    intro π hπ
    have hspec := chosenInterestingCollection_spec D I hπ
    obtain ⟨P', hP'adm, hP'π, hP'supp⟩ :=
      interesting_left_support
        (by omega) b b' hgap u x hu πi hfix hπ
    have hEq : f π = P' := by
      apply admissibleCollection_reconstruct
        hspec.1 hP'adm
      rw [hspec.2.1, hP'π]
    apply Finset.mem_filter.2
    refine ⟨Finset.mem_univ _, hspec.1, ?_⟩
    intro q hq
    rw [hEq] at hq
    exact hP'supp q hq
  have hcardImage :
      (interestingPermutations D I).card =
        ((interestingPermutations D I).image f).card := by
    symm
    exact Finset.card_image_of_injOn hfinj
  have hsub :
      (interestingPermutations D I).image f ⊆
        supportedAdmissibleCollections D Q := by
    intro P hP
    rcases Finset.mem_image.1 hP with ⟨π, hπ, rfl⟩
    exact hsupport π hπ
  have hQ : Q.card ≤ 7 * D ^ 2 :=
    card_interestingLeftSupport_le hD7 b x
  have hcount :=
    Section5External.supportedAdmissibleCollections_card_le
      (D := D) Q
  have hbase : 5 * D + 1 ≤ D ^ 2 := by
    nlinarith
  calc
    (interestingPermutations D I).card
      = ((interestingPermutations D I).image f).card := hcardImage
    _ ≤ (supportedAdmissibleCollections D Q).card :=
      Finset.card_le_card hsub
    _ ≤ (5 * D + 1) ^ Q.card := hcount
    _ ≤ (D ^ 2) ^ Q.card := by
      gcongr
    _ ≤ (D ^ 2) ^ (7 * D ^ 2) := by
      gcongr
    _ = D ^ (14 * D ^ 2) := by
      rw [← pow_mul]
      congr 1
      ring

def lemma55HeadSet {n D : ℕ}
    (u : Fin D → Fin n) (b' : Fin n)
    (πi : Fin D → Equiv.Perm (Fin n))
    (i : Fin D) : Finset (Fin n) :=
  (indexInterval (u i) b').image (πi i)

def lemma55TailSet {n D : ℕ}
    (b' : Fin n) (x : Fin D → Fin n)
    (i : Fin D) : Finset (Fin n) :=
  indexOpenClosed b' (x i)

theorem lemma55HeadSet_subset_window {n D : ℕ}
    (b b' : Fin n)
    (u : Fin D → Fin n)
    (hu : ∀ i,
      paperPos b ≤ paperPos (u i) ∧
        paperPos (u i) ≤ paperPos b')
    (πi : Fin D → Equiv.Perm (Fin n))
    (hfix : ∀ i, FixedOutside b b' (πi i))
    (i : Fin D) :
    lemma55HeadSet u b' πi i ⊆ indexInterval b b' := by
  sorry

theorem lemma55TailSet_fixed {n D : ℕ}
    (b b' : Fin n) (x : Fin D → Fin n)
    (πi : Fin D → Equiv.Perm (Fin n))
    (hfix : ∀ i, FixedOutside b b' (πi i))
    (i : Fin D) :
    (lemma55TailSet b' x i).image (πi i) =
      lemma55TailSet b' x i := by
  sorry

theorem lemma55_constraint_split {n D : ℕ}
    (b b' : Fin n)
    (u x : Fin D → Fin n)
    (hu : ∀ i,
      paperPos b ≤ paperPos (u i) ∧
        paperPos (u i) ≤ paperPos b')
    (hx : x ∈ tailTuples b' D)
    (πi : Fin D → Equiv.Perm (Fin n))
    (hfix : ∀ i, FixedOutside b b' (πi i))
    (i : Fin D) :
    constraintSet u x πi i =
      lemma55HeadSet u b' πi i ∪ lemma55TailSet b' x i := by
  sorry

theorem lemma55TailSet_nested {n D : ℕ}
    (b' : Fin n) {x : Fin D → Fin n}
    (hx : x ∈ tailTuples b' D) :
    ∀ i j, i ≤ j →
      lemma55TailSet b' x i ⊆ lemma55TailSet b' x j := by
  intro i j hij y hy
  have hmono := (Finset.mem_filter.mp hx).2.1.monotone hij
  simp only [lemma55TailSet,indexOpenClosed,Finset.mem_filter,
    Finset.mem_univ,true_and] at hy ⊢
  exact ⟨hy.1,le_trans hy.2 (by exact_mod_cast hmono)⟩

theorem lemma55TailSet_card {n D : ℕ}
    (b' : Fin n) {x : Fin D → Fin n}
    (hx : x ∈ tailTuples b' D) (i : Fin D) :
    (lemma55TailSet b' x i).card = tailSizes b' x i := by
  have hxi := (Finset.mem_filter.mp hx).2.2 i
  have hle : b'.val ≤ (x i).val := by
    simp [paperPos] at hxi
    omega
  simpa [lemma55TailSet,tailSizes] using
    card_indexOpenClosed b' (x i) hle

theorem lemma55HeadTail_disjoint {n D : ℕ}
    (b b' : Fin n)
    (u x : Fin D → Fin n)
    (hu : ∀ i,
      paperPos b ≤ paperPos (u i) ∧
        paperPos (u i) ≤ paperPos b')
    (πi : Fin D → Equiv.Perm (Fin n))
    (hfix : ∀ i, FixedOutside b b' (πi i))
    (i : Fin D) :
    Disjoint (lemma55HeadSet u b' πi i)
      (lemma55TailSet b' x i) := by
  rw [Finset.disjoint_left]
  intro y hyH hyT
  have hyF := lemma55HeadSet_subset_window b b' u hu πi hfix i hyH
  simp [indexInterval,lemma55TailSet,indexOpenClosed] at hyF hyT
  omega

theorem lemma55_fixed_tail_conditional_bound
    {p D : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    (τ : Fin S.card → ZMod p) (hτ : IsIndexedOrdering S τ)
    (b b' : Fin S.card)
    (u x : Fin D → Fin S.card)
    (hu : ∀ i,
      paperPos b ≤ paperPos (u i) ∧
        paperPos (u i) ≤ paperPos b')
    (hx : x ∈ tailTuples b' D)
    (πi : Fin D → Equiv.Perm (Fin S.card))
    (hfix : ∀ i, FixedOutside b b' (πi i))
    (C : ℝ)
    (hm : IsChainSizeTuple
      (S \ indexImageSet τ (indexInterval b b')).card
      (tailSizes b' x))
    (hchain :
      ∀ z : Fin D → ZMod p,
        chainMass (S \ indexImageSet τ (indexInterval b b'))
            (tailSizes b' x) z ≤
          chainUpperBound p
            (S \ indexImageSet τ (indexInterval b b')).card
            C (tailSizes b' x)) :
    orderingConditionalMass S
      (fun σ => AgreesOn (indexInterval b b') σ τ)
      (fun σ =>
        ∀ i,
          indexedIntervalSum
            (applyPositionPerm σ (πi i))
            (u i) (x i) = 0) ≤
      chainUpperBound p
        (S \ indexImageSet τ (indexInterval b b')).card
        C (tailSizes b' x) := by
  sorry

theorem lemma55_fixed_x_pi_mass_le
    {α : ℝ} (hα0 : 0 < α) (hαh : α < 1 / 2)
    (P : Section5Parameters α)
    {p : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hreg : Section5Regime P p S)
    (b b' : Fin S.card)
    (hb2 : 2 ≤ paperPos b)
    (hgap : paperPos b' - paperPos b = 5 * P.D)
    (u x : Fin P.D → Fin S.card)
    (hu : ∀ i,
      paperPos b ≤ paperPos (u i) ∧
        paperPos (u i) ≤ paperPos b')
    (hx : x ∈ tailTuples b' P.D)
    (πi : Fin P.D → Equiv.Perm (Fin S.card))
    (hfix : ∀ i, FixedOutside b b' (πi i))
    (π : Equiv.Perm (Fin S.card)) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    orderingEventMass S
      (fun σ =>
        ∀ i,
          indexedIntervalSum
            (applyPositionPerm
              (applyPositionPerm σ π) (πi i))
            (u i) (x i) = 0) ≤
      chainUpperBound p (S.card - (5 * P.D + 1))
        (chainConstant P.D) (tailSizes b' x) := by
  sorry

/-- Lemma 5.5. -/
theorem lemma5_5
    {α : ℝ} (hα0 : 0 < α) (hαh : α < 1 / 2)
    (P : Section5Parameters α)
    {p : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hreg : Section5Regime P p S)
    (b b' : Fin S.card)
    (hb2 : 2 ≤ paperPos b)
    (hb' : paperPos b' ≤ S.card - 2)
    (hgap : paperPos b' - paperPos b = 5 * P.D)
    (u : Fin P.D → Fin S.card)
    (hu : ∀ i,
      paperPos b ≤ paperPos (u i) ∧
        paperPos (u i) ≤ paperPos b')
    (πi : Fin P.D → Equiv.Perm (Fin S.card))
    (hfix : ∀ i, FixedOutside b b' (πi i)) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    orderingEventMass S
      (fun σ => Lemma55Event σ b b' u πi) ≤
        1 / (S.card : ℝ) ^ 2 := by
  sorry

end

end GrahamRearrangement
