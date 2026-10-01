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
  unfold interestingLeftSupport
  have h1 := card_symmetricWindow_le b (5 * D)
  have h2 :
      (Finset.univ.biUnion fun i => backwardWindow (x i) (5 * D)).card ≤
        D * (5 * D) := by
    calc
      _ ≤ ∑ i : Fin D, (backwardWindow (x i) (5 * D)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin D, 5 * D :=
          Finset.sum_le_sum fun i _ => card_backwardWindow_le (x i) (5 * D)
      _ = D * (5 * D) := by simp
  calc
    _ ≤ (symmetricWindow b (5 * D)).card +
          (Finset.univ.biUnion fun i => backwardWindow (x i) (5 * D)).card :=
        Finset.card_union_le _ _
    _ ≤ (2 * (5 * D) + 1) + D * (5 * D) := by omega
    _ ≤ 7 * D ^ 2 := by nlinarith

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
  rcases hπ with ⟨π, ⟨P, hPadm, hPπ⟩, hzero⟩
  obtain ⟨P', hPsub, hP'disj, hcross, himage⟩ :=
    Section5.trim_irrelevant_disjoint_swaps P hPadm.1
      (fun i => constraintSet u x πi i)
  refine ⟨collectionPerm P', ?_, ?_⟩
  · simp only [interestingPermutations, Finset.mem_filter,
      Finset.mem_univ, true_and]
    refine ⟨P', ⟨hP'disj, fun q hq => hPadm.2 q (hPsub hq)⟩, rfl, ?_⟩
    intro q hq
    obtain ⟨i, hi⟩ := hcross q hq
    refine ⟨i, ?_⟩
    unfold SwapCrosses
    tauto
  · intro i
    have key : ∀ ρ : Equiv.Perm (Fin n),
        indexedIntervalSum
            (applyPositionPerm (applyPositionPerm σ ρ) (πi i))
            (u i) (x i) =
          indexSetSum σ ((constraintSet u x πi i).image ρ) := by
      intro ρ
      rw [← indexSetSum_indexInterval, indexSetSum_applyPositionPerm_image,
        indexSetSum_applyPositionPerm_image]
      rfl
    rw [key, himage i, hPπ, ← key]
    exact hzero i

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
  have hb' : b'.val = b.val + 5 * D := by
    simp only [paperPos] at hgap
    omega
  have hloc : ¬ (Nat.dist q.1.val b.val ≤ 5 * D) := by
    intro h
    exact hnotlocal (by simp [symmetricWindow, h])
  unfold Nat.dist at hloc
  have hlen' : q.1.val < q.2.val ∧ q.2.val ≤ q.1.val + 5 * D := by
    simp only [paperPos] at hlen
    omega
  rcases lt_or_ge q.1.val b.val with hlt | hge
  · exfalso
    have h1 := constraintSet_not_mem_below_window b b' u x hu πi hfix i q.1
      (by simp only [paperPos]; omega)
    have h2 := constraintSet_not_mem_below_window b b' u x hu πi hfix i q.2
      (by simp only [paperPos]; omega)
    unfold SwapCrosses at hcross
    tauto
  · have m1 := constraintSet_mem_above_window b b' u x hu πi hfix i q.1
      (by simp only [paperPos]; omega)
    have m2 := constraintSet_mem_above_window b b' u x hu πi hfix i q.2
      (by simp only [paperPos]; omega)
    have hui := (hu i).2
    simp only [paperPos] at hui
    simp only [indexInterval, Finset.mem_filter, Finset.mem_univ,
      true_and] at m1 m2
    unfold SwapCrosses at hcross
    rw [m1, m2] at hcross
    simp only [backwardWindow, Finset.mem_filter, Finset.mem_univ, true_and]
    omega

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
  classical
  rcases (Finset.mem_filter.1 hπ).2 with ⟨P, hPadm, hPπ, hcross⟩
  refine ⟨P, hPadm, hPπ, ?_⟩
  intro q hq
  rcases hcross q hq with ⟨i, hi⟩
  by_cases hlocal : q.1 ∈ symmetricWindow b (5 * D)
  · exact Finset.mem_union_left _ hlocal
  · have htail : q.1 ∈ backwardWindow (x i) (5 * D) :=
      interesting_crossing_forces_tail_start
        hD b b' hgap u x hu πi hfix q i (hPadm.2 q hq) hi hlocal
    exact Finset.mem_union_right _ (Finset.mem_biUnion.2
      ⟨i, Finset.mem_univ i, htail⟩)

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
  classical
  have h : IsInterestingPermutation D I π := (Finset.mem_filter.1 hπ).2
  unfold chosenInterestingCollection
  rw [dite_eq_left h]
  exact Classical.choose_spec h

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
    Section5.supportedAdmissibleCollections_card_le
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
  intro y hy
  rcases Finset.mem_image.mp hy with ⟨w, hw, rfl⟩
  simp only [indexInterval, Finset.mem_filter, Finset.mem_univ,
    true_and] at hw ⊢
  have hui := (hu i).1
  simp only [paperPos] at hui
  by_contra hout
  have hfixed := hfix i (πi i w) (by simp only [paperPos]; omega)
  have hEq : πi i w = w := (πi i).injective hfixed
  rw [hEq] at hout
  omega

theorem lemma55TailSet_fixed {n D : ℕ}
    (b b' : Fin n) (x : Fin D → Fin n)
    (πi : Fin D → Equiv.Perm (Fin n))
    (hfix : ∀ i, FixedOutside b b' (πi i))
    (i : Fin D) :
    (lemma55TailSet b' x i).image (πi i) =
      lemma55TailSet b' x i := by
  ext y
  simp only [lemma55TailSet, Finset.mem_image]
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hzData := (Finset.mem_filter.mp hz).2
    rw [hfix i z (Or.inr (by simp only [paperPos]; omega))]
    exact hz
  · intro hy
    refine ⟨y, hy, ?_⟩
    have hyData := (Finset.mem_filter.mp hy).2
    exact hfix i y (Or.inr (by simp only [paperPos]; omega))

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
  have hxi := (Finset.mem_filter.mp hx).2.2 i
  have hui := hu i
  simp only [paperPos] at hxi hui
  have hsplit :
      indexInterval (u i) (x i) =
        indexInterval (u i) b' ∪ indexOpenClosed b' (x i) := by
    ext y
    simp only [indexInterval, indexOpenClosed, Finset.mem_union,
      Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  unfold constraintSet lemma55HeadSet
  rw [hsplit, Finset.image_union]
  congr 1
  exact lemma55TailSet_fixed b b' x πi hfix i

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
  have hdisj : ∀ i, Disjoint (indexInterval b b') (lemma55TailSet b' x i) := by
    intro i
    rw [Finset.disjoint_left]
    intro y hyF hyI
    simp only [indexInterval, lemma55TailSet, indexOpenClosed,
      Finset.mem_filter, Finset.mem_univ, true_and] at hyF hyI
    omega
  have key : ∀ σ : Fin S.card → ZMod p, AgreesOn (indexInterval b b') σ τ →
      ∀ i, indexedIntervalSum (applyPositionPerm σ (πi i)) (u i) (x i) =
        indexSetSum τ (lemma55HeadSet u b' πi i) +
          indexSetSum σ (lemma55TailSet b' x i) := by
    intro σ hagr i
    rw [← indexSetSum_indexInterval, indexSetSum_applyPositionPerm_image]
    change indexSetSum σ (constraintSet u x πi i) = _
    rw [lemma55_constraint_split b b' u x hu hx πi hfix i]
    unfold indexSetSum
    rw [Finset.sum_union (lemma55HeadTail_disjoint b b' u x hu πi hfix i)]
    congr 1
    exact Section5.indexSetSum_eq_of_agreesOn hagr
      (lemma55HeadSet_subset_window b b' u hu πi hfix i)
  have hevent :
      orderingConditionalMass S
        (fun σ => AgreesOn (indexInterval b b') σ τ)
        (fun σ =>
          ∀ i,
            indexedIntervalSum
              (applyPositionPerm σ (πi i))
              (u i) (x i) = 0) =
      orderingConditionalMass S
        (fun σ => AgreesOn (indexInterval b b') σ τ)
        (fun σ => ∀ i, indexSetSum σ (lemma55TailSet b' x i) =
          - indexSetSum τ (lemma55HeadSet u b' πi i)) := by
    unfold orderingConditionalMass uniformConditionalMass
    apply uniformMass_congr
    intro σ hσ
    have hagr : AgreesOn (indexInterval b b') σ τ := (Finset.mem_filter.mp hσ).2
    apply forall_congr'
    intro i
    rw [key σ hagr i]
    exact add_eq_zero_iff_eq_neg'
  rw [hevent, Section5.conditional_nested_images_chainMass
    S τ hτ (indexInterval b b') (lemma55TailSet b' x) hdisj
    (lemma55TailSet_nested b' hx) (tailSizes b' x)
    (lemma55TailSet_card b' hx)
    (fun i => - indexSetSum τ (lemma55HeadSet u b' πi i))]
  exact hchain _

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
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hD := section5Parameters_D_pos hα0 hαh P
  have hbb' : b'.val = b.val + 5 * P.D := by
    simp only [paperPos] at hgap
    omega
  have hFcard : (indexInterval b b').card = 5 * P.D + 1 := by
    rw [card_indexInterval b b' (by omega)]
    omega
  have hinv := Section5.ordering_perm_invariant S π
    (fun σ => ∀ i,
      indexedIntervalSum (applyPositionPerm σ (πi i)) (u i) (x i) = 0)
  refine hinv.symm.trans_le ?_
  apply Section5.event_le_of_agreesOn_fibers S (indexInterval b b')
  intro τ hτ
  have himage := Section5.exposed_image_card S hτ (indexInterval b b')
  have hsub := Section5.exposedImage_subset S hτ (indexInterval b b')
  have hTcard :
      (S \ indexImageSet τ (indexInterval b b')).card =
        S.card - (5 * P.D + 1) := by
    rw [Finset.card_sdiff_of_subset hsub, himage, hFcard]
  have h50 := section5_card_ge_fiftyD hreg
  have hT2 : 2 ≤ (S \ indexImageSet τ (indexInterval b b')).card := by
    rw [hTcard]
    omega
  have htuple :
      IsChainSizeTuple (S \ indexImageSet τ (indexInterval b b')).card
        (tailSizes b' x) :=
    Section5.tailSizes_valid b b' hb2 hgap x hx hTcard
  have hchain :
      ∀ z : Fin P.D → ZMod p,
        chainMass (S \ indexImageSet τ (indexInterval b b'))
            (tailSizes b' x) z ≤
          chainUpperBound p (S \ indexImageSet τ (indexInterval b b')).card
            (chainConstant P.D) (tailSizes b' x) :=
    fun z => chainConstant_spec P.D hD p hp _ hT2 _ htuple z
  have hbound := lemma55_fixed_tail_conditional_bound S τ hτ b b' u x hu hx
    πi hfix (chainConstant P.D) htuple hchain
  rwa [hTcard] at hbound

theorem lemma55_chainUpperBound_nonneg {k p n : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (m : Fin k → ℕ) :
    0 ≤ chainUpperBound p n C m := by
  unfold chainUpperBound
  apply Finset.sum_nonneg
  intro j _
  apply Finset.prod_nonneg
  intro i _
  unfold chainFactor
  positivity

/-- Sum of the Corollary 4.2 bounds over an injective family of valid size
tuples is bounded by the full sum in Lemma 4.3 (for a nonnegative constant). -/
theorem lemma55_chainUpperBound_sum_le {p n k : ℕ} {C : ℝ} (hC : 0 ≤ C)
    {Θ : Type*} (X : Finset Θ) (m : Θ → Fin k → ℕ)
    (hvalid : ∀ θ ∈ X, IsChainSizeTuple n (m θ))
    (hinj : Set.InjOn m X) :
    (∑ θ ∈ X, chainUpperBound p n C (m θ)) ≤ lemma43LHS p n k C := by
  classical
  unfold lemma43LHS lemma43Summand
  rw [← Finset.sum_image hinj]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro m' hm'
    rcases Finset.mem_image.1 hm' with ⟨θ, hθ, rfl⟩
    unfold chainSizeTuples
    simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
    exact ⟨fun i => ((hvalid θ hθ).2 i).2, hvalid θ hθ⟩
  · intro m' _ _
    exact lemma55_chainUpperBound_nonneg hC m'

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
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hD7 : 7 ≤ P.D := by
    rw [P.D_eq]
    exact section5D_ge_seven hα0 hαh
  have hD := section5Parameters_D_pos hα0 hαh P
  have h50 := section5_card_ge_fiftyD hreg
  have hCpos := chainConstant_pos P.D
  obtain ⟨s, hs⟩ : ∃ s, s = S.card - (5 * P.D + 1) := ⟨_, rfl⟩
  have hunion :
      orderingEventMass S (fun σ => Lemma55Event σ b b' u πi) ≤
        ((P.D ^ (14 * P.D ^ 2) : ℕ) : ℝ) *
          lemma43LHS p s P.D (chainConstant P.D) := by
    unfold orderingEventMass
    apply Section5.bounded_choice_witness_union
      (indexedOrderings S) (tailTuples b' P.D)
      (fun x => interestingPermutations P.D
        (fun i => constraintSet u x πi i))
      (fun σ => Lemma55Event σ b b' u πi)
      (fun x π σ =>
        ∀ i,
          indexedIntervalSum
            (applyPositionPerm (applyPositionPerm σ π) (πi i))
            (u i) (x i) = 0)
      (P.D ^ (14 * P.D ^ 2))
      (fun x => chainUpperBound p s (chainConstant P.D) (tailSizes b' x))
      (lemma43LHS p s P.D (chainConstant P.D))
    · intro σ _ h
      rcases h with ⟨x, hx, π, hπ, hz⟩
      obtain ⟨π', hπ', hz'⟩ :=
        lemma55_reduce_to_interesting σ b b' u x πi ⟨π, hπ, hz⟩
      exact ⟨x, hx, π', hπ', hz'⟩
    · intro x _
      exact interestingPermutations_card_le hD7 b b' hgap u x hu πi hfix
    · intro x hx π _
      rw [hs]
      exact lemma55_fixed_x_pi_mass_le hα0 hαh P hp S hreg b b' hb2 hgap
        u x hu hx πi hfix π
    · apply lemma55_chainUpperBound_sum_le hCpos.le
      · intro x hx
        exact Section5.tailSizes_valid b b' hb2 hgap x hx hs
      · intro x hx y hy hxy
        have hxv := fun i => (Finset.mem_filter.mp hx).2.2 i
        have hyv := fun i => (Finset.mem_filter.mp hy).2.2 i
        funext i
        have h := congrFun hxy i
        have hxi := hxv i
        have hyi := hyv i
        simp only [tailSizes, paperPos] at h hxi hyi
        exact Fin.ext (by omega)
    · intro x _
      exact lemma55_chainUpperBound_nonneg hCpos.le _
  have hs2 : 2 ≤ s := by omega
  have h43 :=
    lemma4_3 P.D hD (chainConstant P.D) hCpos p hp s hs2
  have hn2 := section5_card_ge_two hα0 hαh hreg
  have hbase :
      lemma43Base p s (chainConstant P.D) ≤
        2 * (S.card : ℝ) ^ (-α) := by
    apply Section5.half_ground_lemma43Base_le hn2
    · omega
    · omega
    · exact hCpos.le
    · exact section5_card_over_p hα0 hαh hp hreg
    · exact section5_chainConstant_bound hreg P.D (Or.inr rfl)
  have hbase0 : 0 ≤ lemma43Base p s (chainConstant P.D) := by
    unfold lemma43Base
    positivity
  have hpow :=
    Section5.two_neg_alpha_pow_le_cube
      (n := S.card) (D := P.D) (α := α)
      (by omega) hα0
      (section5Parameters_alphaD hα0 P)
  have hnpos : (0 : ℝ) < S.card := by
    have : (0 : ℕ) < S.card := by omega
    exact_mod_cast this
  have hC := P.Cα_second
  have hnC := hreg.2.1
  have hM : (0 : ℝ) ≤ ((P.D ^ (14 * P.D ^ 2) : ℕ) : ℝ) := by positivity
  calc
    orderingEventMass S (fun σ => Lemma55Event σ b b' u πi)
      ≤ ((P.D ^ (14 * P.D ^ 2) : ℕ) : ℝ) *
          lemma43LHS p s P.D (chainConstant P.D) := hunion
    _ ≤ ((P.D ^ (14 * P.D ^ 2) : ℕ) : ℝ) *
          ((P.D + 1 : ℝ) * (lemma43Base p s (chainConstant P.D)) ^ P.D) :=
        mul_le_mul_of_nonneg_left h43 hM
    _ ≤ ((P.D ^ (14 * P.D ^ 2) : ℕ) : ℝ) *
          ((P.D + 1 : ℝ) * (2 * (S.card : ℝ) ^ (-α)) ^ P.D) := by
        gcongr
    _ ≤ ((P.D ^ (14 * P.D ^ 2) : ℕ) : ℝ) *
          ((P.D + 1 : ℝ) * ((2 : ℝ) ^ P.D / (S.card : ℝ) ^ 3)) := by
        gcongr
    _ = ((P.D + 1 : ℝ) * (2 : ℝ) ^ P.D * (P.D : ℝ) ^ (14 * P.D ^ 2)) /
          (S.card : ℝ) ^ 3 := by
        push_cast
        ring
    _ ≤ (S.card : ℝ) / (S.card : ℝ) ^ 3 := by
        gcongr
        linarith
    _ = 1 / (S.card : ℝ) ^ 2 := by
        field_simp

end

end GrahamRearrangement
