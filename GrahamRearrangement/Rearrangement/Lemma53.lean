module

public import GrahamRearrangement.Rearrangement.Lemma56

@[expose] public section

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Lemma 5.3

The blocked-choice event is split into the right-extending event E₁ and the
left-extending event E₂, bounded by Lemmas 5.5 and 5.6 respectively.
-/

noncomputable section

theorem swap_fixedOutside
    {n : ℕ} (b b' y : Fin n)
    (hby : paperPos b < paperPos y)
    (hyb' : paperPos y ≤ paperPos b') :
    FixedOutside b b' (Equiv.swap b y) := by
  intro i hi
  have hib : i ≠ b := by
    intro h
    subst h
    rcases hi with h | h <;> omega
  have hiy : i ≠ y := by
    intro h
    subst h
    rcases hi with h | h <;> omega
  exact Equiv.swap_apply_of_ne_of_ne hib hiy

/-- An admissible permutation fixing every position below `b` moves a position
of `{b,...,b+5D}` at most `5D` places, and never below `b`. -/
theorem lemma53_admissible_moves_locally
    {n D : ℕ} (b : Fin n) (π : Equiv.Perm (Fin n))
    (hadm : IsAdmissiblePermutation D π) (hfix : FixedBelow b π)
    (i : Fin n) (hi : b.val ≤ i.val ∧ i.val ≤ b.val + 5 * D) :
    b.val ≤ (π i).val ∧ (π i).val ≤ b.val + 10 * D := by
  rcases hadm with ⟨P, hP, rfl⟩
  by_cases h1 : ∃ q ∈ P, q.1 = i
  · obtain ⟨q, hq, rfl⟩ := h1
    have hlen := hP.2 q hq
    rw [(collectionPerm_apply_pair hP hq).1]
    simp only [paperPos] at hlen
    omega
  · by_cases h2 : ∃ q ∈ P, q.2 = i
    · obtain ⟨q, hq, rfl⟩ := h2
      have hact := collectionPerm_apply_pair hP hq
      have hlen := hP.2 q hq
      simp only [paperPos] at hlen
      have hq1b : b.val ≤ q.1.val := by
        by_contra hlt
        have hfx := hfix q.1 (by simp only [paperPos]; omega)
        rw [hact.1] at hfx
        rw [hfx] at hlen
        omega
      rw [hact.2]
      omega
    · have hfx : collectionPerm P i = i := by
        apply collectionPerm_apply_of_forall_ne P i
        intro q hq
        constructor
        · intro h
          exact h1 ⟨q, hq, h.symm⟩
        · intro h
          exact h2 ⟨q, hq, h.symm⟩
      rw [hfx]
      omega

/-- Failure of B₀ says that the subset-sum map is injective on the local
5D-window even after applying any admissible permutation fixing the prefix.
This is the precise local-injectivity statement used in the proof of Lemma 5.3. -/
theorem local_subset_sum_injective_after_admissible
    {n p D : ℕ}
    (σ : Fin n → ZMod p) (b : Fin n)
    (hb : b ∈ badRightEndpoints σ)
    (hbfar : paperPos b + 30 * D ≤ n)
    (h0 : ¬ BadEvent0 D σ)
    (π : Equiv.Perm (Fin n))
    (hadm : IsAdmissiblePermutation D π)
    (hfix : FixedBelow b π)
    {J J' : Finset (Fin n)}
    (hJ : J ⊆ forwardWindow b (5 * D))
    (hJ' : J' ⊆ forwardWindow b (5 * D))
    (hne : J ≠ J') :
    indexSetSum (applyPositionPerm σ π) J ≠
      indexSetSum (applyPositionPerm σ π) J' := by
  intro heq
  have himage : ∀ K : Finset (Fin n), K ⊆ forwardWindow b (5 * D) →
      K.image π ⊆ forwardWindow b (20 * D) := by
    intro K hK z hz
    rcases Finset.mem_image.1 hz with ⟨w, hw, rfl⟩
    have hw' := hK hw
    simp only [forwardWindow, Finset.mem_filter, Finset.mem_univ,
      true_and] at hw' ⊢
    have := lemma53_admissible_moves_locally b π hadm hfix w hw'
    omega
  have himageNe : J.image π ≠ J'.image π :=
    (Finset.image_injective π.injective).ne hne
  rw [indexSetSum_applyPositionPerm_image,
    indexSetSum_applyPositionPerm_image] at heq
  exact h0 ⟨b, hb, hbfar, J.image π, J'.image π,
    himage J hJ, himage J' hJ', himageNe, heq⟩

theorem local_nonzero_after_admissible
    {n p D : ℕ}
    (σ : Fin n → ZMod p) (b : Fin n)
    (hb : b ∈ badRightEndpoints σ)
    (hbfar : paperPos b + 30 * D ≤ n)
    (h0 : ¬ BadEvent0 D σ)
    (π : Equiv.Perm (Fin n))
    (hadm : IsAdmissiblePermutation D π)
    (hfix : FixedBelow b π)
    {J : Finset (Fin n)}
    (hJne : J.Nonempty)
    (hJ : J ⊆ forwardWindow b (5 * D)) :
    indexSetSum (applyPositionPerm σ π) J ≠ 0 := by
  have h :=
    local_subset_sum_injective_after_admissible
      σ b hb hbfar h0 π hadm hfix hJ (Finset.empty_subset _)
      hJne.ne_empty
  simpa [indexSetSum] using h

def RightBlockedWitness {n p D : ℕ}
    (σ : Fin n → ZMod p) (b : Fin n)
    (π : Equiv.Perm (Fin n)) (y : Fin n) : Prop :=
  ∃ s t : Fin n,
    paperPos b < paperPos s ∧ paperPos s ≤ paperPos y ∧
    paperPos b + 5 * D < paperPos t ∧
    indexedIntervalSum
      (applyPositionPerm (applyPositionPerm σ π) (Equiv.swap b y))
      s t = 0

def LeftBlockedWitness {n p : ℕ}
    (σ : Fin n → ZMod p) (b : Fin n)
    (π : Equiv.Perm (Fin n)) (y : Fin n) : Prop :=
  ∃ s t : Fin n,
    paperPos s < paperPos b ∧
    paperPos b ≤ paperPos t ∧ paperPos t < paperPos y ∧
    indexedIntervalSum
      (applyPositionPerm (applyPositionPerm σ π) (Equiv.swap b y))
      s t = 0

/-- The transposition `(b y)` with `b < y ≤ b+5D` maps subsets of the window
`{b,...,b+5D}` into the same window. -/
theorem lemma53_swap_image_subset_window {n D : ℕ} (b y : Fin n)
    (K : Finset (Fin n))
    (hy : b.val < y.val ∧ y.val ≤ b.val + 5 * D)
    (hK : ∀ w ∈ K, b.val ≤ w.val ∧ w.val ≤ b.val + 5 * D) :
    K.image (Equiv.swap b y) ⊆ forwardWindow b (5 * D) := by
  intro z hz
  rcases Finset.mem_image.1 hz with ⟨w, hw, rfl⟩
  have hw' := hK w hw
  simp only [forwardWindow, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases eq_or_ne w b with rfl | hwb
  · rw [Equiv.swap_apply_left]
    omega
  · rcases eq_or_ne w y with rfl | hwy
    · rw [Equiv.swap_apply_right]
      omega
    · rw [Equiv.swap_apply_of_ne_of_ne hwb hwy]
      omega

/-- This is the dichotomy in the third and fourth paragraphs of the proof of Lemma 5.3:
a blocked interval cannot be wholly contained in the 5D-window, so it must
extend to the right or to the left. -/
theorem blocked_witness_has_side
    {n p D : ℕ}
    (σ : Fin n → ZMod p) (b : Fin n)
    (hb : b ∈ badRightEndpoints σ)
    (hbfar : paperPos b + 30 * D ≤ n)
    (h0 : ¬ BadEvent0 D σ)
    (π : Equiv.Perm (Fin n))
    (hadm : IsAdmissiblePermutation D π)
    (hfix : FixedBelow b π)
    {y : Fin n} (hy : y ∈ blockedCandidates D σ b π) :
    RightBlockedWitness (D := D) σ b π y ∨
      LeftBlockedWitness σ b π y := by
  classical
  have hblocked : IsBlockedAt D σ b π y := (Finset.mem_filter.1 hy).2
  rcases hblocked with ⟨hby, hy5, s, t, hs2, hst, hzero, hcross⟩
  by_cases hright : paperPos b + 5 * D < paperPos t
  · left
    refine ⟨s, t, ?_, ?_, hright, hzero⟩ <;> omega
  · by_cases hleft : paperPos s < paperPos b
    · right
      refine ⟨s, t, hleft, ?_, ?_, hzero⟩ <;> omega
    · exfalso
      simp only [paperPos] at hby hy5 hst hright hleft
      apply local_nonzero_after_admissible σ b hb hbfar h0 π hadm hfix
        (J := (indexInterval s t).image (Equiv.swap b y))
      · refine ⟨Equiv.swap b y s, Finset.mem_image_of_mem _ ?_⟩
        simp only [indexInterval, Finset.mem_filter, Finset.mem_univ,
          true_and]
        omega
      · apply lemma53_swap_image_subset_window b y _ (by omega)
        intro w hw
        simp only [indexInterval, Finset.mem_filter, Finset.mem_univ,
          true_and] at hw
        omega
      · rw [← indexSetSum_applyPositionPerm_image, indexSetSum_indexInterval]
        exact hzero

/-- A finset of size at least `D` contains the range of an injective `D`-tuple. -/
theorem lemma53_exists_injective_tuple {n D : ℕ}
    (T : Finset (Fin n)) (hT : D ≤ T.card) :
    ∃ y : Fin D → Fin n, Function.Injective y ∧ ∀ i, y i ∈ T := by
  obtain ⟨T', hT'T, hT'card⟩ := Finset.exists_subset_card_eq hT
  exact ⟨fun i => T'.orderEmbOfFin hT'card i,
    (T'.orderEmbOfFin hT'card).injective,
    fun i => hT'T (Finset.orderEmbOfFin_mem T' hT'card i)⟩

/-- At the pigeonhole stage only the blocked choices y_i are known to be
distinct. Distinctness of the far endpoints is proved separately below, just
as in the paper. -/
theorem blocked_family_side_split
    {n p D : ℕ}
    (σ : Fin n → ZMod p) (b : Fin n)
    (hb : b ∈ badRightEndpoints σ)
    (hbfar : paperPos b + 30 * D ≤ n)
    (h0 : ¬ BadEvent0 D σ)
    (π : Equiv.Perm (Fin n))
    (hadm : IsAdmissiblePermutation D π)
    (hfix : FixedBelow b π)
    (hblocked :
      2 * D ≤ (blockedCandidates D σ b π).card) :
    (∃ y : Fin D → Fin n,
      Function.Injective y ∧
      ∀ i, y i ∈ blockedCandidates D σ b π ∧
        RightBlockedWitness (D := D) σ b π (y i)) ∨
    (∃ y : Fin D → Fin n,
      Function.Injective y ∧
      ∀ i, y i ∈ blockedCandidates D σ b π ∧
        LeftBlockedWitness σ b π (y i)) := by
  classical
  have hcover :
      blockedCandidates D σ b π ⊆
        (blockedCandidates D σ b π).filter
            (RightBlockedWitness (D := D) σ b π) ∪
          (blockedCandidates D σ b π).filter
            (LeftBlockedWitness σ b π) := by
    intro y hy
    rcases blocked_witness_has_side σ b hb hbfar h0 π hadm hfix hy with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hy, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hy, h⟩)
  have hcard := le_trans hblocked
    (le_trans (Finset.card_le_card hcover) (Finset.card_union_le _ _))
  rcases le_or_gt D ((blockedCandidates D σ b π).filter
      (RightBlockedWitness (D := D) σ b π)).card with hR | hR
  · left
    obtain ⟨y, hyinj, hy⟩ := lemma53_exists_injective_tuple _ hR
    exact ⟨y, hyinj, fun i => Finset.mem_filter.1 (hy i)⟩
  · right
    obtain ⟨y, hyinj, hy⟩ := lemma53_exists_injective_tuple (D := D)
      ((blockedCandidates D σ b π).filter
        (LeftBlockedWitness σ b π)) (by omega)
    exact ⟨y, hyinj, fun i => Finset.mem_filter.1 (hy i)⟩

/-- The distinctness argument for the right endpoints t_i in E₁, exactly as
on pp. 25--26 of the paper. -/
theorem right_witness_endpoints_injective
    {n p D : ℕ}
    (σ : Fin n → ZMod p) (b b' : Fin n)
    (hgap : paperPos b' - paperPos b = 5 * D)
    (hb : b ∈ badRightEndpoints σ)
    (hbfar : paperPos b + 30 * D ≤ n)
    (h0 : ¬ BadEvent0 D σ)
    (π : Equiv.Perm (Fin n))
    (hadm : IsAdmissiblePermutation D π)
    (hfix : FixedBelow b π)
    (y s t : Fin D → Fin n)
    (hyinj : Function.Injective y)
    (hw : ∀ i,
      paperPos b < paperPos (y i) ∧
      paperPos (y i) ≤ paperPos b' ∧
      paperPos b < paperPos (s i) ∧
      paperPos (s i) ≤ paperPos (y i) ∧
      paperPos b' < paperPos (t i) ∧
      indexedIntervalSum
        (applyPositionPerm
          (applyPositionPerm σ π) (Equiv.swap b (y i)))
        (s i) (t i) = 0) :
    Function.Injective t := by
  have claim : ∀ i j, paperPos (y i) < paperPos (y j) → t i ≠ t j := by
    intro i j hij htij
    have hDpos : 0 < D := Fin.pos i
    obtain ⟨hyi1, hyi2, hsi1, hsi2, hti, hzi⟩ := hw i
    obtain ⟨hyj1, hyj2, hsj1, hsj2, htj, hzj⟩ := hw j
    have hsplit_i := swap_interval_split_right (applyPositionPerm σ π)
      b b' (y i) (s i) (t i) hyi1 hyi2 hsi1 hsi2 hti
    have hsplit_j := swap_interval_split_right (applyPositionPerm σ π)
      b b' (y j) (s j) (t j) hyj1 hyj2 hsj1 hsj2 htj
    rw [hzi] at hsplit_i
    rw [hzj, ← htij] at hsplit_j
    simp only [paperPos] at hgap hyi1 hyi2 hsi1 hsi2 hyj1 hyj2 hsj1 hsj2 hij
    have hb' : b'.val = b.val + 5 * D := by omega
    have hyji : y j ≠ y i := by
      intro h
      rw [h] at hij
      omega
    have hyjb : y j ≠ b := by
      intro h
      rw [h] at hyj1
      omega
    apply local_subset_sum_injective_after_admissible σ b hb hbfar h0 π hadm
      hfix
      (J := (indexInterval (s i) b').image (Equiv.swap b (y i)))
      (J' := (indexInterval (s j) b').image (Equiv.swap b (y j)))
    · apply lemma53_swap_image_subset_window b (y i) _ (by omega)
      intro w hw
      simp only [indexInterval, Finset.mem_filter, Finset.mem_univ,
        true_and] at hw
      omega
    · apply lemma53_swap_image_subset_window b (y j) _ (by omega)
      intro w hw
      simp only [indexInterval, Finset.mem_filter, Finset.mem_univ,
        true_and] at hw
      omega
    · intro heq
      have hin : y j ∈ (indexInterval (s i) b').image (Equiv.swap b (y i)) := by
        refine Finset.mem_image.2 ⟨y j, ?_, Equiv.swap_apply_of_ne_of_ne hyjb hyji⟩
        simp only [indexInterval, Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      rw [heq] at hin
      rcases Finset.mem_image.1 hin with ⟨w, hw, hsw⟩
      rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right] at hsw
      rw [hsw] at hw
      simp only [indexInterval, Finset.mem_filter, Finset.mem_univ,
        true_and] at hw
      omega
    · exact add_right_cancel (hsplit_i.symm.trans hsplit_j)
  intro i j hij
  by_contra hne
  have hyne : y i ≠ y j := fun h => hne (hyinj h)
  have hpne : paperPos (y i) ≠ paperPos (y j) := by
    intro h
    apply hyne
    apply Fin.ext
    simp only [paperPos] at h
    omega
  rcases lt_or_gt_of_ne hpne with hlt | hgt
  · exact claim i j hlt hij
  · exact claim j i hgt hij.symm

/-- The analogous distinctness argument for the left endpoints s_i in E₂. -/
theorem left_witness_endpoints_injective
    {n p D : ℕ}
    (σ : Fin n → ZMod p) (b b' : Fin n)
    (hgap : paperPos b' - paperPos b = 5 * D)
    (hb : b ∈ badRightEndpoints σ)
    (hbfar : paperPos b + 30 * D ≤ n)
    (h0 : ¬ BadEvent0 D σ)
    (π : Equiv.Perm (Fin n))
    (hadm : IsAdmissiblePermutation D π)
    (hfix : FixedBelow b π)
    (y s t : Fin D → Fin n)
    (hyinj : Function.Injective y)
    (hw : ∀ i,
      paperPos b < paperPos (y i) ∧
      paperPos (y i) ≤ paperPos b' ∧
      paperPos (s i) < paperPos b ∧
      paperPos b ≤ paperPos (t i) ∧
      paperPos (t i) < paperPos (y i) ∧
      indexedIntervalSum
        (applyPositionPerm
          (applyPositionPerm σ π) (Equiv.swap b (y i)))
        (s i) (t i) = 0) :
    Function.Injective s := by
  have claim : ∀ i j, paperPos (y i) < paperPos (y j) → s i ≠ s j := by
    intro i j hij hsij
    have hDpos : 0 < D := Fin.pos i
    obtain ⟨hyi1, hyi2, hsi, hti1, hti2, hzi⟩ := hw i
    obtain ⟨hyj1, hyj2, hsj, htj1, htj2, hzj⟩ := hw j
    have hsplit_i := swap_interval_split_left (applyPositionPerm σ π)
      b (y i) (s i) (t i) hyi1 hsi hti1 hti2
    have hsplit_j := swap_interval_split_left (applyPositionPerm σ π)
      b (y j) (s j) (t j) hyj1 hsj htj1 htj2
    rw [hzi] at hsplit_i
    rw [hzj, ← hsij] at hsplit_j
    simp only [paperPos] at hgap hyi1 hyi2 hti1 hti2 hyj1 hyj2 htj1 htj2 hij
    have hb' : b'.val = b.val + 5 * D := by omega
    have hyji : y j ≠ y i := by
      intro h
      rw [h] at hij
      omega
    have hyjb : y j ≠ b := by
      intro h
      rw [h] at hyj1
      omega
    apply local_subset_sum_injective_after_admissible σ b hb hbfar h0 π hadm
      hfix
      (J := (indexInterval b (t i)).image (Equiv.swap b (y i)))
      (J' := (indexInterval b (t j)).image (Equiv.swap b (y j)))
    · apply lemma53_swap_image_subset_window b (y i) _ (by omega)
      intro w hw
      simp only [indexInterval, Finset.mem_filter, Finset.mem_univ,
        true_and] at hw
      omega
    · apply lemma53_swap_image_subset_window b (y j) _ (by omega)
      intro w hw
      simp only [indexInterval, Finset.mem_filter, Finset.mem_univ,
        true_and] at hw
      omega
    · intro heq
      have hin : y j ∈ (indexInterval b (t j)).image (Equiv.swap b (y j)) := by
        refine Finset.mem_image.2 ⟨b, ?_, Equiv.swap_apply_left b (y j)⟩
        simp only [indexInterval, Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      rw [← heq] at hin
      rcases Finset.mem_image.1 hin with ⟨w, hw, hsw⟩
      rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_of_ne_of_ne hyjb hyji] at hsw
      rw [hsw] at hw
      simp only [indexInterval, Finset.mem_filter, Finset.mem_univ,
        true_and] at hw
      omega
    · exact add_left_cancel (hsplit_i.symm.trans hsplit_j)
  intro i j hij
  by_contra hne
  have hyne : y i ≠ y j := fun h => hne (hyinj h)
  have hpne : paperPos (y i) ≠ paperPos (y j) := by
    intro h
    apply hyne
    apply Fin.ext
    simp only [paperPos] at h
    omega
  rcases lt_or_gt_of_ne hpne with hlt | hgt
  · exact claim i j hlt hij
  · exact claim j i hgt hij.symm

theorem badEvent3_core_side_reduction
    {n p D : ℕ} (hD : 0 < D)
    (σ : Fin n → ZMod p)
    (h3 : BadEvent3 D σ)
    (h0 : ¬ BadEvent0 D σ)
    (h1 : ¬ BadEvent1 D σ) :
    RightRepairEvent D σ ∨ LeftRepairEvent D σ := by
  classical
  rcases h3 with ⟨b, hb, π, hπadm, hπfix, hblocked⟩
  have hbfar : paperPos b + 30 * D ≤ n := by
    by_contra h
    exact h1 ⟨b, hb, by omega⟩
  have hb3 := badRightEndpoint_ge_three hb
  have hb'lt : b.val + 5 * D < n := by
    simp only [paperPos] at hbfar
    omega
  have hgap : paperPos (⟨b.val + 5 * D, hb'lt⟩ : Fin n) - paperPos b = 5 * D := by
    simp only [paperPos]
    omega
  have hb'pos : paperPos (⟨b.val + 5 * D, hb'lt⟩ : Fin n) = paperPos b + 5 * D := by
    simp only [paperPos]
    omega
  have hyb : ∀ y ∈ blockedCandidates D σ b π,
      paperPos b < paperPos y ∧ paperPos y ≤ paperPos b + 5 * D := by
    intro y hy
    have h := (Finset.mem_filter.1 hy).2
    exact ⟨h.1, h.2.1⟩
  rcases blocked_family_side_split σ b hb hbfar h0 π hπadm hπfix hblocked with
    ⟨y, hyinj, hyw⟩ | ⟨y, hyinj, hyw⟩
  · choose s t hs using fun i => (hyw i).2
    have hw : ∀ i,
        paperPos b < paperPos (y i) ∧
        paperPos (y i) ≤ paperPos (⟨b.val + 5 * D, hb'lt⟩ : Fin n) ∧
        paperPos b < paperPos (s i) ∧
        paperPos (s i) ≤ paperPos (y i) ∧
        paperPos (⟨b.val + 5 * D, hb'lt⟩ : Fin n) < paperPos (t i) ∧
        indexedIntervalSum
          (applyPositionPerm
            (applyPositionPerm σ π) (Equiv.swap b (y i)))
          (s i) (t i) = 0 := by
      intro i
      obtain ⟨h1, h2, h3, h4⟩ := hs i
      obtain ⟨h5, h6⟩ := hyb (y i) (hyw i).1
      exact ⟨h5, by omega, h1, h2, by omega, h4⟩
    have htinj := right_witness_endpoints_injective σ b _ hgap hb hbfar h0 π
      hπadm hπfix y s t hyinj hw
    obtain ⟨ρ, hρ⟩ := Section5.exists_sorting_perm t htinj
    left
    refine ⟨b, ⟨b.val + 5 * D, hb'lt⟩, by omega, hbfar, hgap, y ∘ ρ, s ∘ ρ,
      fun i => ⟨(hw (ρ i)).1, (hw (ρ i)).2.1⟩,
      fun i => ⟨(hw (ρ i)).2.2.1, le_trans (hw (ρ i)).2.2.2.1 (hw (ρ i)).2.1⟩,
      t ∘ ρ, ?_, π, hπadm, fun i => (hw (ρ i)).2.2.2.2.2⟩
    simp only [tailTuples, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hρ, fun i => (hw (ρ i)).2.2.2.2.1⟩
  · choose s t hs using fun i => (hyw i).2
    have hw : ∀ i,
        paperPos b < paperPos (y i) ∧
        paperPos (y i) ≤ paperPos (⟨b.val + 5 * D, hb'lt⟩ : Fin n) ∧
        paperPos (s i) < paperPos b ∧
        paperPos b ≤ paperPos (t i) ∧
        paperPos (t i) < paperPos (y i) ∧
        indexedIntervalSum
          (applyPositionPerm
            (applyPositionPerm σ π) (Equiv.swap b (y i)))
          (s i) (t i) = 0 := by
      intro i
      obtain ⟨h1, h2, h3, h4⟩ := hs i
      obtain ⟨h5, h6⟩ := hyb (y i) (hyw i).1
      exact ⟨h5, by omega, h1, h2, h3, h4⟩
    have hsinj := left_witness_endpoints_injective σ b _ hgap hb hbfar h0 π
      hπadm hπfix y s t hyinj hw
    obtain ⟨ρ, hρ⟩ := Section5.exists_sorting_perm s hsinj
    right
    refine ⟨b, ⟨b.val + 5 * D, hb'lt⟩, by omega, hbfar, hgap, y ∘ ρ, t ∘ ρ,
      fun i => ⟨(hw (ρ i)).1, (hw (ρ i)).2.1⟩,
      fun i => ⟨(hw (ρ i)).2.2.2.1,
        lt_of_lt_of_le (hw (ρ i)).2.2.2.2.1 (hw (ρ i)).2.1⟩,
      s ∘ ρ, ?_, π, hπadm, fun i => (hw (ρ i)).2.2.2.2.2⟩
    simp only [headTuples, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hρ, fun i => (hw (ρ i)).2.2.1⟩

def rightRepairAtom {n p D : ℕ}
    (θ : RepairParams n D) (σ : Fin n → ZMod p) : Prop :=
  Lemma55Event σ θ.b' θ.u
    (fun i => Equiv.swap θ.b (θ.y i))

def leftRepairAtom {n p D : ℕ}
    (θ : RepairParams n D) (σ : Fin n → ZMod p) : Prop :=
  Lemma56Event σ θ.b θ.u
    (fun i => Equiv.swap θ.b (θ.y i))

/-- The final arithmetic shared by the bounds for E₁ and E₂. -/
theorem lemma53_union_arith
    {α : ℝ} (P : Section5Parameters α)
    {p : ℕ} (S : Finset (ZMod p)) (hreg : Section5Regime P p S)
    (N : ℕ) (hN : N ≤ S.card * (5 * P.D) ^ (2 * P.D)) :
    (N : ℝ) * (1 / (S.card : ℝ) ^ 2) ≤ 1 / 100 := by
  have h50 := section5_card_ge_fiftyD hreg
  have hnpos : (0 : ℝ) < S.card := by
    have : 0 < S.card := by
      have := P.Cα_pos
      have h := hreg.2.1
      exact_mod_cast (lt_of_lt_of_le this h)
    exact_mod_cast this
  have h100 := P.second_ge_100
  have hC := P.Cα_second
  have hn := hreg.2.1
  have hNR : (N : ℝ) ≤ (S.card : ℝ) * (5 * P.D : ℝ) ^ (2 * P.D) := by
    exact_mod_cast hN
  calc
    (N : ℝ) * (1 / (S.card : ℝ) ^ 2)
      ≤ (S.card : ℝ) * (5 * P.D : ℝ) ^ (2 * P.D) * (1 / (S.card : ℝ) ^ 2) := by
        gcongr
    _ = (5 * P.D : ℝ) ^ (2 * P.D) / (S.card : ℝ) := by
        field_simp
    _ ≤ 1 / 100 := by
        rw [div_le_iff₀ hnpos]
        linarith

theorem rightRepairEvent_mass
    {α : ℝ} (hα0 : 0 < α) (hαh : α < 1 / 2)
    (P : Section5Parameters α)
    {p : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hreg : Section5Regime P p S) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    orderingEventMass S (RightRepairEvent P.D) ≤
      (1 / 100 : ℝ) := by
  let : NeZero p := ⟨hp.ne_zero⟩
  have hD := section5Parameters_D_pos hα0 hαh P
  have hmass :
      orderingEventMass S (RightRepairEvent P.D) ≤
        ((rightRepairParameters S.card P.D).card : ℝ) *
          (1 / (S.card : ℝ) ^ 2) := by
    unfold orderingEventMass
    apply Section5.witness_union_bound
      (indexedOrderings S) (rightRepairParameters S.card P.D)
      (RightRepairEvent P.D)
      (fun θ σ => Lemma55Event σ θ.b' θ.u
        (fun i => Equiv.swap θ.b (θ.y i)))
    · intro σ _ h
      rcases h with ⟨b, b', hb2, hbfar, hgap, y, u, hy, hu, hev⟩
      exact ⟨⟨b, b', y, u⟩,
        mem_rightRepairParameters.2 ⟨hb2, hbfar, hgap, hy, hu⟩, hev⟩
    · intro θ hθ
      obtain ⟨hb2, hbfar, hgap, hy, hu⟩ := mem_rightRepairParameters.1 hθ
      exact lemma5_5 hα0 hαh P hp S hreg θ.b θ.b' hb2 hgap θ.u
        (fun i => ⟨(hu i).1.le, (hu i).2⟩)
        (fun i => Equiv.swap θ.b (θ.y i))
        (fun i => swap_fixedOutside θ.b θ.b' (θ.y i) (hy i).1 (hy i).2)
  exact le_trans hmass (lemma53_union_arith P S hreg _
    (rightRepairParameters_card_le S.card P.D hD))

theorem leftRepairEvent_mass
    {α : ℝ} (hα0 : 0 < α) (hαh : α < 1 / 2)
    (P : Section5Parameters α)
    {p : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hreg : Section5Regime P p S) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    orderingEventMass S (LeftRepairEvent P.D) ≤
      (1 / 100 : ℝ) := by
  let : NeZero p := ⟨hp.ne_zero⟩
  have hD := section5Parameters_D_pos hα0 hαh P
  have hmass :
      orderingEventMass S (LeftRepairEvent P.D) ≤
        ((leftRepairParameters S.card P.D).card : ℝ) *
          (1 / (S.card : ℝ) ^ 2) := by
    unfold orderingEventMass
    apply Section5.witness_union_bound
      (indexedOrderings S) (leftRepairParameters S.card P.D)
      (LeftRepairEvent P.D)
      (fun θ σ => Lemma56Event σ θ.b θ.u
        (fun i => Equiv.swap θ.b (θ.y i)))
    · intro σ _ h
      rcases h with ⟨b, b', hb2, hbfar, hgap, y, u, hy, hu, hev⟩
      exact ⟨⟨b, b', y, u⟩,
        mem_leftRepairParameters.2 ⟨hb2, hbfar, hgap, hy, hu⟩, hev⟩
    · intro θ hθ
      obtain ⟨hb2, hbfar, hgap, hy, hu⟩ := mem_leftRepairParameters.1 hθ
      have hb'le : paperPos θ.b' ≤ S.card - 2 := by omega
      exact lemma5_6 hα0 hαh P hp S hreg θ.b θ.b' hb2 hb'le hgap θ.u
        (fun i => ⟨(hu i).1, (hu i).2.le⟩)
        (fun i => Equiv.swap θ.b (θ.y i))
        (fun i => swap_fixedOutside θ.b θ.b' (θ.y i) (hy i).1 (hy i).2)
  exact le_trans hmass (lemma53_union_arith P S hreg _
    (leftRepairParameters_card_le S.card P.D hD))

/-- Lemma 5.3. -/
theorem lemma5_3
    {α : ℝ} (hα0 : 0 < α) (hαh : α < 1 / 2)
    (P : Section5Parameters α)
    {p : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hreg : Section5Regime P p S) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    orderingEventMass S (BadEvent3 P.D) ≤
      (1 / 25 : ℝ) := by
  let : NeZero p := ⟨hp.ne_zero⟩
  have hD := section5Parameters_D_pos hα0 hαh P
  have hcore :
      uniformMass (indexedOrderings S)
          (fun σ => BadEvent3 P.D σ ∧ ¬ BadEvent0 P.D σ ∧
            ¬ BadEvent1 P.D σ) ≤ 2 / 100 := by
    calc
      uniformMass (indexedOrderings S)
          (fun σ => BadEvent3 P.D σ ∧ ¬ BadEvent0 P.D σ ∧
            ¬ BadEvent1 P.D σ)
        ≤ uniformMass (indexedOrderings S)
            (fun σ => RightRepairEvent P.D σ ∨ LeftRepairEvent P.D σ) := by
          apply uniformMass_mono
          intro σ h
          exact badEvent3_core_side_reduction hD σ h.1 h.2.1 h.2.2
      _ ≤ uniformMass (indexedOrderings S) (RightRepairEvent P.D) +
          uniformMass (indexedOrderings S) (LeftRepairEvent P.D) :=
          uniformMass_or_le_add _ _ _
      _ ≤ 1 / 100 + 1 / 100 :=
          add_le_add (rightRepairEvent_mass hα0 hαh P hp S hreg)
            (leftRepairEvent_mass hα0 hαh P hp S hreg)
      _ = 2 / 100 := by norm_num
  have htotal := uniformMass_le_two_exceptions (indexedOrderings S)
    (BadEvent3 P.D) (BadEvent0 P.D) (BadEvent1 P.D) (2 / 100) hcore
  have h0 := lemma5_4 hα0 hαh P hp S hreg
  have h1 := lemma5_1 hα0 hαh P hp S hreg
  unfold orderingEventMass at h0 h1 ⊢
  linarith

end

end GrahamRearrangement
