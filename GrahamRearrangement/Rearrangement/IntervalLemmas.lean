module

public import GrahamRearrangement.Rearrangement.Definitions

@[expose] public section

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Section 5: interval and partial-sum lemmas

These are the bookkeeping equivalences connecting the introduction's list definition
of a valid ordering with the paper's interval notation in Section 5.
-/

section ListIntervals

variable {G : Type*} [AddCommGroup G]

def listPrefixSum (xs : List G) (k : ℕ) : G :=
  (xs.take k).sum

theorem getElem_partialSums (xs : List G) (i : ℕ)
    (hi : i < xs.length) :
    (partialSums xs)[i]'(by simpa [length_partialSums] using hi) =
      listPrefixSum xs (i + 1) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
      cases i with
      | zero =>
          simp [partialSums, listPrefixSum]
      | succ i =>
          have hi' : i < xs.length := by simpa using hi
          simp [partialSums, listPrefixSum, ih i hi', add_assoc]

/-- Sum on the slice [a,b] is the difference of the two relevant prefix sums. -/
theorem listIntervalSum_eq_prefix_sub (xs : List G) (a b : ℕ)
    (hab : a ≤ b) (hb : b < xs.length) :
    listIntervalSum xs a b =
      listPrefixSum xs (b + 1) - listPrefixSum xs a := by
  have htake : xs.take (b + 1) = xs.take a ++ (xs.drop a).take (b + 1 - a) := by
    rw [← List.take_add]
    congr 1
    omega
  unfold listIntervalSum listPrefixSum
  rw [htake, List.sum_append]
  abel

theorem listPrefix_eq_iff_interval_zero (xs : List G)
    (a b : ℕ) (hab : a ≤ b) (hb : b < xs.length) :
    listPrefixSum xs a = listPrefixSum xs (b + 1) ↔
      listIntervalSum xs a b = 0 := by
  rw [listIntervalSum_eq_prefix_sub xs a b hab hb]
  exact eq_comm.trans sub_eq_zero.symm

theorem partialSums_nodup_iff_prefix (xs : List G) :
    (partialSums xs).Nodup ↔
      ∀ i j : ℕ, i < j → j < xs.length →
        listPrefixSum xs (i + 1) ≠ listPrefixSum xs (j + 1) := by
  rw [List.nodup_iff_injective_get]
  constructor
  · intro hinj i j hij hj heq
    have hi : i < xs.length := lt_trans hij hj
    have hget : (partialSums xs).get ⟨i, by simpa using hi⟩ =
        (partialSums xs).get ⟨j, by simpa using hj⟩ := by
      simp only [List.get_eq_getElem]
      rw [getElem_partialSums xs i hi, getElem_partialSums xs j hj]
      exact heq
    have := congrArg Fin.val (hinj hget)
    simp only at this
    omega
  · intro hp i j hij
    simp only [List.get_eq_getElem] at hij
    have hi : i.val < xs.length := by simpa using i.isLt
    have hj : j.val < xs.length := by simpa using j.isLt
    rw [getElem_partialSums xs i hi, getElem_partialSums xs j hj] at hij
    apply Fin.ext
    rcases lt_trichotomy i.val j.val with h | h | h
    · exact absurd hij (hp i j h hj)
    · exact h
    · exact absurd hij.symm (hp j i h hi)

end ListIntervals

section IndexedIntervals

theorem indexedIntervalSum_eq_prefix_sub {n p : ℕ}
    (σ : Fin n → ZMod p) (a b : Fin n)
    (hab : a.val ≤ b.val) :
    indexedIntervalSum σ a b =
      listPrefixSum (indexedToList σ) (b.val + 1) -
        listPrefixSum (indexedToList σ) a.val := by
  rw [indexedIntervalSum_eq_listIntervalSum σ a b hab]
  apply listIntervalSum_eq_prefix_sub
  · exact hab
  · simp [indexedToList]

theorem indexed_interval_zero_iff_prefix_eq {n p : ℕ}
    (σ : Fin n → ZMod p) (a b : Fin n)
    (hab : a.val ≤ b.val) :
    indexedIntervalSum σ a b = 0 ↔
      listPrefixSum (indexedToList σ) a.val =
        listPrefixSum (indexedToList σ) (b.val + 1) := by
  rw [indexedIntervalSum_eq_prefix_sub σ a b hab, sub_eq_zero]
  exact eq_comm

theorem interval_sum_eq_halfOpen_add_endpoint {n p : ℕ}
    (σ : Fin n → ZMod p) (a b : Fin n)
    (hab : a.val ≤ b.val) :
    indexedIntervalSum σ a b =
      indexSetSum σ (indexHalfOpen a b) + σ b := by
  have hsplit : indexInterval a b = insert b (indexHalfOpen a b) := by
    ext i
    simp only [indexInterval, indexHalfOpen, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_insert]
    constructor
    · intro h
      by_cases hib : i = b
      · exact Or.inl hib
      · right
        have : i.val ≠ b.val := fun h' => hib (Fin.ext h')
        omega
    · rintro (rfl | h)
      · exact ⟨hab, le_rfl⟩
      · omega
  have hb : b ∉ indexHalfOpen a b := by
    simp [indexHalfOpen]
  rw [← indexSetSum_indexInterval, hsplit]
  unfold indexSetSum
  rw [Finset.sum_insert hb, add_comm]

theorem indexed_singleton_sum {n p : ℕ}
    (σ : Fin n → ZMod p) (a : Fin n) :
    indexedIntervalSum σ a a = σ a := by
  unfold indexedIntervalSum
  simp

/-- Distinct partial sums are equivalent to the Section 5 interval condition,
using 0∉S to discard singleton zero intervals. -/
theorem valid_iff_noZeroPaperSegments {p : ℕ}
    {S : Finset (ZMod p)} (hzero : 0 ∉ S)
    {σ : Fin S.card → ZMod p} (hσ : IsIndexedOrdering S σ) :
    IsValidOrdering S (indexedToList σ) ↔ HasNoZeroPaperSegments σ := by
  have hord := indexedToList_isOrdering hσ
  have hlen : (indexedToList σ).length = S.card := by simp [indexedToList]
  unfold IsValidOrdering
  rw [partialSums_nodup_iff_prefix]
  constructor
  · rintro ⟨-, hprefix⟩ a b ha hab hsum
    unfold paperPos at ha hab
    have hz := (indexed_interval_zero_iff_prefix_eq σ a b (by omega)).1 hsum
    have hne := hprefix (a.val - 1) b.val (by omega) (by rw [hlen]; exact b.isLt)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ a.val)] at hne
    exact hne hz
  · intro hseg
    refine ⟨hord, ?_⟩
    intro i j hij hj heq
    rw [hlen] at hj
    let a : Fin S.card := ⟨i + 1, by omega⟩
    let b : Fin S.card := ⟨j, hj⟩
    have hzi : indexedIntervalSum σ a b = 0 :=
      (indexed_interval_zero_iff_prefix_eq σ a b (by simp only [a, b]; omega)).2 heq
    by_cases hadj : i + 1 = j
    · have hab : a = b := Fin.ext hadj
      rw [hab, indexed_singleton_sum] at hzi
      exact hzero (hzi ▸ (hσ.2 (σ b)).2 ⟨b, rfl⟩)
    · exact hseg a b (by simp [paperPos, a]) (by simp only [paperPos, a, b]; omega) hzi

theorem indexedIntervalSum_after_perm
    {n p : ℕ} (σ : Fin n → ZMod p)
    (π : Equiv.Perm (Fin n)) (a b : Fin n)
    (hab : a.val ≤ b.val) :
    indexedIntervalSum (applyPositionPerm σ π) a b =
      indexSetSum σ ((indexInterval a b).image π) := by
  rw [← indexSetSum_indexInterval]
  exact indexSetSum_applyPositionPerm_image σ π (indexInterval a b)

theorem swap_interval_split_right {n p : ℕ}
    (τ : Fin n → ZMod p) (b b' y s t : Fin n)
    (hby : paperPos b < paperPos y)
    (hyb' : paperPos y ≤ paperPos b')
    (hbs : paperPos b < paperPos s)
    (hsy : paperPos s ≤ paperPos y)
    (hb't : paperPos b' < paperPos t) :
    indexedIntervalSum (applyPositionPerm τ (Equiv.swap b y)) s t =
      indexSetSum τ ((indexInterval s b').image (Equiv.swap b y)) +
        indexSetSum τ (indexOpenClosed b' t) := by
  unfold paperPos at hby hyb' hbs hsy hb't
  rw [← indexSetSum_indexInterval, indexSetSum_applyPositionPerm_image]
  have hsplit : indexInterval s t = indexInterval s b' ∪ indexOpenClosed b' t := by
    ext i
    simp only [indexInterval, indexOpenClosed, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    omega
  have hfix : (indexOpenClosed b' t).image (Equiv.swap b y) = indexOpenClosed b' t := by
    conv_rhs => rw [← Finset.image_id (s := indexOpenClosed b' t)]
    apply Finset.image_congr
    intro i hi
    simp only [Finset.mem_coe, indexOpenClosed, Finset.mem_filter, Finset.mem_univ,
      true_and] at hi
    apply Equiv.swap_apply_of_ne_of_ne
    · intro h
      rw [h] at hi
      omega
    · intro h
      rw [h] at hi
      omega
  have hdisj : Disjoint ((indexInterval s b').image (Equiv.swap b y))
      (indexOpenClosed b' t) := by
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hz1
    simp only [indexInterval, indexOpenClosed, Finset.mem_filter, Finset.mem_univ,
      true_and] at hi hz2
    by_cases hib : i = b
    · rw [hib] at hi
      omega
    by_cases hiy : i = y
    · rw [hiy, Equiv.swap_apply_right] at hz2
      omega
    · rw [Equiv.swap_apply_of_ne_of_ne hib hiy] at hz2
      omega
  rw [hsplit, Finset.image_union, hfix]
  unfold indexSetSum
  rw [Finset.sum_union hdisj]

theorem swap_interval_split_left {n p : ℕ}
    (τ : Fin n → ZMod p) (b y s t : Fin n)
    (hby : paperPos b < paperPos y)
    (hsb : paperPos s < paperPos b)
    (hbt : paperPos b ≤ paperPos t)
    (hty : paperPos t < paperPos y) :
    indexedIntervalSum (applyPositionPerm τ (Equiv.swap b y)) s t =
      indexSetSum τ (indexHalfOpen s b) +
        indexSetSum τ ((indexInterval b t).image (Equiv.swap b y)) := by
  unfold paperPos at hby hsb hbt hty
  rw [← indexSetSum_indexInterval, indexSetSum_applyPositionPerm_image]
  have hsplit : indexInterval s t = indexHalfOpen s b ∪ indexInterval b t := by
    ext i
    simp only [indexInterval, indexHalfOpen, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    omega
  have hfix : (indexHalfOpen s b).image (Equiv.swap b y) = indexHalfOpen s b := by
    conv_rhs => rw [← Finset.image_id (s := indexHalfOpen s b)]
    apply Finset.image_congr
    intro i hi
    simp only [Finset.mem_coe, indexHalfOpen, Finset.mem_filter, Finset.mem_univ,
      true_and] at hi
    apply Equiv.swap_apply_of_ne_of_ne
    · intro h
      rw [h] at hi
      omega
    · intro h
      rw [h] at hi
      omega
  have hdisj : Disjoint (indexHalfOpen s b)
      ((indexInterval b t).image (Equiv.swap b y)) := by
    rw [Finset.disjoint_right]
    intro z hz2 hz1
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hz2
    simp only [indexInterval, indexHalfOpen, Finset.mem_filter, Finset.mem_univ,
      true_and] at hi hz1
    by_cases hib : i = b
    · rw [hib, Equiv.swap_apply_left] at hz1
      omega
    by_cases hiy : i = y
    · rw [hiy] at hi
      omega
    · rw [Equiv.swap_apply_of_ne_of_ne hib hiy] at hz1
      omega
  rw [hsplit, Finset.image_union, hfix]
  unfold indexSetSum
  rw [Finset.sum_union hdisj]

end IndexedIntervals

end GrahamRearrangement
