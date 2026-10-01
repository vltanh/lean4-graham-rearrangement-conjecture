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
  sorry

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
  sorry

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
  · simpa [indexedToList] using b.isLt

theorem indexed_interval_zero_iff_prefix_eq {n p : ℕ}
    (σ : Fin n → ZMod p) (a b : Fin n)
    (hab : a.val ≤ b.val) :
    indexedIntervalSum σ a b = 0 ↔
      listPrefixSum (indexedToList σ) a.val =
        listPrefixSum (indexedToList σ) (b.val + 1) := by
  sorry

theorem interval_sum_eq_halfOpen_add_endpoint {n p : ℕ}
    (σ : Fin n → ZMod p) (a b : Fin n)
    (hab : a.val ≤ b.val) :
    indexedIntervalSum σ a b =
      indexSetSum σ (indexHalfOpen a b) + σ b := by
  sorry

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
  sorry

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
  sorry

theorem swap_interval_split_left {n p : ℕ}
    (τ : Fin n → ZMod p) (b y s t : Fin n)
    (hby : paperPos b < paperPos y)
    (hsb : paperPos s < paperPos b)
    (hbt : paperPos b ≤ paperPos t)
    (hty : paperPos t < paperPos y) :
    indexedIntervalSum (applyPositionPerm τ (Equiv.swap b y)) s t =
      indexSetSum τ (indexHalfOpen s b) +
        indexSetSum τ ((indexInterval b t).image (Equiv.swap b y)) := by
  sorry

end IndexedIntervals

end GrahamRearrangement
