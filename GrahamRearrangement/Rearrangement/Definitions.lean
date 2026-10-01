module

public import GrahamRearrangement.Combinatorial

@[expose] public section

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Section 5: exact definitions

The implementation uses `Fin n` for the paper's index set `{1,...,n}`.  The
translation is explicit: `paperPos i = i.val + 1`.
-/

noncomputable section

/-- Reversal of the finite paper index set: position a is sent to n+1-a. -/
def reverseIndex (n : ℕ) : Equiv.Perm (Fin n) where
  toFun i := ⟨n - 1 - i.val, by have := i.isLt; omega⟩
  invFun i := ⟨n - 1 - i.val, by have := i.isLt; omega⟩
  left_inv i := by apply Fin.ext; have := i.isLt; dsimp; omega
  right_inv i := by apply Fin.ext; have := i.isLt; dsimp; omega

@[simp] theorem reverseIndex_apply_val {n : ℕ} (i : Fin n) :
    (reverseIndex n i).val = n - 1 - i.val := rfl

@[simp] theorem reverseIndex_involutive {n : ℕ} (i : Fin n) :
    reverseIndex n (reverseIndex n i) = i := by
  apply Fin.ext
  have := i.isLt
  simp only [reverseIndex_apply_val]
  omega

def paperPos {n : ℕ} (i : Fin n) : ℕ := i.val + 1

theorem paperPos_pos {n : ℕ} (i : Fin n) : 1 ≤ paperPos i := by
  simp [paperPos]

theorem paperPos_le {n : ℕ} (i : Fin n) : paperPos i ≤ n := by
  have := i.isLt
  unfold paperPos
  omega

theorem paperPos_lt_iff {n : ℕ} {i j : Fin n} :
    paperPos i < paperPos j ↔ i.val < j.val := by
  simp [paperPos]

/-- An indexed ordering of S, corresponding to a bijection {1,...,|S|} -> S. -/
def IsIndexedOrdering {p : ℕ} (S : Finset (ZMod p))
    (σ : Fin S.card → ZMod p) : Prop :=
  Function.Injective σ ∧ ∀ x, x ∈ S ↔ ∃ i, σ i = x

def indexedToList {n p : ℕ} (σ : Fin n → ZMod p) : List (ZMod p) :=
  List.ofFn σ

/-- Paper interval sum Σ(σ,[a,b]), written in zero-based representatives. -/
def indexedIntervalSum {n p : ℕ} (σ : Fin n → ZMod p)
    (a b : Fin n) : ZMod p :=
  ∑ i ∈ Finset.Icc a.val b.val,
    if hi : i < n then σ ⟨i, hi⟩ else 0

def indexInterval {n : ℕ} (a b : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun i => a.val ≤ i.val ∧ i.val ≤ b.val

theorem card_indexInterval {n : ℕ} (a b : Fin n)
    (hab : a.val ≤ b.val) :
    (indexInterval a b).card = b.val - a.val + 1 := by
  have h : indexInterval a b = Finset.Icc a b := by
    ext i
    simp only [indexInterval, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Icc]
    rfl
  rw [h, Fin.card_Icc]
  omega

/-- Open-closed interval (a,b], used when splitting a right-extending
zero-sum interval at an exposed endpoint. -/
def indexOpenClosed {n : ℕ} (a b : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun i => a.val < i.val ∧ i.val ≤ b.val

theorem card_indexOpenClosed {n : ℕ} (a b : Fin n)
    :
    (indexOpenClosed a b).card = b.val - a.val := by
  have h : indexOpenClosed a b = Finset.Ioc a b := by
    ext i
    simp only [indexOpenClosed, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ioc]
    rfl
  rw [h, Fin.card_Ioc]

/-- Half-open index interval [a,b), used after exposing the value at b. -/
def indexHalfOpen {n : ℕ} (a b : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun i => a.val ≤ i.val ∧ i.val < b.val

theorem card_indexHalfOpen {n : ℕ} (a b : Fin n)
    :
    (indexHalfOpen a b).card = b.val - a.val := by
  have h : indexHalfOpen a b = Finset.Ico a b := by
    ext i
    simp only [indexHalfOpen, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ico]
    rfl
  rw [h, Fin.card_Ico]

/-- Sum of the image of an arbitrary finite index set. -/
def indexSetSum {n p : ℕ} (σ : Fin n → ZMod p)
    (J : Finset (Fin n)) : ZMod p :=
  ∑ i ∈ J, σ i

theorem indexSetSum_indexInterval {n p : ℕ}
    (σ : Fin n → ZMod p) (a b : Fin n) :
    indexSetSum σ (indexInterval a b) =
      indexedIntervalSum σ a b := by
  unfold indexSetSum indexInterval indexedIntervalSum
  refine Finset.sum_bij (fun i _ => i.val) ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact Finset.mem_Icc.2 hi
  · intro i₁ _ i₂ _ h
    exact Fin.ext h
  · intro j hj
    have hj' := Finset.mem_Icc.1 hj
    have hjn : j < n := lt_of_le_of_lt hj'.2 b.isLt
    refine ⟨⟨j, hjn⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hj'
  · intro i _
    simp [i.isLt]

/-- The forward paper interval {b,...,b+r}, clipped to {1,...,n}. -/
def forwardWindow {n : ℕ} (b : Fin n) (r : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i =>
    b.val ≤ i.val ∧ i.val ≤ b.val + r

theorem card_forwardWindow_eq {n : ℕ} (b : Fin n) (r : ℕ)
    (hfit : b.val + r < n) :
    (forwardWindow b r).card = r + 1 := by
  have h : forwardWindow b r = Finset.Icc b ⟨b.val + r, hfit⟩ := by
    ext i
    simp only [forwardWindow, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Icc]
    rfl
  rw [h, Fin.card_Icc]
  simp only
  omega

theorem card_forwardWindow_le {n : ℕ} (b : Fin n) (r : ℕ) :
    (forwardWindow b r).card ≤ r + 1 := by
  calc (forwardWindow b r).card ≤ (Finset.range (r + 1)).card := by
        apply Finset.card_le_card_of_injOn (fun i : Fin n => i.val - b.val)
        · intro i hi
          simp only [forwardWindow, Finset.coe_filter, Finset.mem_univ, true_and,
            Set.mem_ofPred_eq] at hi
          simp only [Finset.coe_range, Set.mem_Iio]
          omega
        · intro i hi j hj h
          simp only [forwardWindow, Finset.coe_filter, Finset.mem_univ, true_and,
            Set.mem_ofPred_eq] at hi hj
          apply Fin.ext
          simp only at h
          omega
    _ = r + 1 := Finset.card_range _

/-- Symmetric paper window {z-r,...,z+r}, clipped to {1,...,n}. -/
def symmetricWindow {n : ℕ} (z : Fin n) (r : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => Nat.dist i.val z.val ≤ r

theorem card_symmetricWindow_le {n : ℕ} (z : Fin n) (r : ℕ) :
    (symmetricWindow z r).card ≤ 2 * r + 1 := by
  calc (symmetricWindow z r).card ≤ (Finset.range (2 * r + 1)).card := by
        apply Finset.card_le_card_of_injOn (fun i : Fin n => i.val + r - z.val)
        · intro i hi
          simp only [symmetricWindow, Finset.coe_filter, Finset.mem_univ, true_and,
            Set.mem_ofPred_eq] at hi
          unfold Nat.dist at hi
          simp only [Finset.coe_range, Set.mem_Iio]
          omega
        · intro i hi j hj h
          simp only [symmetricWindow, Finset.coe_filter, Finset.mem_univ, true_and,
            Set.mem_ofPred_eq] at hi hj
          unfold Nat.dist at hi hj
          apply Fin.ext
          simp only at h
          omega
    _ = 2 * r + 1 := Finset.card_range _

def backwardWindow {n : ℕ} (x : Fin n) (r : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun q =>
    q.val ≤ x.val ∧ x.val < q.val + r

theorem card_backwardWindow_le {n : ℕ} (x : Fin n) (r : ℕ) :
    (backwardWindow x r).card ≤ r := by
  calc (backwardWindow x r).card ≤ (Finset.range r).card := by
        apply Finset.card_le_card_of_injOn (fun q : Fin n => x.val - q.val)
        · intro i hi
          simp only [backwardWindow, Finset.coe_filter, Finset.mem_univ, true_and,
            Set.mem_ofPred_eq] at hi
          simp only [Finset.coe_range, Set.mem_Iio]
          omega
        · intro i hi j hj h
          simp only [backwardWindow, Finset.coe_filter, Finset.mem_univ, true_and,
            Set.mem_ofPred_eq] at hi hj
          apply Fin.ext
          simp only at h
          omega
    _ = r := Finset.card_range _

def tailTuples {n : ℕ} (b' : Fin n) (D : ℕ) :
    Finset (Fin D → Fin n) :=
  Finset.univ.filter fun x =>
    StrictMono x ∧ ∀ i, paperPos b' < paperPos (x i)

def tailSizes {n D : ℕ} (b' : Fin n)
    (x : Fin D → Fin n) : Fin D → ℕ :=
  fun i => (x i).val - b'.val

def constraintSet {n D : ℕ}
    (u x : Fin D → Fin n)
    (πi : Fin D → Equiv.Perm (Fin n)) (i : Fin D) :
    Finset (Fin n) :=
  (indexInterval (u i) (x i)).image (πi i)

def interestingLeftSupport {n D : ℕ}
    (b : Fin n) (x : Fin D → Fin n) : Finset (Fin n) :=
  symmetricWindow b (5 * D) ∪
    Finset.univ.biUnion fun i => backwardWindow (x i) (5 * D)

def headTuples {n : ℕ} (b : Fin n) (D : ℕ) :
    Finset (Fin D → Fin n) :=
  Finset.univ.filter fun x =>
    StrictMono x ∧ ∀ i, paperPos (x i) < paperPos b

def headSizes {n D : ℕ} (b : Fin n)
    (x : Fin D → Fin n) : Fin D → ℕ :=
  fun i => b.val - (x ⟨D - 1 - i.val, by have := i.isLt; omega⟩).val

/-- B(σ): right endpoints of zero-sum intervals [a,b] with 2≤a<b≤n. -/
def badRightEndpoints {n p : ℕ}
    (σ : Fin n → ZMod p) : Finset (Fin n) :=
  Finset.univ.filter fun b =>
    ∃ a : Fin n,
      2 ≤ paperPos a ∧ paperPos a < paperPos b ∧
        indexedIntervalSum σ a b = 0

@[simp] theorem mem_badRightEndpoints_iff {n p : ℕ}
    (σ : Fin n → ZMod p) (b : Fin n) :
    b ∈ badRightEndpoints σ ↔
      ∃ a : Fin n,
        2 ≤ paperPos a ∧ paperPos a < paperPos b ∧
          indexedIntervalSum σ a b = 0 := by
  simp [badRightEndpoints]

theorem badRightEndpoint_ge_three {n p : ℕ}
    {σ : Fin n → ZMod p} {b : Fin n}
    (hb : b ∈ badRightEndpoints σ) :
    3 ≤ paperPos b := by
  rcases (mem_badRightEndpoints_iff σ b).1 hb with ⟨a, ha2, hab, _⟩
  omega

/-- Exact target condition used in Section 5: no zero-sum [a,b] with 2≤a<b. -/
def HasNoZeroPaperSegments {n p : ℕ} (σ : Fin n → ZMod p) : Prop :=
  ∀ a b : Fin n,
    2 ≤ paperPos a → paperPos a < paperPos b →
      indexedIntervalSum σ a b ≠ 0

/-- Conjugation of a position permutation by order reversal. -/
def reverseConjugate {n : ℕ} (π : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin n) :=
  (reverseIndex n).trans (π.trans (reverseIndex n))

@[simp] theorem reverseConjugate_apply {n : ℕ}
    (π : Equiv.Perm (Fin n)) (i : Fin n) :
    reverseConjugate π i =
      reverseIndex n (π (reverseIndex n i)) := rfl

theorem paperPos_reverseIndex {n : ℕ} (i : Fin n) :
    paperPos (reverseIndex n i) = n + 1 - paperPos i := by
  have := i.isLt
  simp only [paperPos, reverseIndex_apply_val]
  omega

/-- Apply a permutation of paper positions. Composition order agrees with σ∘π. -/
def applyPositionPerm {n p : ℕ} (σ : Fin n → ZMod p)
    (π : Equiv.Perm (Fin n)) : Fin n → ZMod p :=
  σ ∘ π

theorem indexSetSum_applyPositionPerm_image
    {n p : ℕ} (σ : Fin n → ZMod p)
    (π : Equiv.Perm (Fin n)) (J : Finset (Fin n)) :
    indexSetSum (applyPositionPerm σ π) J =
      indexSetSum σ (J.image π) := by
  unfold indexSetSum applyPositionPerm
  rw [Finset.sum_image]
  · rfl
  · intro i hi j hj hij
    exact π.injective hij

def swapPairsDisjoint {n : ℕ} (q r : Fin n × Fin n) : Prop :=
  q.1 ≠ r.1 ∧ q.1 ≠ r.2 ∧ q.2 ≠ r.1 ∧ q.2 ≠ r.2

/-- An admissible collection P of disjoint pairs (x,y), x<y, y-x≤5D. -/
def IsAdmissibleCollection {n : ℕ} (D : ℕ)
    (P : Finset (Fin n × Fin n)) : Prop :=
  (P : Set (Fin n × Fin n)).Pairwise swapPairsDisjoint ∧
    ∀ q ∈ P,
      paperPos q.1 < paperPos q.2 ∧
        paperPos q.2 - paperPos q.1 ≤ 5 * D

def swapsPermList {α : Type*} [DecidableEq α] :
    List (α × α) → Equiv.Perm α
  | [] => Equiv.refl _
  | q :: qs => (Equiv.swap q.1 q.2).trans (swapsPermList qs)

/-- Canonical composition of the disjoint swaps in P. -/
def collectionPerm {n : ℕ}
    (P : Finset (Fin n × Fin n)) : Equiv.Perm (Fin n) :=
  swapsPermList P.toList

def SwapCrosses {n : ℕ} (q : Fin n × Fin n)
    (I : Finset (Fin n)) : Prop :=
  (q.1 ∈ I ∧ q.2 ∉ I) ∨ (q.1 ∉ I ∧ q.2 ∈ I)

/-- Transpositions with disjoint supports commute. -/
theorem swap_trans_swap_comm_of_ne {α : Type*} [DecidableEq α] {a b c d : α}
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    (Equiv.swap a b).trans (Equiv.swap c d) =
      (Equiv.swap c d).trans (Equiv.swap a b) := by
  ext x
  simp only [Equiv.trans_apply, Equiv.swap_apply_def]
  split_ifs <;> simp_all

/-- `swapsPermList` as a product in the permutation group (recall that
`f * g = g.trans f`). -/
theorem swapsPermList_eq_prod {α : Type*} [DecidableEq α] (l : List (α × α)) :
    swapsPermList l = ((l.map fun q => Equiv.swap q.1 q.2).reverse).prod := by
  induction l with
  | nil => rfl
  | cons q qs ih =>
    rw [swapsPermList, ih, List.map_cons, List.reverse_cons, List.prod_append,
      List.prod_singleton]
    rfl

/-- Reordering a list of pairwise commuting transpositions does not change
their composition. -/
theorem swapsPermList_eq_of_perm {α : Type*} [DecidableEq α] {l r : List (α × α)}
    (hp : l.Perm r)
    (hcomm : ∀ q ∈ l, ∀ s ∈ l,
      Commute (Equiv.swap q.1 q.2) (Equiv.swap s.1 s.2)) :
    swapsPermList l = swapsPermList r := by
  rw [swapsPermList_eq_prod, swapsPermList_eq_prod]
  apply List.Perm.prod_eq'
  · exact (List.reverse_perm _).trans ((hp.map _).trans (List.reverse_perm _).symm)
  · rw [List.pairwise_reverse, List.pairwise_map]
    exact List.pairwise_of_forall_mem_list fun a ha b hb => (hcomm a ha b hb).symm

/-- A point outside all pairs is fixed by the composed transpositions. -/
theorem swapsPermList_apply_of_forall_ne {α : Type*} [DecidableEq α]
    (l : List (α × α)) (x : α)
    (hx : ∀ q ∈ l, x ≠ q.1 ∧ x ≠ q.2) : swapsPermList l x = x := by
  induction l with
  | nil => rfl
  | cons q qs ih =>
    have hq := hx q (List.mem_cons_self ..)
    rw [swapsPermList, Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne hq.1 hq.2]
    exact ih fun r hr => hx r (List.mem_cons_of_mem _ hr)

/-- For pairwise disjoint pairs, the composed transpositions exchange the two
entries of every pair. -/
theorem swapsPermList_apply_pair {α : Type*} [DecidableEq α]
    (l : List (α × α))
    (hl : l.Pairwise fun q r => q.1 ≠ r.1 ∧ q.1 ≠ r.2 ∧ q.2 ≠ r.1 ∧ q.2 ≠ r.2)
    {q : α × α} (hq : q ∈ l) :
    swapsPermList l q.1 = q.2 ∧ swapsPermList l q.2 = q.1 := by
  induction l with
  | nil => simp at hq
  | cons r rs ih =>
    rw [List.pairwise_cons] at hl
    simp only [swapsPermList, Equiv.trans_apply]
    rcases List.mem_cons.1 hq with rfl | hq'
    · rw [Equiv.swap_apply_left, Equiv.swap_apply_right]
      constructor
      · apply swapsPermList_apply_of_forall_ne
        intro s hs
        exact ⟨(hl.1 s hs).2.2.1, (hl.1 s hs).2.2.2⟩
      · apply swapsPermList_apply_of_forall_ne
        intro s hs
        exact ⟨(hl.1 s hs).1, (hl.1 s hs).2.1⟩
    · have hrq := hl.1 q hq'
      rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hrq.1) (Ne.symm hrq.2.2.1),
        Equiv.swap_apply_of_ne_of_ne (Ne.symm hrq.2.1) (Ne.symm hrq.2.2.2)]
      exact ih hl.2 hq'

theorem toList_pairwise_of_admissible {n D : ℕ} {P : Finset (Fin n × Fin n)}
    (hP : IsAdmissibleCollection D P) :
    P.toList.Pairwise fun q r => q.1 ≠ r.1 ∧ q.1 ≠ r.2 ∧ q.2 ≠ r.1 ∧ q.2 ≠ r.2 :=
  P.nodup_toList.pairwise_of_forall_ne fun _ ha _ hb hab =>
    hP.1 (Finset.mem_coe.2 (Finset.mem_toList.1 ha))
      (Finset.mem_coe.2 (Finset.mem_toList.1 hb)) hab

/-- `π_P` exchanges the two entries of every pair of an admissible `P`. -/
theorem collectionPerm_apply_pair {n D : ℕ} {P : Finset (Fin n × Fin n)}
    (hP : IsAdmissibleCollection D P) {q : Fin n × Fin n} (hq : q ∈ P) :
    collectionPerm P q.1 = q.2 ∧ collectionPerm P q.2 = q.1 :=
  swapsPermList_apply_pair P.toList (toList_pairwise_of_admissible hP)
    (Finset.mem_toList.2 hq)

/-- `π_P` fixes every position not appearing in a pair of `P`. -/
theorem collectionPerm_apply_of_forall_ne {n : ℕ} (P : Finset (Fin n × Fin n))
    (x : Fin n) (hx : ∀ q ∈ P, x ≠ q.1 ∧ x ≠ q.2) :
    collectionPerm P x = x :=
  swapsPermList_apply_of_forall_ne P.toList x fun q hq => hx q (Finset.mem_toList.1 hq)

/-- The transpositions in an admissible collection commute because their
supports are disjoint, exactly as stated in Section 5. -/
theorem admissible_transpositions_commute {n D : ℕ}
    {P : Finset (Fin n × Fin n)}
    (hP : IsAdmissibleCollection D P)
    {q r : Fin n × Fin n} (hq : q ∈ P) (hr : r ∈ P)
    (hqr : q ≠ r) :
    (Equiv.swap q.1 q.2).trans (Equiv.swap r.1 r.2) =
      (Equiv.swap r.1 r.2).trans (Equiv.swap q.1 q.2) := by
  have hd := hP.1 (Finset.mem_coe.2 hq) (Finset.mem_coe.2 hr) hqr
  exact swap_trans_swap_comm_of_ne hd.1 hd.2.1 hd.2.2.1 hd.2.2.2

/-- Consequently, `π_P` is independent of the enumeration of the admissible
collection `P`. -/
theorem collectionPerm_order_independent {n D : ℕ}
    {P : Finset (Fin n × Fin n)}
    (hP : IsAdmissibleCollection D P)
    (l : List (Fin n × Fin n))
    (hl : l.toFinset = P) (hln : l.Nodup) :
    swapsPermList l = collectionPerm P := by
  unfold collectionPerm
  apply swapsPermList_eq_of_perm
  · apply List.perm_of_nodup_nodup_toFinset_eq hln P.nodup_toList
    rw [hl, Finset.toList_toFinset]
  · intro q hq s hs
    have hqP : q ∈ P := by rw [← hl]; exact List.mem_toFinset.2 hq
    have hsP : s ∈ P := by rw [← hl]; exact List.mem_toFinset.2 hs
    by_cases hqs : q = s
    · subst hqs
      exact Commute.refl _
    · exact admissible_transpositions_commute hP hsP hqP (Ne.symm hqs)

theorem admissibleCollection_subset {n D : ℕ}
    {P Q : Finset (Fin n × Fin n)}
    (hP : IsAdmissibleCollection D P)
    (hQ : IsAdmissibleCollection D Q)
    (hperm : collectionPerm P = collectionPerm Q) :
    P ⊆ Q := by
  intro q hq
  have hqlt := (hP.2 q hq).1
  have hq1 : collectionPerm Q q.1 = q.2 := by
    rw [← hperm]; exact (collectionPerm_apply_pair hP hq).1
  by_contra hqQ
  have hmoved : ∃ r ∈ Q, q.1 = r.1 ∨ q.1 = r.2 := by
    by_contra hnone
    push Not at hnone
    have := collectionPerm_apply_of_forall_ne Q q.1 hnone
    rw [hq1] at this
    unfold paperPos at hqlt
    have := congrArg Fin.val this
    omega
  obtain ⟨r, hr, h1 | h2⟩ := hmoved
  · have hr1 := (collectionPerm_apply_pair hQ hr).1
    rw [← h1, hq1] at hr1
    exact hqQ (by rwa [show q = r from Prod.ext h1 hr1])
  · have hr2 := (collectionPerm_apply_pair hQ hr).2
    rw [← h2, hq1] at hr2
    have hrlt := (hQ.2 r hr).1
    unfold paperPos at hqlt hrlt
    rw [← h2, ← hr2] at hrlt
    omega

/-- The paper's observation that an admissible collection can be uniquely
reconstructed from its permutation. -/
theorem admissibleCollection_reconstruct {n D : ℕ}
    {P Q : Finset (Fin n × Fin n)}
    (hP : IsAdmissibleCollection D P)
    (hQ : IsAdmissibleCollection D Q)
    (hperm : collectionPerm P = collectionPerm Q) :
    P = Q :=
  Finset.Subset.antisymm (admissibleCollection_subset hP hQ hperm)
    (admissibleCollection_subset hQ hP hperm.symm)

def supportedAdmissibleCollections {n : ℕ}
    (D : ℕ) (Q : Finset (Fin n)) :
    Finset (Finset (Fin n × Fin n)) := by
  classical
  exact Finset.univ.filter fun P =>
    IsAdmissibleCollection D P ∧
      ∀ q ∈ P, q.1 ∈ Q

def IsAdmissiblePermutation {n : ℕ} (D : ℕ)
    (π : Equiv.Perm (Fin n)) : Prop :=
  ∃ P : Finset (Fin n × Fin n),
    IsAdmissibleCollection D P ∧ collectionPerm P = π

def Lemma55Event {n p D : ℕ}
    (σ : Fin n → ZMod p)
    (b' : Fin n)
    (u : Fin D → Fin n)
    (πi : Fin D → Equiv.Perm (Fin n)) : Prop :=
  ∃ x ∈ tailTuples b' D,
    ∃ π : Equiv.Perm (Fin n),
      IsAdmissiblePermutation D π ∧
      ∀ i,
        indexedIntervalSum
          (applyPositionPerm
            (applyPositionPerm σ π) (πi i))
          (u i) (x i) = 0

def Lemma56Event {n p D : ℕ}
    (σ : Fin n → ZMod p)
    (b : Fin n)
    (u : Fin D → Fin n)
    (πi : Fin D → Equiv.Perm (Fin n)) : Prop :=
  ∃ x ∈ headTuples b D,
    ∃ π : Equiv.Perm (Fin n),
      IsAdmissiblePermutation D π ∧
      ∀ i,
        indexedIntervalSum
          (applyPositionPerm
            (applyPositionPerm σ π) (πi i))
          (x i) (u i) = 0

def IsInterestingPermutation {n k : ℕ} (D : ℕ)
    (I : Fin k → Finset (Fin n))
    (π : Equiv.Perm (Fin n)) : Prop :=
  ∃ P : Finset (Fin n × Fin n),
    IsAdmissibleCollection D P ∧
    collectionPerm P = π ∧
    ∀ q ∈ P, ∃ i, SwapCrosses q (I i)

def interestingPermutations {n k : ℕ} (D : ℕ)
    (I : Fin k → Finset (Fin n)) :
    Finset (Equiv.Perm (Fin n)) := by
  classical
  exact Finset.univ.filter (IsInterestingPermutation D I)

def FixedBelow {n : ℕ} (b : Fin n)
    (π : Equiv.Perm (Fin n)) : Prop :=
  ∀ i : Fin n, paperPos i < paperPos b → π i = i

def FixedOutside {n : ℕ} (b b' : Fin n)
    (π : Equiv.Perm (Fin n)) : Prop :=
  ∀ i : Fin n,
    (paperPos i < paperPos b ∨ paperPos b' < paperPos i) → π i = i

def FixedThrough {n : ℕ} (b : Fin n)
    (π : Equiv.Perm (Fin n)) : Prop :=
  ∀ i : Fin n, paperPos i ≤ paperPos b → π i = i

/-- The paper's definition of y blocked for σ,b,π. -/
def IsBlockedAt {n p : ℕ} (D : ℕ) (σ : Fin n → ZMod p)
    (b : Fin n) (π : Equiv.Perm (Fin n)) (y : Fin n) : Prop :=
  paperPos b < paperPos y ∧
  paperPos y ≤ paperPos b + 5 * D ∧
  ∃ s t : Fin n,
    2 ≤ paperPos s ∧ paperPos s < paperPos t ∧
    indexedIntervalSum
      (applyPositionPerm (applyPositionPerm σ π) (Equiv.swap b y)) s t = 0 ∧
    ((paperPos b < paperPos s ∧ paperPos s ≤ paperPos y) ∨
      (paperPos b ≤ paperPos t ∧ paperPos t < paperPos y))

def blockedCandidates {n p : ℕ} (D : ℕ)
    (σ : Fin n → ZMod p) (b : Fin n)
    (π : Equiv.Perm (Fin n)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun y => IsBlockedAt D σ b π y

/-- Image of an index set under an ordering. -/
def indexImageSet {n p : ℕ} (σ : Fin n → ZMod p)
    (I : Finset (Fin n)) : Finset (ZMod p) :=
  I.image σ

theorem indexSetSum_eq_subsetSum_image {n p : ℕ}
    {σ : Fin n → ZMod p} (hσ : Function.Injective σ)
    (I : Finset (Fin n)) :
    indexSetSum σ I = subsetSum (indexImageSet σ I) := by
  unfold indexSetSum subsetSum indexImageSet
  rw [Finset.sum_image]
  intro i hi j hj hij
  exact hσ hij

/-- Agreement of two indexed orderings on an exposed set of positions. -/
def AgreesOn {n p : ℕ} (F : Finset (Fin n))
    (σ τ : Fin n → ZMod p) : Prop :=
  ∀ i ∈ F, σ i = τ i

instance {n p : ℕ} (F : Finset (Fin n)) (σ τ : Fin n → ZMod p) :
    Decidable (AgreesOn F σ τ) := by
  unfold AgreesOn
  infer_instance

structure RepairParams (n D : ℕ) where
  b : Fin n
  b' : Fin n
  y : Fin D → Fin n
  u : Fin D → Fin n
deriving DecidableEq, Fintype

def strictForwardWindow {n : ℕ} (b : Fin n) (r : ℕ) :
    Finset (Fin n) :=
  (forwardWindow b r).erase b

theorem mem_strictForwardWindow {n r : ℕ} {b x : Fin n} :
    x ∈ strictForwardWindow b r ↔
      paperPos b < paperPos x ∧
        paperPos x ≤ paperPos b + r := by
  simp [strictForwardWindow,forwardWindow,paperPos]
  omega

theorem card_strictForwardWindow_le {n : ℕ}
    (b : Fin n) (r : ℕ) :
    (strictForwardWindow b r).card ≤ r := by
  have hb : b ∈ forwardWindow b r := by
    simp [forwardWindow]
  unfold strictForwardWindow
  rw [Finset.card_erase_of_mem hb]
  have hw := card_forwardWindow_le b r
  omega

def canonicalLocalEnd {n : ℕ} (b : Fin n) (D : ℕ)
    (hfit : paperPos b + 5 * D ≤ n) : Fin n :=
  ⟨b.val + 5 * D, by
    simp [paperPos] at hfit
    omega⟩

theorem canonicalLocalEnd_gap {n D : ℕ} (b : Fin n)
    (hfit : paperPos b + 5 * D ≤ n) :
    paperPos (canonicalLocalEnd b D hfit) - paperPos b = 5 * D := by
  simp [canonicalLocalEnd,paperPos]

/-- The finite set of parameter records `(b,b',y,u)` over which the union bound
for `RightRepairEvent` is taken: exactly the records satisfying the side
conditions of `RightRepairEvent`.  (When `D > 0`, `b'` is determined by `b`,
namely `b' = b + 5D`.) -/
def rightRepairParameters (n D : ℕ) :
    Finset (RepairParams n D) := by
  classical
  exact Finset.univ.filter fun θ =>
    2 ≤ paperPos θ.b ∧
    paperPos θ.b + 30 * D ≤ n ∧
    paperPos θ.b' - paperPos θ.b = 5 * D ∧
    (∀ i,
      paperPos θ.b < paperPos (θ.y i) ∧
        paperPos (θ.y i) ≤ paperPos θ.b') ∧
    (∀ i,
      paperPos θ.b < paperPos (θ.u i) ∧
        paperPos (θ.u i) ≤ paperPos θ.b')

/-- The finite set of parameter records for the union bound for
`LeftRepairEvent`: exactly the records satisfying its side conditions. -/
def leftRepairParameters (n D : ℕ) :
    Finset (RepairParams n D) := by
  classical
  exact Finset.univ.filter fun θ =>
    2 ≤ paperPos θ.b ∧
    paperPos θ.b + 30 * D ≤ n ∧
    paperPos θ.b' - paperPos θ.b = 5 * D ∧
    (∀ i,
      paperPos θ.b < paperPos (θ.y i) ∧
        paperPos (θ.y i) ≤ paperPos θ.b') ∧
    (∀ i,
      paperPos θ.b ≤ paperPos (θ.u i) ∧
        paperPos (θ.u i) < paperPos θ.b')

theorem mem_rightRepairParameters {n D : ℕ}
    {θ : RepairParams n D} :
    θ ∈ rightRepairParameters n D ↔
      2 ≤ paperPos θ.b ∧
      paperPos θ.b + 30 * D ≤ n ∧
      paperPos θ.b' - paperPos θ.b = 5 * D ∧
      (∀ i,
        paperPos θ.b < paperPos (θ.y i) ∧
          paperPos (θ.y i) ≤ paperPos θ.b') ∧
      (∀ i,
        paperPos θ.b < paperPos (θ.u i) ∧
          paperPos (θ.u i) ≤ paperPos θ.b') := by
  unfold rightRepairParameters
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ θ)

theorem mem_leftRepairParameters {n D : ℕ}
    {θ : RepairParams n D} :
    θ ∈ leftRepairParameters n D ↔
      2 ≤ paperPos θ.b ∧
      paperPos θ.b + 30 * D ≤ n ∧
      paperPos θ.b' - paperPos θ.b = 5 * D ∧
      (∀ i,
        paperPos θ.b < paperPos (θ.y i) ∧
          paperPos (θ.y i) ≤ paperPos θ.b') ∧
      (∀ i,
        paperPos θ.b ≤ paperPos (θ.u i) ∧
          paperPos (θ.u i) < paperPos θ.b') := by
  unfold leftRepairParameters
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ θ)

/-- Counting principle for repair parameters: if `b'` is determined by `b` and
the coordinates of `y` and `u` range over windows of size at most `5D`
depending only on `b`, there are at most `n (5D)^(2D)` records. -/
theorem card_repairParams_le_of_windows {n D : ℕ}
    (T : Finset (RepairParams n D))
    (W₁ W₂ : Fin n → Finset (Fin n))
    (hW₁ : ∀ b, (W₁ b).card ≤ 5 * D) (hW₂ : ∀ b, (W₂ b).card ≤ 5 * D)
    (hy : ∀ θ ∈ T, ∀ i, θ.y i ∈ W₁ θ.b)
    (hu : ∀ θ ∈ T, ∀ i, θ.u i ∈ W₂ θ.b)
    (hb' : ∀ θ ∈ T, ∀ θ' ∈ T, θ.b = θ'.b → θ.b' = θ'.b') :
    T.card ≤ n * (5 * D) ^ (2 * D) := by
  classical
  let F : Finset (Fin n × (Fin D → Fin n) × (Fin D → Fin n)) :=
    Finset.univ.biUnion fun b =>
      (Fintype.piFinset (fun _ : Fin D => W₁ b) ×ˢ
        Fintype.piFinset (fun _ : Fin D => W₂ b)).image fun yu => (b, yu)
  calc T.card ≤ F.card := by
        apply Finset.card_le_card_of_injOn (fun θ => (θ.b, θ.y, θ.u))
        · intro θ hθ
          rw [Finset.mem_coe] at hθ
          rw [Finset.mem_coe]
          exact Finset.mem_biUnion.2 ⟨θ.b, Finset.mem_univ _,
            Finset.mem_image.2 ⟨(θ.y, θ.u), Finset.mem_product.2
              ⟨Fintype.mem_piFinset.2 (hy θ hθ), Fintype.mem_piFinset.2 (hu θ hθ)⟩, rfl⟩⟩
        · intro θ hθ θ' hθ' h
          simp only [Prod.mk.injEq] at h
          obtain ⟨h1, h2, h3⟩ := h
          have h4 := hb' θ hθ θ' hθ' h1
          cases θ
          cases θ'
          simp_all
    _ ≤ ∑ _b : Fin n, (5 * D) ^ (2 * D) := by
        refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun b _ => ?_)
        refine Finset.card_image_le.trans ?_
        rw [Finset.card_product, Fintype.card_piFinset, Fintype.card_piFinset,
          Finset.prod_const, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          two_mul, pow_add]
        exact Nat.mul_le_mul (Nat.pow_le_pow_left (hW₁ b) D)
          (Nat.pow_le_pow_left (hW₂ b) D)
    _ = n * (5 * D) ^ (2 * D) := by simp

/-- For `D > 0`, the gap condition `b' - b = 5D` determines `b'` from `b`. -/
theorem repairGap_determines_end {n D : ℕ} (hD : 0 < D) {b c c' : Fin n}
    (hc : paperPos c - paperPos b = 5 * D)
    (hc' : paperPos c' - paperPos b = 5 * D) :
    c = c' := by
  unfold paperPos at hc hc'
  apply Fin.ext
  omega

/-- The hypothesis `0 < D` is needed: for `D = 0` the gap condition
`paperPos b' - paperPos b = 0` does not determine `b'`, and e.g. for `n = 3`
there are `5 > 3 = n * (5D)^(2D)` records. -/
theorem rightRepairParameters_card_le (n D : ℕ) (hD : 0 < D) :
    (rightRepairParameters n D).card ≤
      n * (5 * D) ^ (2 * D) := by
  apply card_repairParams_le_of_windows _ (fun b => strictForwardWindow b (5 * D))
    (fun b => strictForwardWindow b (5 * D))
    (fun b => card_strictForwardWindow_le b _) (fun b => card_strictForwardWindow_le b _)
  · intro θ hθ i
    obtain ⟨-, -, hgap, hy, -⟩ := mem_rightRepairParameters.1 hθ
    refine mem_strictForwardWindow.2 ⟨(hy i).1, ?_⟩
    have := (hy i).2
    omega
  · intro θ hθ i
    obtain ⟨-, -, hgap, -, hu⟩ := mem_rightRepairParameters.1 hθ
    refine mem_strictForwardWindow.2 ⟨(hu i).1, ?_⟩
    have := (hu i).2
    omega
  · intro θ hθ θ' hθ' hb
    obtain ⟨-, -, hgap, -, -⟩ := mem_rightRepairParameters.1 hθ
    obtain ⟨-, -, hgap', -, -⟩ := mem_rightRepairParameters.1 hθ'
    rw [hb] at hgap
    exact repairGap_determines_end hD hgap hgap'

/-- As for `rightRepairParameters_card_le`, the hypothesis `0 < D` is needed. -/
theorem leftRepairParameters_card_le (n D : ℕ) (hD : 0 < D) :
    (leftRepairParameters n D).card ≤
      n * (5 * D) ^ (2 * D) := by
  classical
  have hW : ∀ b : Fin n,
      (Finset.univ.filter fun x : Fin n =>
        b.val ≤ x.val ∧ x.val < b.val + 5 * D).card ≤ 5 * D := by
    intro b
    calc _ ≤ (Finset.range (5 * D)).card := by
          apply Finset.card_le_card_of_injOn (fun x : Fin n => x.val - b.val)
          · intro x hx
            simp only [Finset.coe_filter, Finset.mem_univ, true_and,
              Set.mem_ofPred_eq] at hx
            simp only [Finset.coe_range, Set.mem_Iio]
            omega
          · intro x hx x' hx' h
            simp only [Finset.coe_filter, Finset.mem_univ, true_and,
              Set.mem_ofPred_eq] at hx hx'
            apply Fin.ext
            simp only at h
            omega
      _ = 5 * D := Finset.card_range _
  apply card_repairParams_le_of_windows _ (fun b => strictForwardWindow b (5 * D))
    (fun b => Finset.univ.filter fun x : Fin n => b.val ≤ x.val ∧ x.val < b.val + 5 * D)
    (fun b => card_strictForwardWindow_le b _) hW
  · intro θ hθ i
    obtain ⟨-, -, hgap, hy, -⟩ := mem_leftRepairParameters.1 hθ
    refine mem_strictForwardWindow.2 ⟨(hy i).1, ?_⟩
    have := (hy i).2
    omega
  · intro θ hθ i
    obtain ⟨-, -, hgap, -, hu⟩ := mem_leftRepairParameters.1 hθ
    have h1 := (hu i).1
    have h2 := (hu i).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    unfold paperPos at h1 h2 hgap
    omega
  · intro θ hθ θ' hθ' hb
    obtain ⟨-, -, hgap, -, -⟩ := mem_leftRepairParameters.1 hθ
    obtain ⟨-, -, hgap', -, -⟩ := mem_leftRepairParameters.1 hθ'
    rw [hb] at hgap
    exact repairGap_determines_end hD hgap hgap'

/-- Right-extending witness event used in the proof of Lemma 5.3. -/
def RightRepairEvent {n p : ℕ} (D : ℕ)
    (σ : Fin n → ZMod p) : Prop :=
  ∃ b b' : Fin n,
    2 ≤ paperPos b ∧
    paperPos b + 30 * D ≤ n ∧
    paperPos b' - paperPos b = 5 * D ∧
    ∃ y u : Fin D → Fin n,
      (∀ i,
        paperPos b < paperPos (y i) ∧
          paperPos (y i) ≤ paperPos b') ∧
      (∀ i,
        paperPos b < paperPos (u i) ∧
          paperPos (u i) ≤ paperPos b') ∧
      Lemma55Event σ b' u
        (fun i => Equiv.swap b (y i))

/-- Left-extending witness event used in the proof of Lemma 5.3. -/
def LeftRepairEvent {n p : ℕ} (D : ℕ)
    (σ : Fin n → ZMod p) : Prop :=
  ∃ b b' : Fin n,
    2 ≤ paperPos b ∧
    paperPos b + 30 * D ≤ n ∧
    paperPos b' - paperPos b = 5 * D ∧
    ∃ y u : Fin D → Fin n,
      (∀ i,
        paperPos b < paperPos (y i) ∧
          paperPos (y i) ≤ paperPos b') ∧
      (∀ i,
        paperPos b ≤ paperPos (u i) ∧
          paperPos (u i) < paperPos b') ∧
      Lemma56Event σ b u
        (fun i => Equiv.swap b (y i))

/-- Bad event B₁, exactly as in Lemma 5.1. -/
def BadEvent1 {n p : ℕ} (D : ℕ) (σ : Fin n → ZMod p) : Prop :=
  ∃ b ∈ badRightEndpoints σ,
    n ≤ paperPos b + 30 * D

/-- Bad event B₂, exactly as in Lemma 5.2. -/
def BadEvent2 {n p : ℕ} (D : ℕ) (σ : Fin n → ZMod p) : Prop :=
  ∃ z : Fin n,
    D < ((badRightEndpoints σ) ∩ symmetricWindow z (10 * D)).card

/-- Bad event B₃, exactly as in Lemma 5.3. -/
def BadEvent3 {n p : ℕ} (D : ℕ) (σ : Fin n → ZMod p) : Prop :=
  ∃ b ∈ badRightEndpoints σ,
    ∃ π : Equiv.Perm (Fin n),
      IsAdmissiblePermutation D π ∧
      FixedBelow b π ∧
      2 * D ≤ (blockedCandidates D σ b π).card

/-- Auxiliary bad event B₀ from Lemma 5.4. -/
def BadEvent0 {n p : ℕ} (D : ℕ) (σ : Fin n → ZMod p) : Prop :=
  ∃ b ∈ badRightEndpoints σ,
    paperPos b + 30 * D ≤ n ∧
    ∃ J J' : Finset (Fin n),
      J ⊆ forwardWindow b (20 * D) ∧
      J' ⊆ forwardWindow b (20 * D) ∧
      J ≠ J' ∧
      indexSetSum σ J = indexSetSum σ J'

def Section5Good {n p : ℕ} (D : ℕ) (σ : Fin n → ZMod p) : Prop :=
  ¬ BadEvent1 D σ ∧ ¬ BadEvent2 D σ ∧ ¬ BadEvent3 D σ

/-! The bad events are decided classically, so that each has a single
`DecidablePred` instance. -/

noncomputable instance {n p D : ℕ} : DecidablePred (BadEvent0 (n := n) (p := p) D) :=
  Classical.decPred _

noncomputable instance {n p D : ℕ} : DecidablePred (BadEvent1 (n := n) (p := p) D) :=
  Classical.decPred _

noncomputable instance {n p D : ℕ} : DecidablePred (BadEvent2 (n := n) (p := p) D) :=
  Classical.decPred _

noncomputable instance {n p D : ℕ} : DecidablePred (BadEvent3 (n := n) (p := p) D) :=
  Classical.decPred _

noncomputable instance {n p D : ℕ} : DecidablePred (Section5Good (n := n) (p := p) D) :=
  Classical.decPred _

noncomputable instance {n p D : ℕ} : DecidablePred (RightRepairEvent (n := n) (p := p) D) :=
  Classical.decPred _

noncomputable instance {n p D : ℕ} : DecidablePred (LeftRepairEvent (n := n) (p := p) D) :=
  Classical.decPred _

noncomputable instance {n p D : ℕ} (b' : Fin n) (u : Fin D → Fin n)
    (πi : Fin D → Equiv.Perm (Fin n)) :
    DecidablePred fun σ : Fin n → ZMod p => Lemma55Event σ b' u πi :=
  Classical.decPred _

noncomputable instance {n p D : ℕ} (b : Fin n) (u : Fin D → Fin n)
    (πi : Fin D → Equiv.Perm (Fin n)) :
    DecidablePred fun σ : Fin n → ZMod p => Lemma56Event σ b u πi :=
  Classical.decPred _

/-- All indexed orderings of S: the finite sample space for the random bijection σ. -/
def indexedOrderings {p : ℕ} [NeZero p] (S : Finset (ZMod p)) :
    Finset (Fin S.card → ZMod p) := by
  classical
  exact Finset.univ.filter fun σ => IsIndexedOrdering S σ

def orderingEventMass {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (E : (Fin S.card → ZMod p) → Prop) [DecidablePred E] : ℝ :=
  uniformMass (indexedOrderings S) E

def orderingConditionalMass {p : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    (cond event : (Fin S.card → ZMod p) → Prop)
    [DecidablePred cond] [DecidablePred event] : ℝ :=
  uniformConditionalMass (indexedOrderings S) cond event

/-- List interval sum, retained only for translating back to the introduction. -/
def listIntervalSum {G : Type*} [AddCommMonoid G]
    (xs : List G) (a b : ℕ) : G :=
  ((xs.drop a).take (b + 1 - a)).sum

theorem indexedToList_isOrdering {p : ℕ} {S : Finset (ZMod p)}
    {σ : Fin S.card → ZMod p} (hσ : IsIndexedOrdering S σ) :
    IsOrdering S (indexedToList σ) := by
  refine ⟨List.nodup_ofFn.2 hσ.1, ?_⟩
  ext x
  rw [List.mem_toFinset, indexedToList, List.mem_ofFn, hσ.2]

/-- Prefix sums of `indexedToList σ` as sums over initial ranges of naturals. -/
theorem sum_take_indexedToList {n p : ℕ} (σ : Fin n → ZMod p) (k : ℕ)
    (hk : k ≤ n) :
    ((indexedToList σ).take k).sum =
      ∑ i ∈ Finset.range k, if hi : i < n then σ ⟨i, hi⟩ else 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk' : k < n := by omega
    rw [List.sum_take_succ _ k (by simp [indexedToList]; omega), ih (by omega),
      Finset.sum_range_succ]
    simp [indexedToList, hk']

/-- The exact bridge between paper intervals and list intervals. -/
theorem indexedIntervalSum_eq_listIntervalSum {n p : ℕ}
    (σ : Fin n → ZMod p) (a b : Fin n) (hab : a.val ≤ b.val) :
    indexedIntervalSum σ a b =
      listIntervalSum (indexedToList σ) a.val b.val := by
  have htake : (indexedToList σ).take (b.val + 1) =
      (indexedToList σ).take a.val ++
        ((indexedToList σ).drop a.val).take (b.val + 1 - a.val) := by
    rw [← List.take_add]
    congr 1
    omega
  have hsum := congrArg List.sum htake
  rw [List.sum_append, sum_take_indexedToList σ _ (by omega),
    sum_take_indexedToList σ _ (by omega)] at hsum
  unfold indexedIntervalSum listIntervalSum
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sub _ (by omega), hsum]
  abel

end

end GrahamRearrangement
