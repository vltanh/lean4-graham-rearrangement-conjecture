module

public import GrahamRearrangement.BooleanSlice

@[expose] public section

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Section 4: definitions

Finite sample spaces and expressions used in the combinatorial anticoncentration
deductions.
-/

noncomputable section

/-- All nested chains R₁ ⊆ ⋯ ⊆ Rₖ ⊆ S with prescribed cardinalities |Rᵢ| = mᵢ, as in
Corollary 4.2. When the sizes are strictly increasing, the inclusions are automatically
strict. -/
def chainFamily {p k : ℕ} [NeZero p] (S : Finset (ZMod p))
    (m : Fin k → ℕ) : Finset (Fin k → Finset (ZMod p)) := by
  classical
  exact Finset.univ.filter fun R =>
    (∀ i, R i ⊆ S ∧ (R i).card = m i) ∧
      ∀ i j, i ≤ j → R i ⊆ R j

/-- Uniform probability mass of prescribed sums on a nested-chain sample space. -/
def chainMass {p k : ℕ} [NeZero p] (S : Finset (ZMod p))
    (m : Fin k → ℕ) (z : Fin k → ZMod p) : ℝ :=
  uniformMass (chainFamily S m)
    (fun R => ∀ i, subsetSum (R i) = z i)

/-- Extend m₁,...,mₖ by m₀=0 and mₖ₊₁=n. -/
def extendedSize {k : ℕ} (n : ℕ) (m : Fin k → ℕ) (i : ℕ) : ℕ :=
  if h0 : i = 0 then 0
  else if hi : i ≤ k then m ⟨i - 1, by omega⟩
  else n

/-- Consecutive gap mᵢ₊₁-mᵢ. -/
def chainGap {k : ℕ} (n : ℕ) (m : Fin k → ℕ)
    (i : Fin (k + 1)) : ℕ :=
  extendedSize n m (i.val + 1) - extendedSize n m i.val

/-- One Corollary 4.2 factor. -/
def chainFactor (p n : ℕ) (C : ℝ) (gap : ℕ) : ℝ :=
  1 / (p : ℝ) +
    C * Real.sqrt (Real.log (n : ℝ)) /
      ((n : ℝ) * Real.sqrt (gap : ℝ))

/-- Right-hand side of Corollary 4.2. -/
def chainUpperBound {k : ℕ} (p n : ℕ) (C : ℝ)
    (m : Fin k → ℕ) : ℝ :=
  ∑ j : Fin (k + 1),
    ∏ i ∈ (Finset.univ.erase j),
      chainFactor p n C (chainGap n m i)

/-- Exact hypotheses on the size tuple in Corollary 4.2. -/
def IsChainSizeTuple {k : ℕ} (n : ℕ) (m : Fin k → ℕ) : Prop :=
  StrictMono m ∧ ∀ i, 1 ≤ m i ∧ m i < n

/-- Finite family over which Lemma 4.3 sums. -/
def chainSizeTuples (n k : ℕ) : Finset (Fin k → ℕ) := by
  classical
  exact (Fintype.piFinset fun _ => Finset.range n).filter (IsChainSizeTuple n)

/-- Generic weighted sum over increasing h-tuples, using only the first h
gaps (from 0 to m₁, ..., m_{h-1} to m_h). -/
def prefixKernelSum (n h : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ m ∈ chainSizeTuples n h,
    ∏ i : Fin h,
      w (chainGap n m ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)

/-- Generic sum with one of the k+1 consecutive gaps omitted. -/
def omittedKernelSum (n k : ℕ) (w : ℕ → ℝ)
    (j : Fin (k + 1)) : ℝ :=
  ∑ m ∈ chainSizeTuples n k,
    ∏ i ∈ Finset.univ.erase j, w (chainGap n m i)

def leftPrefixTuple {k : ℕ}
    (m : Fin k → ℕ) (j : Fin (k + 1)) :
    Fin j.val → ℕ :=
  fun i => m ⟨i.val, lt_of_lt_of_le i.isLt (Nat.le_of_lt_succ j.isLt)⟩

def reverseRightTuple {k : ℕ} (n : ℕ)
    (m : Fin k → ℕ) (j : Fin (k + 1)) :
    Fin (k - j.val) → ℕ :=
  fun i =>
    n - m ⟨k - 1 - i.val, by
      have hij : i.val < k - j.val := i.isLt
      omega⟩


private theorem mem_chainSizeTuples_iff {n k : ℕ} {m : Fin k → ℕ} :
    m ∈ chainSizeTuples n k ↔ IsChainSizeTuple n m := by
  classical
  unfold chainSizeTuples
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨fun i => Finset.mem_range.mpr (h.2 i).2, h⟩

theorem leftPrefixTuple_mem {n k : ℕ}
    {m : Fin k → ℕ} (hm : m ∈ chainSizeTuples n k)
    (j : Fin (k + 1)) :
    leftPrefixTuple m j ∈ chainSizeTuples n j.val := by
  rw [mem_chainSizeTuples_iff] at hm ⊢
  obtain ⟨hmono, hbounds⟩ := hm
  refine ⟨?_, fun i => hbounds _⟩
  intro a b hab
  exact hmono (show (⟨a.val, _⟩ : Fin k) < ⟨b.val, _⟩ from hab)

theorem reverseRightTuple_mem {n k : ℕ}
    {m : Fin k → ℕ} (hm : m ∈ chainSizeTuples n k)
    (j : Fin (k + 1)) :
    reverseRightTuple n m j ∈
      chainSizeTuples n (k - j.val) := by
  rw [mem_chainSizeTuples_iff] at hm ⊢
  obtain ⟨hmono, hbounds⟩ := hm
  refine ⟨?_, ?_⟩
  · intro a b hab
    have ha := a.isLt
    have hb := b.isLt
    have hab' : a.val < b.val := hab
    have hlt := hmono (show (⟨k - 1 - b.val, by omega⟩ : Fin k) <
      ⟨k - 1 - a.val, by omega⟩ from by
        show k - 1 - b.val < k - 1 - a.val
        omega)
    have h1 := hbounds ⟨k - 1 - a.val, by omega⟩
    simp only [reverseRightTuple]
    omega
  · intro i
    have hi := i.isLt
    have h1 := hbounds ⟨k - 1 - i.val, by omega⟩
    simp only [reverseRightTuple]
    omega

/-- The pair (left prefix, reversed right part) determines a chain size tuple.
(The membership hypotheses are needed: `n - ·` is not injective on values `≥ n`.) -/
theorem fullTuple_eq_of_left_reverseRight_eq {n k : ℕ}
    (m m' : Fin k → ℕ) (j : Fin (k + 1))
    (hm : m ∈ chainSizeTuples n k) (hm' : m' ∈ chainSizeTuples n k)
    (h :
      (leftPrefixTuple m j, reverseRightTuple n m j) =
        (leftPrefixTuple m' j, reverseRightTuple n m' j)) :
    m = m' := by
  rw [mem_chainSizeTuples_iff] at hm hm'
  funext i
  have hleft := congrArg Prod.fst h
  have hright := congrArg Prod.snd h
  by_cases hi : i.val < j.val
  · exact congrFun hleft ⟨i.val, hi⟩
  · have hik := i.isLt
    have hj := j.isLt
    have hir : k - 1 - i.val < k - j.val := by omega
    have hr := congrFun hright ⟨k - 1 - i.val, hir⟩
    simp only [reverseRightTuple] at hr
    have hidx : (⟨k - 1 - (k - 1 - i.val), by omega⟩ : Fin k) = i := by
      ext
      simp only
      omega
    rw [hidx] at hr
    have h1 := (hm.2 i).2
    have h2 := (hm'.2 i).2
    omega

theorem extendedSize_step_le {n k : ℕ}
    {m : Fin k → ℕ} (hm : IsChainSizeTuple n m)
    {i : ℕ} (hi : i ≤ k) :
    extendedSize n m i ≤ extendedSize n m (i + 1) := by
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0
    simp [extendedSize]
  · rcases Nat.lt_or_ge i k with hik | hik
    · have h1 : extendedSize n m i = m ⟨i - 1, by omega⟩ := by
        unfold extendedSize
        rw [dite_eq_right (by omega), dite_eq_left hi]
      have h2 : extendedSize n m (i + 1) = m ⟨i, hik⟩ := by
        unfold extendedSize
        rw [dite_eq_right (by omega), dite_eq_left (by omega)]
        rfl
      rw [h1, h2]
      exact hm.1.monotone (show (⟨i - 1, _⟩ : Fin k) ≤ ⟨i, hik⟩ from by
        show i - 1 ≤ i
        omega)
    · have h1 : extendedSize n m i = m ⟨i - 1, by omega⟩ := by
        unfold extendedSize
        rw [dite_eq_right (by omega), dite_eq_left hi]
      have h2 : extendedSize n m (i + 1) = n := by
        unfold extendedSize
        rw [dite_eq_right (by omega), dite_eq_right (by omega)]
      rw [h1, h2]
      exact (hm.2 _).2.le

private theorem extendedSize_zero {n k : ℕ} (m : Fin k → ℕ) :
    extendedSize n m 0 = 0 := by
  simp [extendedSize]

private theorem extendedSize_of_gt {n k : ℕ} (m : Fin k → ℕ) {i : ℕ} (hi : k < i) :
    extendedSize n m i = n := by
  unfold extendedSize
  rw [dite_eq_right (by omega), dite_eq_right (by omega)]

private theorem extendedSize_mono {n k : ℕ}
    {m : Fin k → ℕ} (hm : IsChainSizeTuple n m) :
    Monotone (extendedSize n m) := by
  apply monotone_nat_of_le_succ
  intro i
  by_cases hi : i ≤ k
  · exact extendedSize_step_le hm hi
  · rw [extendedSize_of_gt m (by omega), extendedSize_of_gt m (by omega)]

theorem sum_chainGap {n k : ℕ}
    (m : Fin k → ℕ) (hm : IsChainSizeTuple n m) :
    ∑ i : Fin (k + 1), chainGap n m i = n := by
  have h := Fin.sum_univ_eq_sum_range
    (fun i => extendedSize n m (i + 1) - extendedSize n m i) (k + 1)
  unfold chainGap
  rw [h, Finset.sum_range_tsub (extendedSize_mono hm), extendedSize_zero,
    extendedSize_of_gt m (by omega), Nat.sub_zero]

/-- Sizes of a tuple and of its initial segment agree up to the length of the
segment. -/
private theorem extendedSize_init {n h : ℕ} (M : Fin (h + 1) → ℕ) {i : ℕ} (hi : i ≤ h) :
    extendedSize n M i = extendedSize n (Fin.init M) i := by
  unfold extendedSize
  by_cases h0 : i = 0
  · rw [dite_eq_left h0, dite_eq_left h0]
  · rw [dite_eq_right h0, dite_eq_right h0, dite_eq_left (by omega), dite_eq_left hi]
    rfl

private theorem extendedSize_last {n h : ℕ} (m : Fin h → ℕ) :
    extendedSize n m h = if h0 : h = 0 then 0 else m ⟨h - 1, by omega⟩ := by
  unfold extendedSize
  by_cases h0 : h = 0
  · rw [dite_eq_left h0, dite_eq_left h0]
  · rw [dite_eq_right h0, dite_eq_right h0, dite_eq_left le_rfl]

private theorem le_extendedSize_last {n h : ℕ} {m : Fin h → ℕ}
    (hm : IsChainSizeTuple n m) (i : Fin h) : m i ≤ extendedSize n m h := by
  have hi := i.isLt
  rw [extendedSize_last, dite_eq_right (by omega)]
  exact hm.1.monotone (show i ≤ ⟨h - 1, by omega⟩ from by
    show i.val ≤ h - 1
    omega)

private theorem isChainSizeTuple_snoc {n h : ℕ} {m : Fin h → ℕ}
    (hm : IsChainSizeTuple n m) {d : ℕ} (hd1 : 1 ≤ d)
    (hd2 : d ≤ n - extendedSize n m h - 1) :
    IsChainSizeTuple n (Fin.snoc m (extendedSize n m h + d) : Fin (h + 1) → ℕ) := by
  refine ⟨?_, ?_⟩
  · intro a b hab
    induction b using Fin.lastCases with
    | last =>
      obtain ⟨a', rfl⟩ := Fin.exists_castSucc_eq.mpr (Fin.ne_last_of_lt hab)
      rw [Fin.snoc_last, Fin.snoc_castSucc]
      have := le_extendedSize_last hm a'
      omega
    | cast b =>
      obtain ⟨a', rfl⟩ := Fin.exists_castSucc_eq.mpr
        (Fin.ne_last_of_lt (lt_trans hab (Fin.castSucc_lt_last b)))
      rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact hm.1 (Fin.castSucc_lt_castSucc_iff.mp hab)
  · intro i
    induction i using Fin.lastCases with
    | last =>
      rw [Fin.snoc_last]
      omega
    | cast i =>
      rw [Fin.snoc_castSucc]
      exact hm.2 i

private theorem isChainSizeTuple_init {n h : ℕ} {M : Fin (h + 1) → ℕ}
    (hM : IsChainSizeTuple n M) : IsChainSizeTuple n (Fin.init M) := by
  refine ⟨?_, fun i => hM.2 _⟩
  intro a b hab
  exact hM.1 (Fin.castSucc_lt_castSucc_iff.mpr hab)

private theorem chainGap_init {n h : ℕ} (M : Fin (h + 1) → ℕ) (i : Fin h) :
    chainGap n M ⟨i.val, by omega⟩ =
      chainGap n (Fin.init M) ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ := by
  unfold chainGap
  have hi := i.isLt
  simp only
  rw [extendedSize_init M (by omega), extendedSize_init M (by omega)]

/-- Split the prefix tuple sum according to its last value. -/
theorem prefixKernelSum_succ (n h : ℕ) (w : ℕ → ℝ) :
    prefixKernelSum n (h + 1) w =
      ∑ m ∈ chainSizeTuples n h,
        (∏ i : Fin h,
          w (chainGap n m ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)) *
        ∑ d ∈ Finset.Icc 1
            (n - extendedSize n m h - 1), w d := by
  classical
  unfold prefixKernelSum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_sigma']
  refine Finset.sum_nbij'
    (fun M => (⟨Fin.init M, M (Fin.last h) - extendedSize n (Fin.init M) h⟩ :
      Σ _ : Fin h → ℕ, ℕ))
    (fun x => (Fin.snoc x.1 (extendedSize n x.1 h + x.2) : Fin (h + 1) → ℕ))
    ?_ ?_ ?_ ?_ ?_
  · intro M hM
    rw [mem_chainSizeTuples_iff] at hM
    rw [Finset.mem_sigma, mem_chainSizeTuples_iff, Finset.mem_Icc]
    dsimp only
    have hlt := (hM.2 (Fin.last h)).2
    have hinit : extendedSize n (Fin.init M) h < M (Fin.last h) := by
      rw [extendedSize_last]
      split_ifs with h0
      · exact (hM.2 (Fin.last h)).1
      · apply hM.1
        show h - 1 < h
        omega
    exact ⟨isChainSizeTuple_init hM, by omega, by omega⟩
  · rintro ⟨m, d⟩ hx
    rw [Finset.mem_sigma, mem_chainSizeTuples_iff, Finset.mem_Icc] at hx
    rw [mem_chainSizeTuples_iff]
    exact isChainSizeTuple_snoc hx.1 hx.2.1 hx.2.2
  · intro M hM
    rw [mem_chainSizeTuples_iff] at hM
    have hinit : extendedSize n (Fin.init M) h ≤ M (Fin.last h) := by
      rw [extendedSize_last]
      split_ifs with h0
      · exact Nat.zero_le _
      · apply hM.1.monotone
        show h - 1 ≤ h
        omega
    simp only
    rw [Nat.add_sub_cancel' hinit, Fin.snoc_init_self]
  · rintro ⟨m, d⟩ _
    simp only [Fin.init_snoc, Fin.snoc_last, Nat.add_sub_cancel_left]
  · intro M _
    rw [Fin.prod_univ_castSucc]
    congr 1
    · apply Finset.prod_congr rfl
      intro i _
      exact congrArg w (chainGap_init M i)
    · congr 1
      unfold chainGap
      simp only [Fin.val_last]
      rw [extendedSize_init M le_rfl]
      congr 1
      unfold extendedSize
      rw [dite_eq_right (by omega), dite_eq_left le_rfl]
      rfl

private theorem extendedSize_leftPrefixTuple {n k : ℕ} (m : Fin k → ℕ) (j : Fin (k + 1))
    {t : ℕ} (ht : t ≤ j.val) :
    extendedSize n (leftPrefixTuple m j) t = extendedSize n m t := by
  have hj := j.isLt
  unfold extendedSize
  by_cases h0 : t = 0
  · rw [dite_eq_left h0, dite_eq_left h0]
  · rw [dite_eq_right h0, dite_eq_right h0, dite_eq_left ht, dite_eq_left (by omega)]
    rfl

private theorem chainGap_reverseRightTuple {n k : ℕ} {m : Fin k → ℕ}
    (hm : IsChainSizeTuple n m) (j : Fin (k + 1)) (i : ℕ) (hi : i < k - j.val) :
    chainGap n (reverseRightTuple n m j) ⟨i, Nat.lt_succ_of_lt hi⟩ =
      chainGap n m ⟨k - i, by omega⟩ := by
  have hj := j.isLt
  unfold chainGap
  simp only
  have h1 : extendedSize n (reverseRightTuple n m j) (i + 1) =
      n - m ⟨k - 1 - i, by omega⟩ := by
    unfold extendedSize
    rw [dite_eq_right (by omega), dite_eq_left (by omega)]
    rfl
  have h3 : extendedSize n m (k - i) = m ⟨k - i - 1, by omega⟩ := by
    unfold extendedSize
    rw [dite_eq_right (by omega), dite_eq_left (by omega)]
  rw [h1, h3]
  have hlt := (hm.2 ⟨k - 1 - i, by omega⟩).2
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0
    have h2 : extendedSize n (reverseRightTuple n m j) 0 = 0 :=
      extendedSize_zero _
    have h4 : extendedSize n m (k - 0 + 1) = n :=
      extendedSize_of_gt m (by omega)
    rw [h2, h4]
    have hidx : (⟨k - 0 - 1, by omega⟩ : Fin k) = ⟨k - 1 - 0, by omega⟩ := by
      ext
      simp only
      omega
    rw [hidx]
    omega
  · have h2 : extendedSize n (reverseRightTuple n m j) i =
        n - m ⟨k - 1 - (i - 1), by omega⟩ := by
      unfold extendedSize
      rw [dite_eq_right (by omega), dite_eq_left (by omega)]
      rfl
    have h4 : extendedSize n m (k - i + 1) = m ⟨k - i, by omega⟩ := by
      unfold extendedSize
      rw [dite_eq_right (by omega), dite_eq_left (by omega)]
      congr 1
    rw [h2, h4]
    have hidx1 : (⟨k - 1 - (i - 1), by omega⟩ : Fin k) = ⟨k - i, by omega⟩ := by
      ext
      simp only
      omega
    have hidx2 : (⟨k - 1 - i, by omega⟩ : Fin k) = ⟨k - i - 1, by omega⟩ := by
      ext
      simp only
      omega
    rw [hidx1, hidx2]
    have hmono : m ⟨k - i - 1, by omega⟩ ≤ m ⟨k - i, by omega⟩ :=
      hm.1.monotone (show (⟨k - i - 1, _⟩ : Fin k) ≤ ⟨k - i, _⟩ from by
        show k - i - 1 ≤ k - i
        omega)
    have hlt2 := (hm.2 ⟨k - i, by omega⟩).2
    omega

/-- Omitting the `j`-th gap splits the product into the left prefix and the
reversed right part.  (The chain hypothesis is needed: truncated subtraction makes
the reversed gaps differ from the original ones for non-monotone tuples.) -/
theorem omitted_product_split {n k : ℕ} (w : ℕ → ℝ)
    (m : Fin k → ℕ) (j : Fin (k + 1))
    (hm : IsChainSizeTuple n m) :
    (∏ i ∈ Finset.univ.erase j, w (chainGap n m i)) =
      (∏ i : Fin j.val,
        w (chainGap n (leftPrefixTuple m j)
          ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)) *
      (∏ i : Fin (k - j.val),
        w (chainGap n (reverseRightTuple n m j)
          ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)) := by
  classical
  have hj := j.isLt
  set G : ℕ → ℝ := fun t => w (extendedSize n m (t + 1) - extendedSize n m t) with hG
  have hL : ∏ i ∈ Finset.univ.erase j, w (chainGap n m i) =
      ∏ t ∈ (Finset.range (k + 1)).erase j.val, G t := by
    have himage : (Finset.univ.erase j).image Fin.val =
        (Finset.range (k + 1)).erase j.val := by
      ext t
      simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true,
        Finset.mem_range]
      constructor
      · rintro ⟨i, hij, rfl⟩
        exact ⟨fun h => hij (Fin.ext h), i.isLt⟩
      · rintro ⟨htj, htk⟩
        exact ⟨⟨t, htk⟩, fun h => htj (by rw [← h]), rfl⟩
    rw [← himage, Finset.prod_image (fun a _ b _ h => Fin.ext h)]
    rfl
  have hsplit : (Finset.range (k + 1)).erase j.val =
      Finset.range j.val ∪ Finset.Ico (j.val + 1) (k + 1) := by
    ext t
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    omega
  have hdisj : Disjoint (Finset.range j.val) (Finset.Ico (j.val + 1) (k + 1)) := by
    rw [Finset.disjoint_left]
    intro t ht1 ht2
    simp only [Finset.mem_range] at ht1
    simp only [Finset.mem_Ico] at ht2
    omega
  have hleft : (∏ i : Fin j.val,
        w (chainGap n (leftPrefixTuple m j) ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)) =
      ∏ t ∈ Finset.range j.val, G t := by
    rw [← Fin.prod_univ_eq_prod_range]
    apply Finset.prod_congr rfl
    intro i _
    have hi := i.isLt
    unfold chainGap
    simp only [hG]
    rw [extendedSize_leftPrefixTuple m j (by omega),
      extendedSize_leftPrefixTuple m j (by omega)]
  have hright : (∏ i : Fin (k - j.val),
        w (chainGap n (reverseRightTuple n m j) ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)) =
      ∏ t ∈ Finset.Ico (j.val + 1) (k + 1), G t := by
    have h1 : (∏ i : Fin (k - j.val),
        w (chainGap n (reverseRightTuple n m j) ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)) =
        ∏ i : Fin (k - j.val), G (k - i.val) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [chainGap_reverseRightTuple hm j i.val i.isLt]
      rfl
    rw [h1, Fin.prod_univ_eq_prod_range (fun t => G (k - t))]
    apply Finset.prod_nbij' (fun t => k - t) (fun t => k - t)
    · intro t ht
      simp only [Finset.mem_range] at ht
      simp only [Finset.mem_Ico]
      omega
    · intro t ht
      simp only [Finset.mem_Ico] at ht
      simp only [Finset.mem_range]
      omega
    · intro t ht
      simp only [Finset.mem_range] at ht
      omega
    · intro t ht
      simp only [Finset.mem_Ico] at ht
      omega
    · intro t _
      rfl
  rw [hL, hsplit, Finset.prod_union hdisj, hleft, hright]

theorem extendedSize_at_succ {n k : ℕ}
    {m : Fin k → ℕ}
    (i : Fin k) :
    extendedSize n m (i.val + 1) = m i := by
  have hi := i.isLt
  unfold extendedSize
  rw [dite_eq_right (by omega), dite_eq_left (by omega)]
  rfl

theorem chainGap_prefix_sum {n k : ℕ}
    (m : Fin k → ℕ) (hm : IsChainSizeTuple n m)
    (i : Fin k) :
    ∑ j : Fin (i.val + 1),
      chainGap n m ⟨j.val, by omega⟩ = m i := by
  have h := Fin.sum_univ_eq_sum_range
    (fun t => extendedSize n m (t + 1) - extendedSize n m t) (i.val + 1)
  unfold chainGap
  rw [h, Finset.sum_range_tsub (extendedSize_mono hm), extendedSize_zero,
    extendedSize_at_succ i, Nat.sub_zero]

/-- The kernel appearing in Lemma 4.3. -/
def lemma43Kernel (p n : ℕ) (C : ℝ) (d : ℕ) : ℝ :=
  chainFactor p n C d

/-- The summand in Lemma 4.3 for a single increasing k-tuple. -/
def lemma43Summand {k : ℕ} (p n : ℕ) (C : ℝ)
    (m : Fin k → ℕ) : ℝ :=
  chainUpperBound p n C m

/-- Full left side of Lemma 4.3. -/
def lemma43LHS (p n k : ℕ) (C : ℝ) : ℝ :=
  ∑ m ∈ chainSizeTuples n k, lemma43Summand p n C m

/-- Right side of Lemma 4.3. -/
def lemma43RHS (p n k : ℕ) (C : ℝ) : ℝ :=
  (k + 1 : ℝ) *
    ((n : ℝ) / p +
      2 * C * Real.sqrt (Real.log (n : ℝ)) /
        Real.sqrt (n : ℝ)) ^ k

/-- Corollary 1.4 exactly. -/
def Corollary14Statement : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 →
    ∃ Cε : ℝ, 0 < Cε ∧
      ∀ (p : ℕ) (hp : p.Prime),
        letI : NeZero p := ⟨hp.ne_zero⟩
        ∀ (S : Finset (ZMod p)), 2 ≤ S.card →
        ∀ (m : ℕ), 0 < m →
          (m : ℝ) ≤ (1 - ε) * S.card →
          ∀ z : ZMod p,
            sliceMass S m z ≤
              1 / (p : ℝ) +
                Cε * Real.sqrt (Real.log (S.card : ℝ)) /
                  ((S.card : ℝ) * Real.sqrt (m : ℝ))

/-- Corollary 4.2 exactly. -/
def Corollary42Statement : Prop :=
  ∀ (k : ℕ), 0 < k →
    ∃ Ck : ℝ, 0 < Ck ∧
      ∀ (p : ℕ) (hp : p.Prime),
        letI : NeZero p := ⟨hp.ne_zero⟩
        ∀ (S : Finset (ZMod p)), 2 ≤ S.card →
        ∀ (m : Fin k → ℕ), IsChainSizeTuple S.card m →
        ∀ z : Fin k → ZMod p,
          chainMass S m z ≤ chainUpperBound p S.card Ck m

/-- Lemma 4.3, expressed using the finite family of increasing tuples, for every constant
`C_k > 0` (not only that of Corollary 4.2) and every `n = |S| ≥ 2`. -/
def Lemma43Statement : Prop :=
  ∀ (k : ℕ), 0 < k →
    ∀ Ck : ℝ, 0 < Ck →
      ∀ (p : ℕ), p.Prime →
      ∀ n : ℕ, 2 ≤ n →
        lemma43LHS p n k Ck ≤ lemma43RHS p n k Ck

end

end GrahamRearrangement
