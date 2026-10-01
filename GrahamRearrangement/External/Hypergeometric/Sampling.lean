module

public import GrahamRearrangement.Probability

@[expose] public section

open scoped BigOperators

namespace GrahamRearrangement.External.Hypergeometric

/-!
# Sampling without replacement

A finite, source-level model of sequential sampling without replacement.
The main result identifies the unordered sample produced by this recursion with
the uniform distribution on `U.powersetCard k`.
-/

noncomputable section

/-- Monotonicity of the finite uniform expectation, for a pointwise bound on
the sample space. (Proved locally, so that this file is self-contained.) -/
theorem uniformExpectation_le_of_forall_mem {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (f g : Ω → ℝ)
    (hfg : ∀ ω ∈ space, f ω ≤ g ω) :
    uniformExpectation space f ≤ uniformExpectation space g := by
  unfold uniformExpectation
  gcongr with ω hω
  exact hfg ω hω

/-- The finite uniform expectation only depends on the values on the sample
space. -/
theorem uniformExpectation_congr_on {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (f g : Ω → ℝ)
    (hfg : ∀ ω ∈ space, f ω = g ω) :
    uniformExpectation space f = uniformExpectation space g := by
  unfold uniformExpectation
  rw [Finset.sum_congr rfl hfg]

/-- Expectation under k sequential uniform draws without replacement. -/
def withoutReplacementExpectation {α : Type*} [DecidableEq α]
    (U : Finset α) : (k : ℕ) → (List α → ℝ) → ℝ
  | 0, f => f []
  | k + 1, f =>
      uniformExpectation U fun x =>
        withoutReplacementExpectation (U.erase x) k
          (fun xs => f (x :: xs))

/-- Event probability for the recursive without-replacement sampler. -/
def withoutReplacementMass {α : Type*} [DecidableEq α]
    (U : Finset α) (k : ℕ) (E : List α → Prop)
    [DecidablePred E] : ℝ :=
  withoutReplacementExpectation U k
    (fun xs => if E xs then 1 else 0)

theorem withoutReplacementExpectation_zero {α : Type*} [DecidableEq α]
    (U : Finset α) (f : List α → ℝ) :
    withoutReplacementExpectation U 0 f = f [] := rfl

theorem withoutReplacementExpectation_succ {α : Type*} [DecidableEq α]
    (U : Finset α) (k : ℕ) (f : List α → ℝ) :
    withoutReplacementExpectation U (k + 1) f =
      uniformExpectation U fun x =>
        withoutReplacementExpectation (U.erase x) k
          (fun xs => f (x :: xs)) := rfl

theorem withoutReplacementExpectation_mono
    {α : Type*} [DecidableEq α]
    (U : Finset α) (k : ℕ) (f g : List α → ℝ)
    (hfg : ∀ xs, f xs ≤ g xs) :
    withoutReplacementExpectation U k f ≤
      withoutReplacementExpectation U k g := by
  induction k generalizing U f g with
  | zero => exact hfg []
  | succ k ih =>
      rw [withoutReplacementExpectation_succ,
        withoutReplacementExpectation_succ]
      apply uniformExpectation_le_of_forall_mem
      intro x _
      exact ih (U.erase x) _ _ (fun xs => hfg (x :: xs))

theorem withoutReplacementExpectation_const
    {α : Type*} [DecidableEq α]
    (U : Finset α) {k : ℕ} (hk : k ≤ U.card) (c : ℝ) :
    withoutReplacementExpectation U k (fun _ => c) = c := by
  induction k generalizing U with
  | zero => rfl
  | succ k ih =>
      have hU : U.Nonempty := Finset.card_pos.mp (by omega)
      rw [withoutReplacementExpectation_succ]
      rw [uniformExpectation_congr_on U _ (fun _ => c)
        (fun x hx => ih (U.erase x)
          (by rw [Finset.card_erase_of_mem hx]; omega))]
      exact uniformExpectation_const U hU c

def IsWithoutReplacementSample {α : Type*} [DecidableEq α]
    (U : Finset α) (k : ℕ) (xs : List α) : Prop :=
  xs.length = k ∧ xs.Nodup ∧ ∀ x ∈ xs, x ∈ U

theorem withoutReplacementExpectation_congr_on_samples
    {α : Type*} [DecidableEq α]
    (U : Finset α) (k : ℕ) (f g : List α → ℝ)
    (h :
      ∀ xs, IsWithoutReplacementSample U k xs → f xs = g xs) :
    withoutReplacementExpectation U k f =
      withoutReplacementExpectation U k g := by
  induction k generalizing U f g with
  | zero =>
      exact h [] ⟨rfl, List.nodup_nil, by simp⟩
  | succ k ih =>
      rw [withoutReplacementExpectation_succ,
        withoutReplacementExpectation_succ]
      apply uniformExpectation_congr_on
      intro x hx
      apply ih (U.erase x)
      rintro xs ⟨hlen, hnd, hmem⟩
      apply h
      have hxnot : x ∉ xs := fun hxin =>
        (Finset.mem_erase.mp (hmem x hxin)).1 rfl
      refine ⟨by simp [hlen], List.nodup_cons.mpr ⟨hxnot, hnd⟩, ?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hx
      · exact Finset.mem_of_mem_erase (hmem y hy)

theorem withoutReplacementMass_congr_on_samples
    {α : Type*} [DecidableEq α]
    (U : Finset α) (k : ℕ)
    (E F : List α → Prop) [DecidablePred E] [DecidablePred F]
    (h : ∀ xs, IsWithoutReplacementSample U k xs → (E xs ↔ F xs)) :
    withoutReplacementMass U k E =
      withoutReplacementMass U k F := by
  unfold withoutReplacementMass
  apply withoutReplacementExpectation_congr_on_samples U k
  intro xs hxs
  exact if_congr (h xs hxs) rfl rfl

/-- The joint space obtained by first choosing x in U and then a k-subset of
U\{x}. -/
def headTailSpace {α : Type*} [DecidableEq α]
    (U : Finset α) (k : ℕ) : Finset (α × Finset α) :=
  U.biUnion fun x =>
    ((U.erase x).powersetCard k).image fun R => (x, R)

theorem mem_headTailSpace {α : Type*} [DecidableEq α]
    {U : Finset α} {k : ℕ} {x : α} {R : Finset α} :
    (x,R) ∈ headTailSpace U k ↔
      x ∈ U ∧ R ∈ (U.erase x).powersetCard k := by
  constructor
  · intro h
    obtain ⟨y, hy, hq⟩ := Finset.mem_biUnion.mp h
    obtain ⟨R', hR', hEq⟩ := Finset.mem_image.mp hq
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
    exact ⟨hy, hR'⟩
  · rintro ⟨hx, hR⟩
    exact Finset.mem_biUnion.mpr
      ⟨x, hx, Finset.mem_image.mpr ⟨R, hR, rfl⟩⟩

def headTailSet {α : Type*} [DecidableEq α]
    (q : α × Finset α) : Finset α :=
  insert q.1 q.2

theorem headTailSet_mem_powersetCard
    {α : Type*} [DecidableEq α]
    {U : Finset α} {k : ℕ} {q : α × Finset α}
    (hq : q ∈ headTailSpace U k) :
    headTailSet q ∈ U.powersetCard (k + 1) := by
  rcases mem_headTailSpace.mp hq with ⟨hx,hR⟩
  rcases Finset.mem_powersetCard.mp hR with ⟨hRU,hcard⟩
  have hxR : q.1 ∉ q.2 := by
    intro hxmem
    have := hRU hxmem
    exact (Finset.mem_erase.mp this).1 rfl
  apply Finset.mem_powersetCard.mpr
  constructor
  · intro y hy
    simp [headTailSet] at hy
    rcases hy with rfl | hy
    · exact hx
    · exact Finset.mem_of_mem_erase (hRU hy)
  · simp [headTailSet,hxR,hcard]

/-- A fixed (k+1)-subset has exactly one head-tail representation for each of
its k+1 elements. -/
theorem headTail_fiber_card
    {α : Type*} [DecidableEq α]
    (U : Finset α) (k : ℕ)
    {T : Finset α} (hT : T ∈ U.powersetCard (k + 1)) :
    ((headTailSpace U k).filter fun q => headTailSet q = T).card =
      k + 1 := by
  classical
  let A :=
    (headTailSpace U k).filter fun q => headTailSet q = T
  let f : {q // q ∈ A} → {x // x ∈ T} :=
    fun q => ⟨q.1.1, by
      have hqeq := (Finset.mem_filter.mp q.2).2
      rw [← hqeq]
      simp [headTailSet]⟩
  have hinj : Function.Injective f := by
    intro q r h
    apply Subtype.ext
    rcases q with ⟨⟨x,R⟩,hq⟩
    rcases r with ⟨⟨y,Q⟩,hr⟩
    simp only [f, Subtype.mk.injEq] at h
    subst y
    have hRq := (Finset.mem_filter.mp hq).2
    have hQr := (Finset.mem_filter.mp hr).2
    apply Prod.ext
    · rfl
    · have hxR :
          x ∉ R := by
        rcases mem_headTailSpace.mp (Finset.mem_filter.mp hq).1
          with ⟨_,hRmem⟩
        intro hx
        exact (Finset.mem_erase.mp
          ((Finset.mem_powersetCard.mp hRmem).1 hx)).1 rfl
      have hxQ :
          x ∉ Q := by
        rcases mem_headTailSpace.mp (Finset.mem_filter.mp hr).1
          with ⟨_,hQmem⟩
        intro hx
        exact (Finset.mem_erase.mp
          ((Finset.mem_powersetCard.mp hQmem).1 hx)).1 rfl
      have : insert x R = insert x Q := hRq.trans hQr.symm
      simpa [Finset.insert_eq_self, hxR, hxQ] using
        congrArg (Finset.erase · x) this
  have hsurj : Function.Surjective f := by
    intro x
    let R := T.erase x.1
    have hTU := (Finset.mem_powersetCard.mp hT).1
    have hxU : x.1 ∈ U := hTU x.2
    have hRmem : R ∈ (U.erase x.1).powersetCard k := by
      apply Finset.mem_powersetCard.mpr
      constructor
      · intro y hy
        rcases Finset.mem_erase.mp hy with ⟨hyx,hyT⟩
        exact Finset.mem_erase.mpr ⟨hyx,hTU hyT⟩
      · rw [Finset.card_erase_of_mem x.2,
          (Finset.mem_powersetCard.mp hT).2]
        omega
    refine ⟨⟨(x.1,R),?_⟩,?_⟩
    · apply Finset.mem_filter.mpr
      constructor
      · exact mem_headTailSpace.mpr ⟨hxU,hRmem⟩
      · simp [headTailSet,R,x.2]
    · rfl
  have hcard := Fintype.card_congr (Equiv.ofBijective f ⟨hinj,hsurj⟩)
  simpa [A,(Finset.mem_powersetCard.mp hT).2] using hcard

theorem headTail_event_card
    {α : Type*} [DecidableEq α]
    (U : Finset α) (k : ℕ)
    (E : Finset α → Prop) [DecidablePred E] :
    ((headTailSpace U k).filter fun q => E (headTailSet q)).card =
      (k + 1) * ((U.powersetCard (k + 1)).filter E).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
    (f := headTailSet) (t := (U.powersetCard (k + 1)).filter E)
    (by
      intro q hq
      rcases Finset.mem_filter.mp hq with ⟨hspace, hE⟩
      exact Finset.mem_filter.mpr
        ⟨headTailSet_mem_powersetCard hspace, hE⟩)]
  calc
    _ = ∑ _T ∈ (U.powersetCard (k + 1)).filter E, (k + 1) := by
      apply Finset.sum_congr rfl
      intro T hT
      rcases Finset.mem_filter.mp hT with ⟨hTmem, hET⟩
      rw [← headTail_fiber_card U k hTmem, Finset.filter_filter]
      congr 1
      apply Finset.filter_congr
      intro q _
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨h ▸ hET, h⟩
    _ = _ := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- Uniform (k+1)-subset sampling can be exposed by one uniform head followed
by a uniform k-subset of the erased ground set. -/
theorem uniformSubset_head_tail
    {α : Type*} [DecidableEq α]
    (U : Finset α) (k : ℕ) (hk : k + 1 ≤ U.card)
    (E : Finset α → Prop) [DecidablePred E] :
    uniformMass (U.powersetCard (k + 1)) E =
      uniformExpectation U fun x =>
        uniformMass ((U.erase x).powersetCard k)
          (fun R => E (insert x R)) := by
  classical
  have hU : U.Nonempty := Finset.card_pos.mp (by omega)
  unfold uniformMass uniformExpectation
  -- the inner sample spaces all have size `choose (|U| - 1) k`
  have hinner :
      (∑ x ∈ U,
        ((((U.erase x).powersetCard k).filter
            (fun R => E (insert x R))).card : ℝ) /
          (((U.erase x).powersetCard k).card : ℝ)) =
      (∑ x ∈ U,
        ((((U.erase x).powersetCard k).filter
            (fun R => E (insert x R))).card : ℝ)) /
          (Nat.choose (U.card - 1) k : ℝ) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.card_powersetCard, Finset.card_erase_of_mem hx]
  -- the numerators add up to the head-tail count
  have hsum :
      (∑ x ∈ U,
        (((U.erase x).powersetCard k).filter
          (fun R => E (insert x R))).card) =
      ((headTailSpace U k).filter
        (fun q => E (headTailSet q))).card := by
    unfold headTailSpace
    rw [Finset.filter_biUnion, Finset.card_biUnion]
    · apply Finset.sum_congr rfl
      intro x _
      rw [Finset.filter_image, Finset.card_image_of_injective]
      · rfl
      · intro R Q h
        exact (Prod.mk.inj h).2
    · intro x _ y _ hxy
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro q hqx hqy
      rcases Finset.mem_image.mp (Finset.mem_filter.mp hqx).1
        with ⟨R, _, rfl⟩
      rcases Finset.mem_image.mp (Finset.mem_filter.mp hqy).1
        with ⟨Q, _, hEq⟩
      exact hxy (Prod.mk.inj hEq).1.symm
  have hcount :
      (∑ x ∈ U,
        ((((U.erase x).powersetCard k).filter
            (fun R => E (insert x R))).card : ℝ)) =
      ((k + 1 : ℕ) : ℝ) * (((U.powersetCard (k + 1)).filter E).card : ℝ) := by
    rw [← Nat.cast_mul, ← headTail_event_card U k E, ← hsum, Nat.cast_sum]
  have hchoose :
      (U.card : ℝ) * (Nat.choose (U.card - 1) k : ℝ) =
        (Nat.choose U.card (k + 1) : ℝ) * ((k + 1 : ℕ) : ℝ) := by
    have h := Nat.add_one_mul_choose_eq (U.card - 1) k
    rw [Nat.sub_add_cancel (by omega : 1 ≤ U.card)] at h
    exact_mod_cast h
  rw [hinner, hcount, Finset.card_powersetCard]
  have hchild : (0 : ℝ) < (Nat.choose (U.card - 1) k : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hbig : (0 : ℝ) < (Nat.choose U.card (k + 1) : ℝ) := by
    exact_mod_cast Nat.choose_pos hk
  have hUpos : (0 : ℝ) < (U.card : ℝ) := by exact_mod_cast hU.card_pos
  have hk1 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  rw [div_div, div_eq_div_iff hbig.ne' (by positivity)]
  linear_combination
    (((U.powersetCard (k + 1)).filter E).card : ℝ) * hchoose

theorem withoutReplacementMass_toFinset
    {α : Type*} [DecidableEq α]
    (U : Finset α) (k : ℕ) (hk : k ≤ U.card)
    (E : Finset α → Prop) [DecidablePred E] :
    withoutReplacementMass U k (fun xs => E xs.toFinset) =
      uniformMass (U.powersetCard k) E := by
  induction k generalizing U E with
  | zero =>
      by_cases hE : E ∅ <;>
        simp [withoutReplacementMass, withoutReplacementExpectation,
          uniformMass, Finset.powersetCard_zero, Finset.filter_singleton, hE]
  | succ k ih =>
      rw [withoutReplacementMass, withoutReplacementExpectation_succ,
        uniformSubset_head_tail U k hk E]
      apply uniformExpectation_congr_on
      intro x hx
      have hchild : k ≤ (U.erase x).card := by
        rw [Finset.card_erase_of_mem hx]
        omega
      rw [← ih (U.erase x) hchild (fun R => E (insert x R))]
      simp only [withoutReplacementMass, List.toFinset_cons]

end

end GrahamRearrangement.External.Hypergeometric
