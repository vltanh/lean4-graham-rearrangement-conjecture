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
  sorry

theorem withoutReplacementExpectation_const
    {α : Type*} [DecidableEq α]
    (U : Finset α) {k : ℕ} (hk : k ≤ U.card) (c : ℝ) :
    withoutReplacementExpectation U k (fun _ => c) = c := by
  sorry

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
  sorry

theorem withoutReplacementMass_congr_on_samples
    {α : Type*} [DecidableEq α]
    (U : Finset α) (k : ℕ)
    (E F : List α → Prop) [DecidablePred E] [DecidablePred F]
    (h : ∀ xs, IsWithoutReplacementSample U k xs → (E xs ↔ F xs)) :
    withoutReplacementMass U k E =
      withoutReplacementMass U k F := by
  sorry

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
  sorry

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
  sorry

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
  sorry

theorem withoutReplacementMass_toFinset
    {α : Type*} [DecidableEq α]
    (U : Finset α) (k : ℕ) (hk : k ≤ U.card)
    (E : Finset α → Prop) [DecidablePred E] :
    withoutReplacementMass U k (fun xs => E xs.toFinset) =
      uniformMass (U.powersetCard k) E := by
  sorry

end

end GrahamRearrangement.External.Hypergeometric
