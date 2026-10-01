module

public import GrahamRearrangement.BooleanSlice.Definitions
public import GrahamRearrangement.External

@[expose] public section

open scoped BigOperators Pointwise

namespace GrahamRearrangement.Section3External

/-!
# External sampling/Fourier inputs specialized to the Section 3 model

These are still generic finite-probability or Fourier facts, not results of
Pham--Sauermann.  The paper's Lemmas 3.1--3.7 are proved in subsequent modules.
-/

noncomputable section

theorem balancedPartitions_nonempty {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hm : 0 < m) (hmS : m ≤ S.card) :
    (balancedPartitions (p := p) (m := m) S).Nonempty := by
  refine ⟨canonicalBalancedPartition S hm hmS, ?_⟩
  simp [balancedPartitions, canonicalBalancedPartition_spec S hm hmS]

theorem balancedChoiceSpace_card {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) :
    (balancedChoiceSpace (m := m) S).card =
      (balancedPartitions (m := m) S).card *
        balancedChoiceMultiplicity S.card m := by
  sorry

theorem balancedChoice_event_card {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (E : (Fin m → ZMod p) → Prop)
    [DecidablePred E] :
    ((balancedChoiceSpace (m := m) S).filter fun q => E q.2).card =
      ∑ P ∈ balancedPartitions S,
        ((blockChoices P).filter E).card := by
  sorry

def permuteBalancedPartition {p m : ℕ}
    (π : Equiv.Perm (ZMod p))
    (P : Fin m → Finset (ZMod p)) :
    Fin m → Finset (ZMod p) :=
  fun i => (P i).image π

def permuteBlockChoice {p m : ℕ}
    (π : Equiv.Perm (ZMod p))
    (X : Fin m → ZMod p) :
    Fin m → ZMod p :=
  fun i => π (X i)

theorem permuteBalancedPartition_spec {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    (π : Equiv.Perm (ZMod p)) (hπS : S.image π = S)
    {P : Fin m → Finset (ZMod p)}
    (hP : IsBalancedPartition S P) :
    IsBalancedPartition S (permuteBalancedPartition π P) := by
  classical
  constructor
  · intro i x hx
    rcases Finset.mem_image.mp hx with ⟨y,hy,rfl⟩
    rw [← hπS]
    exact Finset.mem_image.mpr ⟨y,hP.1 i hy,rfl⟩
  constructor
  · intro i j hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    rcases Finset.mem_image.mp hxi with ⟨a,hai,ha⟩
    rcases Finset.mem_image.mp hxj with ⟨b,hbj,hb⟩
    have hab : a = b := π.injective (ha.trans hb.symm)
    subst b
    exact Finset.disjoint_left.mp (hP.2.1 i j hij) hai hbj
  constructor
  · intro x
    constructor
    · intro hx
      rw [← hπS] at hx
      rcases Finset.mem_image.mp hx with ⟨y,hy,rfl⟩
      rcases (hP.2.2.1 y).1 hy with ⟨i,hyi⟩
      exact ⟨i,Finset.mem_image.mpr ⟨y,hyi,rfl⟩⟩
    · rintro ⟨i,hxi⟩
      rcases Finset.mem_image.mp hxi with ⟨y,hyi,rfl⟩
      rw [← hπS]
      exact Finset.mem_image.mpr
        ⟨y,(hP.2.2.1 y).2 ⟨i,hyi⟩,rfl⟩
  · intro i
    unfold permuteBalancedPartition
    rw [Finset.card_image_of_injective _ π.injective,
      hP.2.2.2 i]

theorem permuteBlockChoice_mem {p m : ℕ} [NeZero p]
    (π : Equiv.Perm (ZMod p))
    {P : Fin m → Finset (ZMod p)}
    {X : Fin m → ZMod p}
    (hX : X ∈ blockChoices P) :
    permuteBlockChoice π X ∈
      blockChoices (permuteBalancedPartition π P) := by
  apply blockChoices_mem_iff.mpr
  intro i
  exact Finset.mem_image.mpr
    ⟨X i,(blockChoices_mem_iff.mp hX) i,rfl⟩

theorem choiceSet_permute {p m : ℕ}
    (π : Equiv.Perm (ZMod p)) (X : Fin m → ZMod p) :
    choiceSet (permuteBlockChoice π X) =
      (choiceSet X).image π := by
  ext x
  simp [choiceSet,permuteBlockChoice]

theorem balancedChoice_fiber_equipotent {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    {R R' : Finset (ZMod p)}
    (hR : R ∈ S.powersetCard m)
    (hR' : R' ∈ S.powersetCard m) :
    ((balancedChoiceSpace (m := m) S).filter fun q => choiceSet q.2 = R).card =
    ((balancedChoiceSpace (m := m) S).filter fun q => choiceSet q.2 = R').card := by
  sorry

theorem balancedChoiceSpace_nonempty {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hm : 0 < m) (hmS : m ≤ S.card) :
    (balancedChoiceSpace (m := m) S).Nonempty := by
  sorry

theorem balancedChoice_choiceSet_uniform {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hm : 0 < m) (hmS : m ≤ S.card)
    (E : Finset (ZMod p) → Prop) [DecidablePred E] :
    uniformMass (balancedChoiceSpace (m := m) S)
        (fun q => E (choiceSet q.2)) =
      uniformMass (S.powersetCard m) E := by
  sorry

theorem balancedChoice_mass_eq_partitionExpectation {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hm : 0 < m) (hmS : m ≤ S.card)
    (z : ZMod p) :
    uniformMass (balancedChoiceSpace (m := m) S)
        (fun q => choiceSum q.2 = z) =
      partitionExpectation (m := m) S (fun P => conditionalSumMass P z) := by
  sorry

/-- The balanced-partition/one-choice-per-block sampling experiment is exactly
uniform on size-`m` subsets. -/
theorem sliceMass_eq_partition_average {p m : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hm : 0 < m) (hmS : m ≤ S.card)
    (z : ZMod p) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    sliceMass S m z =
      partitionExpectation (m := m) S (fun P => conditionalSumMass P z) := by
  sorry

/-- Every block in a valid balanced partition has the prescribed size. -/
theorem balanced_block_size_bounds {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hm : 0 < m) (hmS : m ≤ S.card)
    {P : Fin m → Finset (ZMod p)} (hP : IsBalancedPartition S P)
    (i : Fin m) :
    S.card / m ≤ (P i).card ∧
      (P i).card ≤ S.card / m + 1 := by
  rw [hP.2.2.2 i]
  unfold balancedBlockSize
  split <;> omega

/-- The quantitative block-size estimate used in (3.3). -/
theorem balanced_block_sqrt_two_bound {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hS : 2 ≤ S.card)
    (hm4 : m ≤ S.card / 4)
    {P : Fin m → Finset (ZMod p)} (hP : IsBalancedPartition S P)
    (i : Fin m) :
    ((P i).card : ℝ) ≤ Real.sqrt 2 * S.card / m := by
  sorry

/-- After removing a fixed point, its balanced block still has at least
|S|/(2m) remaining points in the Section 3 range. -/
theorem point_block_remainder_lower {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (x : ZMod p)
    (hm : 0 < m) (hm4 : m ≤ S.card / 4)
    {P : Fin m → Finset (ZMod p)}
    (hP : IsBalancedPartition S P) (hx : x ∈ S) :
    S.card / (2 * m) ≤ (pointBlock S P x \ {x}).card := by
  sorry

theorem permuteBalancedPartition_blockIndex
    {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (x : ZMod p)
    (hm : 0 < m) (hxS : x ∈ S)
    (π : Equiv.Perm (ZMod p))
    (hπS : S.image π = S) (hπx : π x = x)
    {P : Fin m → Finset (ZMod p)}
    (hP : IsBalancedPartition S P) :
    blockIndex S (permuteBalancedPartition π P) x =
      blockIndex S P x := by
  let i := blockIndex S P x
  have hxi : x ∈ P i :=
    mem_blockIndex S P x hm hP hxS
  have hP' := permuteBalancedPartition_spec S π hπS hP
  apply blockIndex_eq_of_mem S hm hP' hxS
  exact Finset.mem_image.mpr ⟨x,hxi,hπx⟩

theorem permute_pointBlock_remainder
    {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (x : ZMod p)
    (hm : 0 < m) (hxS : x ∈ S)
    (π : Equiv.Perm (ZMod p))
    (hπS : S.image π = S) (hπx : π x = x)
    {P : Fin m → Finset (ZMod p)}
    (hP : IsBalancedPartition S P) :
    pointBlock S (permuteBalancedPartition π P) x \ {x} =
      (pointBlock S P x \ {x}).image π := by
  sorry

def blockIndexFiber {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (x : ZMod p) (i : Fin m) (hm : 0 < m := by assumption) :
    Finset (Fin m → Finset (ZMod p)) :=
  (balancedPartitions S).filter fun P => blockIndex S P x = i

theorem blockRemainder_fiber_equipotent
    {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (x : ZMod p)
    (hm : 0 < m) (hmS : m ≤ S.card) (hxS : x ∈ S)
    (i : Fin m)
    {A B : Finset (ZMod p)}
    (hA : A ∈ (S \ {x}).powersetCard
      (balancedBlockSize S.card m i - 1))
    (hB : B ∈ (S \ {x}).powersetCard
      (balancedBlockSize S.card m i - 1)) :
    ((blockIndexFiber S x i).filter fun P =>
      pointBlock S P x \ {x} = A).card =
    ((blockIndexFiber S x i).filter fun P =>
      pointBlock S P x \ {x} = B).card := by
  sorry

theorem blockRemainder_conditional_uniform
    {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (x : ZMod p)
    (hm : 0 < m) (hmS : m ≤ S.card) (hxS : x ∈ S)
    (i : Fin m)
    (hfiber : (blockIndexFiber S x i).Nonempty)
    (E : Finset (ZMod p) → Prop) [DecidablePred E] :
    uniformMass (blockIndexFiber S x i)
      (fun P => E (pointBlock S P x \ {x})) =
    uniformMass
      ((S \ {x}).powersetCard
        (balancedBlockSize S.card m i - 1)) E := by
  sorry

theorem point_block_remainder_lower_real {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (x : ZMod p)
    (hm : 0 < m) (hm4 : m ≤ S.card / 4)
    {P : Fin m → Finset (ZMod p)}
    (hP : IsBalancedPartition S P) (hx : x ∈ S) :
    (S.card : ℝ) / (2 * m) ≤
      ((pointBlock S P x \ {x}).card : ℝ) := by
  sorry

/-- Lemma 3.1's hypergeometric application.  The only external input is the
generic hypergeometric lower-tail estimate in `External.hypergeom_quarter_lower_tail`. -/
theorem block_sparse_tail {p m : ℕ} [NeZero p]
    (S G : Finset (ZMod p)) (x : ZMod p)
    (hx : x ∈ S) (hxG : x ∉ G) (hGS : G ⊆ S)
    (hdensity : S.card ≤ 4 * G.card)
    (hm : 0 < m) (hm4 : m ≤ S.card / 4) :
    partitionMass S (fun P =>
      ((pointBlock S P x \ {x}) ∩ G).card <
        S.card / (16 * m)) ≤
      Real.exp (-(S.card : ℝ) / (64 * m)) := by
  sorry

/-- Lemma 3.3's hypergeometric application.  Again the Chernoff estimate itself
is the only external ingredient. -/
theorem block_dense_tail {p m : ℕ} [NeZero p]
    (S G : Finset (ZMod p)) (x : ZMod p)
    (hx : x ∈ S) (hxG : x ∉ G) (hGS : G ⊆ S)
    (hdensity : 3 * S.card ≤ 4 * G.card)
    (hm : 0 < m) (hm4 : m ≤ S.card / 4) :
    partitionMass S (fun P =>
      ((pointBlock S P x \ {x}) ∩ G).card <
        S.card / (4 * m)) ≤
      Real.exp (-(S.card : ℝ) / (48 * m)) := by
  sorry

/-- Fubini for counting a finite family of partition events. -/
theorem partitionExpectation_card_eq_sum_mass {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (E : ZMod p → (Fin m → Finset (ZMod p)) → Prop)
    [∀ χ, DecidablePred (E χ)] :
    partitionExpectation (m := m) S
        (fun P => ((Finset.univ.filter fun χ => E χ P).card : ℝ)) =
      ∑ χ : ZMod p, partitionMass S (E χ) := by
  sorry

/-- Average indicator bound for a deterministic subset of characters. -/
theorem partitionExpectation_filter_le {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (T : Finset (ZMod p))
    (E : ZMod p → (Fin m → Finset (ZMod p)) → Prop)
    [∀ χ, DecidablePred (E χ)]
    (hbound : ∀ χ ∈ T, partitionMass S (E χ) ≤ 1 / (S.card : ℝ) ^ 9) :
    partitionExpectation (m := m) S
      (fun P => ((T.filter fun χ => E χ P).card : ℝ)) ≤
        (T.card : ℝ) / (S.card : ℝ) ^ 9 := by
  sorry

/-- Generic double counting over the rows of a partition energy. -/
theorem partition_energy_lower_by_rows {α ι : Type*}
    [Fintype ι] [DecidableEq α]
    (S : Finset α) (P : ι → Finset α)
    (hpartition : (∀ i, P i ⊆ S) ∧
      (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
      (∀ x, x ∈ S ↔ ∃ i, x ∈ P i))
    (w : α → α → ℝ) (rowLower : α → ℝ)
    (hrow : ∀ i, ∀ x ∈ P i,
      rowLower x ≤ ∑ y ∈ P i, w x y) :
    ∑ i, ∑ x ∈ P i, ∑ y ∈ P i, w x y ≥
      ∑ x ∈ S, rowLower x := by
  classical
  have hsum :
      ∑ i, ∑ x ∈ P i, rowLower x =
        ∑ x ∈ S, rowLower x := by
    rw [← Finset.sum_biUnion]
    · congr 1
      ext x
      simp [hpartition.2.2 x]
    · intro i hi j hj hij
      exact hpartition.2.1 i j hij
  rw [← hsum]
  gcongr with i hi x hx
  exact hrow i x hx

/-- Pair-uniform expectation expands into the double average over `S×S`. -/
theorem pair_uniform_expectation {α : Type*} [DecidableEq α]
    (S : Finset α) (hS : S.Nonempty) (f : α → α → ℝ) :
    uniformExpectation (S.product S) (fun q => f q.1 q.2) =
      (1 / (S.card : ℝ) ^ 2) *
        ∑ x ∈ S, ∑ y ∈ S, f x y := by
  sorry

/-- Averaging over one coordinate extracts a fixed witness with at least the
global average success probability. -/
theorem exists_fiber_mass_ge_pair_mass {α : Type*} [DecidableEq α]
    (S : Finset α) (hS : S.Nonempty) (E : α → α → Prop)
    [DecidablePred fun q : α × α => E q.1 q.2]
    [∀ y, DecidablePred fun x => E x y] :
    ∃ y ∈ S,
      uniformMass S (fun x => E x y) ≥
        uniformMass (S.product S) (fun q => E q.1 q.2) := by
  sorry


end

end GrahamRearrangement.Section3External
