module

public import GrahamRearrangement.BooleanSlice.Definitions
public import GrahamRearrangement.Auxiliary

@[expose] public section

open scoped BigOperators Pointwise

namespace GrahamRearrangement.Section3

/-!
# Auxiliary lemmas for Section 3

Finite-probability and Fourier facts specialized to the random-partition model of Section 3.
None of them is a result of the paper; Lemmas 3.1–3.7 are proved in `Lemmas.lean`.
-/

noncomputable section

theorem balancedPartitions_nonempty {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hm : 0 < m) (hmS : m ≤ S.card) :
    (balancedPartitions (p := p) (m := m) S).Nonempty := by
  refine ⟨canonicalBalancedPartition S hm hmS, ?_⟩
  simp [balancedPartitions, canonicalBalancedPartition_spec S hm hmS]

theorem mem_balancedPartitions {p m : ℕ} [NeZero p]
    {S : Finset (ZMod p)} {P : Fin m → Finset (ZMod p)} :
    P ∈ balancedPartitions S ↔ IsBalancedPartition S P := by
  unfold balancedPartitions
  simp

/-- The fibre of the joint sample space over a fixed partition, restricted to an
event of the block choice, is a copy of the corresponding set of block choices. -/
theorem balancedChoiceSpace_filter_fst_eq {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (E : (Fin m → ZMod p) → Prop) [DecidablePred E]
    {P : Fin m → Finset (ZMod p)} (hP : P ∈ balancedPartitions S) :
    (((balancedChoiceSpace (m := m) S).filter fun q => E q.2).filter
        fun q => q.1 = P) =
      ((blockChoices P).filter E).map
        ⟨fun X => (P, X), Prod.mk_right_injective P⟩ := by
  ext ⟨Q, X⟩
  simp only [Finset.mem_filter, Finset.mem_map, mem_balancedChoiceSpace,
    Function.Embedding.coeFn_mk, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨⟨-, hX⟩, hE⟩, rfl⟩
    exact ⟨X, ⟨hX, hE⟩, rfl, rfl⟩
  · rintro ⟨Y, ⟨hY, hE⟩, rfl, rfl⟩
    exact ⟨⟨⟨hP, hY⟩, hE⟩, rfl⟩

theorem balancedChoice_event_card {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (E : (Fin m → ZMod p) → Prop)
    [DecidablePred E] :
    ((balancedChoiceSpace (m := m) S).filter fun q => E q.2).card =
      ∑ P ∈ balancedPartitions S,
        ((blockChoices P).filter E).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := balancedPartitions S)]
  · apply Finset.sum_congr rfl
    intro P hP
    rw [balancedChoiceSpace_filter_fst_eq S E hP, Finset.card_map]
  · rintro ⟨Q, X⟩ hq
    exact (mem_balancedChoiceSpace.mp (Finset.mem_filter.mp hq).1).1

theorem balancedChoiceSpace_card {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) :
    (balancedChoiceSpace (m := m) S).card =
      (balancedPartitions (m := m) S).card *
        balancedChoiceMultiplicity S.card m := by
  have h := balancedChoice_event_card (m := m) S (fun _ => True)
  rw [Finset.filter_true_of_mem (fun _ _ => trivial)] at h
  rw [h, Finset.card_eq_sum_ones, Finset.sum_mul, one_mul]
  apply Finset.sum_congr rfl
  intro P hP
  rw [Finset.filter_true_of_mem (fun _ _ => trivial)]
  exact blockChoices_card_balanced (mem_balancedPartitions.mp hP)

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

theorem image_symm_eq_of_image_eq {p : ℕ}
    (π : Equiv.Perm (ZMod p)) {S : Finset (ZMod p)} (hπS : S.image π = S) :
    S.image π.symm = S := by
  conv_lhs => rw [← hπS]
  rw [Finset.image_image]
  simp

theorem permuteBalancedPartition_symm_apply {p m : ℕ}
    (π : Equiv.Perm (ZMod p)) (P : Fin m → Finset (ZMod p)) :
    permuteBalancedPartition π.symm (permuteBalancedPartition π P) = P := by
  funext i
  simp [permuteBalancedPartition, Finset.image_image]

theorem permuteBalancedPartition_apply_symm {p m : ℕ}
    (π : Equiv.Perm (ZMod p)) (P : Fin m → Finset (ZMod p)) :
    permuteBalancedPartition π (permuteBalancedPartition π.symm P) = P := by
  funext i
  simp [permuteBalancedPartition, Finset.image_image]

theorem permuteBlockChoice_symm_apply {p m : ℕ}
    (π : Equiv.Perm (ZMod p)) (X : Fin m → ZMod p) :
    permuteBlockChoice π.symm (permuteBlockChoice π X) = X := by
  funext i
  simp [permuteBlockChoice]

theorem permuteBlockChoice_apply_symm {p m : ℕ}
    (π : Equiv.Perm (ZMod p)) (X : Fin m → ZMod p) :
    permuteBlockChoice π (permuteBlockChoice π.symm X) = X := by
  funext i
  simp [permuteBlockChoice]

/-- A permutation preserving `S` and carrying `R` to `R'` maps the fibre of the
joint sample space over `R` into the fibre over `R'`. -/
theorem permute_mem_choiceSet_fiber {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (π : Equiv.Perm (ZMod p)) (hπS : S.image π = S)
    {R R' : Finset (ZMod p)} (hπR : R.image π = R')
    {q : (Fin m → Finset (ZMod p)) × (Fin m → ZMod p)}
    (hq : q ∈ (balancedChoiceSpace (m := m) S).filter fun q => choiceSet q.2 = R) :
    (permuteBalancedPartition π q.1, permuteBlockChoice π q.2) ∈
      (balancedChoiceSpace (m := m) S).filter fun q => choiceSet q.2 = R' := by
  obtain ⟨P, X⟩ := q
  rw [Finset.mem_filter, mem_balancedChoiceSpace] at hq ⊢
  obtain ⟨⟨hPmem, hX⟩, hset⟩ := hq
  refine ⟨⟨mem_balancedPartitions.mpr
    (permuteBalancedPartition_spec S π hπS (mem_balancedPartitions.mp hPmem)),
    permuteBlockChoice_mem π hX⟩, ?_⟩
  dsimp only at hset ⊢
  rw [choiceSet_permute, hset, hπR]

theorem balancedChoice_fiber_equipotent {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    {R R' : Finset (ZMod p)}
    (hR : R ∈ S.powersetCard m)
    (hR' : R' ∈ S.powersetCard m) :
    ((balancedChoiceSpace (m := m) S).filter fun q => choiceSet q.2 = R).card =
    ((balancedChoiceSpace (m := m) S).filter fun q => choiceSet q.2 = R').card := by
  obtain ⟨π, hπR, hπS, -⟩ :=
    exists_perm_maps_finset S R R'
      (Finset.mem_powersetCard.mp hR).1
      (Finset.mem_powersetCard.mp hR').1
      (by rw [(Finset.mem_powersetCard.mp hR).2, (Finset.mem_powersetCard.mp hR').2])
  have hπS' : S.image π.symm = S := image_symm_eq_of_image_eq π hπS
  have hπR' : R'.image π.symm = R := by
    rw [← hπR, Finset.image_image]
    simp
  apply Finset.card_nbij'
    (fun q => (permuteBalancedPartition π q.1, permuteBlockChoice π q.2))
    (fun q => (permuteBalancedPartition π.symm q.1, permuteBlockChoice π.symm q.2))
  · intro q hq
    exact permute_mem_choiceSet_fiber S π hπS hπR hq
  · intro q hq
    exact permute_mem_choiceSet_fiber S π.symm hπS' hπR' hq
  · intro q _
    simp only [permuteBalancedPartition_symm_apply, permuteBlockChoice_symm_apply]
  · intro q _
    simp only [permuteBalancedPartition_apply_symm, permuteBlockChoice_apply_symm]

theorem balancedChoiceSpace_nonempty {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hm : 0 < m) (hmS : m ≤ S.card) :
    (balancedChoiceSpace (m := m) S).Nonempty := by
  obtain ⟨P, hPmem⟩ := balancedPartitions_nonempty S hm hmS
  have hP : IsBalancedPartition S P := mem_balancedPartitions.mp hPmem
  have hne : ∀ i, (P i).Nonempty := by
    intro i
    apply Finset.card_pos.mp
    rw [hP.2.2.2 i]
    unfold balancedBlockSize
    have := Nat.div_pos hmS hm
    split <;> omega
  choose X hX using hne
  exact ⟨(P, X), mem_balancedChoiceSpace.mpr ⟨hPmem, blockChoices_mem_iff.mpr hX⟩⟩

theorem balancedChoice_choiceSet_uniform {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hm : 0 < m) (hmS : m ≤ S.card)
    (E : Finset (ZMod p) → Prop) [DecidablePred E] :
    uniformMass (balancedChoiceSpace (m := m) S)
        (fun q => E (choiceSet q.2)) =
      uniformMass (S.powersetCard m) E :=
  uniformMass_statistic_of_pairwise_equal_fibers
    (balancedChoiceSpace S) (S.powersetCard m) (fun q => choiceSet q.2)
    (fun q hq => by
      obtain ⟨P, X⟩ := q
      exact choiceSet_mem_powersetCard hq)
    (powersetCard_nonempty S hmS) (balancedChoiceSpace_nonempty S hm hmS)
    (fun _ hR _ hR' => balancedChoice_fiber_equipotent S hR hR') E

theorem balancedChoice_mass_eq_partitionExpectation {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hm : 0 < m) (hmS : m ≤ S.card)
    (z : ZMod p) :
    uniformMass (balancedChoiceSpace (m := m) S)
        (fun q => choiceSum q.2 = z) =
      partitionExpectation (m := m) S (fun P => conditionalSumMass P z) := by
  have hK : (0 : ℝ) < balancedChoiceMultiplicity S.card m := by
    exact_mod_cast balancedChoiceMultiplicity_pos S.card m hm hmS
  unfold partitionExpectation conditionalSumMass uniformExpectation uniformMass
  rw [balancedChoice_event_card S (fun X => choiceSum X = z), balancedChoiceSpace_card S]
  have hden : ∀ P ∈ balancedPartitions (m := m) S,
      (((blockChoices P).filter fun X => choiceSum X = z).card : ℝ) /
          ((blockChoices P).card : ℝ) =
        (((blockChoices P).filter fun X => choiceSum X = z).card : ℝ) /
          (balancedChoiceMultiplicity S.card m : ℝ) := by
    intro P hP
    rw [blockChoices_card_balanced (mem_balancedPartitions.mp hP)]
  rw [Finset.sum_congr rfl hden, ← Finset.sum_div, Nat.cast_sum, Nat.cast_mul,
    div_div, mul_comm (balancedChoiceMultiplicity S.card m : ℝ)]

/-- The balanced-partition/one-choice-per-block sampling experiment is exactly
uniform on size-`m` subsets. -/
theorem sliceMass_eq_partition_average {p m : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hm : 0 < m) (hmS : m ≤ S.card)
    (z : ZMod p) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    sliceMass S m z =
      partitionExpectation (m := m) S (fun P => conditionalSumMass P z) := by
  let _ : NeZero p := ⟨hp.ne_zero⟩
  rw [← balancedChoice_mass_eq_partitionExpectation S hm hmS z]
  unfold sliceMass
  rw [← balancedChoice_choiceSet_uniform S hm hmS (fun R => subsetSum R = z)]
  apply uniformMass_congr
  rintro ⟨P, X⟩ hq
  obtain ⟨hPmem, hX⟩ := mem_balancedChoiceSpace.mp hq
  rw [choiceSum_eq_subsetSum_choiceSet (mem_balancedPartitions.mp hPmem) hX]

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
  have hm : 0 < m := i.pos
  have hmS : m ≤ S.card := le_trans hm4 (Nat.div_le_self _ _)
  have h4m : m * 4 ≤ S.card := (Nat.le_div_iff_mul_le (by norm_num)).mp hm4
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hcard : ((P i).card : ℝ) ≤ (S.card : ℝ) / m + 1 := by
    have h1 := (balanced_block_size_bounds S hm hmS hP i).2
    have h2 : ((S.card / m : ℕ) : ℝ) ≤ (S.card : ℝ) / m := Nat.cast_div_le
    have h3 : ((P i).card : ℝ) ≤ ((S.card / m : ℕ) : ℝ) + 1 := by
      exact_mod_cast h1
    linarith
  have hratio : (4 : ℝ) ≤ (S.card : ℝ) / m := by
    rw [le_div_iff₀ hmR]
    exact_mod_cast (by omega : 4 * m ≤ S.card)
  have hsqrt : (5 / 4 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  rw [mul_div_assoc]
  have := mul_le_mul_of_nonneg_right hsqrt (by linarith : (0 : ℝ) ≤ (S.card : ℝ) / m)
  linarith

/-- After removing a fixed point, its balanced block still has at least
|S|/(2m) remaining points in the Section 3 range. -/
theorem point_block_remainder_lower {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (x : ZMod p)
    (hm : 0 < m) (hm4 : m ≤ S.card / 4)
    {P : Fin m → Finset (ZMod p)}
    (hP : IsBalancedPartition S P) (hx : x ∈ S) :
    S.card / (2 * m) ≤ (pointBlock S P x \ {x}).card := by
  have hmS : m ≤ S.card := le_trans hm4 (Nat.div_le_self _ _)
  have hmem : x ∈ pointBlock S P x := mem_blockIndex S P x hm hP hx
  have hcardBlock : S.card / m ≤ (pointBlock S P x).card :=
    (balanced_block_size_bounds S hm hmS hP (blockIndex S P x)).1
  rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hmem]
  have h4m : m * 4 ≤ S.card := (Nat.le_div_iff_mul_le (by norm_num)).mp hm4
  have hq4 : 4 ≤ S.card / m := (Nat.le_div_iff_mul_le hm).2 (by omega)
  have hdiv : S.card / (2 * m) = S.card / m / 2 := by
    rw [Nat.div_div_eq_div_mul, mul_comm m 2]
  rw [hdiv]
  generalize S.card / m = q at *
  omega

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
  have hidx := permuteBalancedPartition_blockIndex S x hm hxS π hπS hπx hP
  unfold pointBlock
  rw [hidx, Finset.image_sdiff _ _ π.injective, Finset.image_singleton, hπx]
  rfl

def blockIndexFiber {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (x : ZMod p) (i : Fin m) (hm : 0 < m := by assumption) :
    Finset (Fin m → Finset (ZMod p)) :=
  (balancedPartitions S).filter fun P => blockIndex S P x = i

theorem mem_blockIndexFiber {p m : ℕ} [NeZero p]
    {S : Finset (ZMod p)} {x : ZMod p} {i : Fin m} (hm : 0 < m)
    {P : Fin m → Finset (ZMod p)} :
    P ∈ blockIndexFiber S x i ↔
      P ∈ balancedPartitions S ∧ blockIndex S P x = i := by
  unfold blockIndexFiber
  rw [Finset.mem_filter]

/-- A permutation preserving `S`, fixing `x`, and carrying `A` to `B` maps the
partitions whose `x`-block remainder is `A` to those whose remainder is `B`,
without changing the block index of `x`. -/
theorem permute_mem_blockRemainderFiber {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (x : ZMod p) (hm : 0 < m) (hxS : x ∈ S) (i : Fin m)
    (π : Equiv.Perm (ZMod p)) (hπS : S.image π = S) (hπx : π x = x)
    {A B : Finset (ZMod p)} (hAB : A.image π = B)
    {P : Fin m → Finset (ZMod p)}
    (hPmem : P ∈ (blockIndexFiber S x i).filter fun P =>
      pointBlock S P x \ {x} = A) :
    permuteBalancedPartition π P ∈ (blockIndexFiber S x i).filter fun P =>
      pointBlock S P x \ {x} = B := by
  rw [Finset.mem_filter, mem_blockIndexFiber hm] at hPmem ⊢
  obtain ⟨⟨hPb, hidx⟩, hrem⟩ := hPmem
  have hP := mem_balancedPartitions.mp hPb
  refine ⟨⟨mem_balancedPartitions.mpr (permuteBalancedPartition_spec S π hπS hP), ?_⟩, ?_⟩
  · rw [permuteBalancedPartition_blockIndex S x hm hxS π hπS hπx hP, hidx]
  · rw [permute_pointBlock_remainder S x hm hxS π hπS hπx hP, hrem, hAB]

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
  obtain ⟨π, hπA, hπU, hπfix⟩ :=
    exists_perm_maps_finset (S \ {x}) A B
      (Finset.mem_powersetCard.mp hA).1
      (Finset.mem_powersetCard.mp hB).1
      (by rw [(Finset.mem_powersetCard.mp hA).2, (Finset.mem_powersetCard.mp hB).2])
  have hπx : π x = x := hπfix x (by simp)
  have hπS : S.image π = S := by
    have hS : insert x (S \ {x}) = S := by
      rw [Finset.sdiff_singleton_eq_erase]
      exact Finset.insert_erase hxS
    rw [← hS, Finset.image_insert, hπU, hπx]
  have hπS' : S.image π.symm = S := image_symm_eq_of_image_eq π hπS
  have hπx' : π.symm x = x := perm_symm_fixes_of_fixes π hπx
  have hπB : B.image π.symm = A := by
    rw [← hπA, Finset.image_image]
    simp
  apply Finset.card_nbij'
    (fun P => permuteBalancedPartition π P)
    (fun P => permuteBalancedPartition π.symm P)
  · intro P hP
    exact permute_mem_blockRemainderFiber S x hm hxS i π hπS hπx hπA hP
  · intro P hP
    exact permute_mem_blockRemainderFiber S x hm hxS i π.symm hπS' hπx' hπB hP
  · intro P _
    exact permuteBalancedPartition_symm_apply π P
  · intro P _
    exact permuteBalancedPartition_apply_symm π P

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
  have hmap : ∀ P ∈ blockIndexFiber S x i,
      pointBlock S P x \ {x} ∈
        (S \ {x}).powersetCard (balancedBlockSize S.card m i - 1) := by
    intro P hPF
    obtain ⟨hPmem, hidx⟩ := (mem_blockIndexFiber hm).mp hPF
    exact pointBlock_remainder_mem_powerset S x hm hmS
      (mem_balancedPartitions.mp hPmem) hxS i hidx
  obtain ⟨P₀, hP₀⟩ := hfiber
  exact uniformMass_statistic_of_pairwise_equal_fibers
    (blockIndexFiber S x i)
    ((S \ {x}).powersetCard (balancedBlockSize S.card m i - 1))
    (fun P => pointBlock S P x \ {x})
    hmap ⟨_, hmap P₀ hP₀⟩ ⟨P₀, hP₀⟩
    (fun _ hA _ hB => blockRemainder_fiber_equipotent S x hm hmS hxS i hA hB) E

theorem point_block_remainder_lower_real {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (x : ZMod p)
    (hm : 0 < m) (hm4 : m ≤ S.card / 4)
    {P : Fin m → Finset (ZMod p)}
    (hP : IsBalancedPartition S P) (hx : x ∈ S) :
    (S.card : ℝ) / (2 * m) ≤
      ((pointBlock S P x \ {x}).card : ℝ) := by
  have hmS : m ≤ S.card := le_trans hm4 (Nat.div_le_self _ _)
  have hmem : x ∈ pointBlock S P x := mem_blockIndex S P x hm hP hx
  have hcardBlock : S.card / m ≤ (pointBlock S P x).card :=
    (balanced_block_size_bounds S hm hmS hP (blockIndex S P x)).1
  rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hmem]
  have h4m : m * 4 ≤ S.card := (Nat.le_div_iff_mul_le (by norm_num)).mp hm4
  have hq4 : 4 ≤ S.card / m := (Nat.le_div_iff_mul_le hm).2 (by omega)
  have hlt : S.card < (S.card / m + 1) * m := by
    rw [add_one_mul]
    exact Nat.lt_div_mul_add hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hcast : ((S.card / m : ℕ) : ℝ) - 1 ≤
      (((pointBlock S P x).card - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    have : ((S.card / m : ℕ) : ℝ) ≤ ((pointBlock S P x).card : ℝ) := by
      exact_mod_cast hcardBlock
    linarith
  have hltR : (S.card : ℝ) < (((S.card / m : ℕ) : ℝ) + 1) * m := by
    exact_mod_cast hlt
  have hq4R : (4 : ℝ) ≤ ((S.card / m : ℕ) : ℝ) := by exact_mod_cast hq4
  rw [div_le_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right hcast hmR.le,
    mul_le_mul_of_nonneg_right hq4R hmR.le]

/-- Conditioning on the block index of `x`: a bound in the uniform `k`-subset
model, valid for every attainable block index, transfers to the random
balanced partition. -/
theorem partitionMass_remainder_le {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (x : ZMod p) (hx : x ∈ S)
    (hm : 0 < m) (hmS : m ≤ S.card)
    (E : Finset (ZMod p) → Prop) [DecidablePred E] (q : ℝ) (hq : 0 ≤ q)
    (hfib : ∀ i : Fin m, (blockIndexFiber S x i).Nonempty →
      uniformMass ((S \ {x}).powersetCard
        (balancedBlockSize S.card m i - 1)) E ≤ q) :
    partitionMass S (fun P => E (pointBlock S P x \ {x})) ≤ q := by
  have hall := uniformConditionalMass_le_of_fibers
    (balancedPartitions (m := m) S) (fun P => blockIndex S P x) (fun _ => True)
    (fun P => E (pointBlock S P x \ {x})) q hq
    (by
      intro i _
      unfold uniformConditionalMass
      change uniformMass (blockIndexFiber S x i)
        (fun P => E (pointBlock S P x \ {x})) ≤ q
      by_cases hfiber : (blockIndexFiber S x i).Nonempty
      · rw [blockRemainder_conditional_uniform S x hm hmS hx i hfiber E]
        exact hfib i hfiber
      · rw [Finset.not_nonempty_iff_eq_empty.mp hfiber]
        simpa [uniformMass] using hq)
  unfold uniformConditionalMass at hall
  rw [Finset.filter_true_of_mem (fun _ _ => trivial)] at hall
  exact hall

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
  have hmS : m ≤ S.card := le_trans hm4 (Nat.div_le_self _ _)
  apply partitionMass_remainder_le S x hx hm hmS
    (fun T => (T ∩ G).card < S.card / (16 * m)) _ (Real.exp_pos _).le
  intro i hfiber
  obtain ⟨P, hPF⟩ := hfiber
  obtain ⟨hPmem, hidx⟩ := (mem_blockIndexFiber hm).mp hPF
  have hP := mem_balancedPartitions.mp hPmem
  have hrem := pointBlock_remainder_mem_powerset S x hm hmS hP hx i hidx
  set k := balancedBlockSize S.card m i - 1 with hk_def
  have hkcard : (pointBlock S P x \ {x}).card = k :=
    (Finset.mem_powersetCard.mp hrem).2
  have hkU : k ≤ (S \ {x}).card :=
    hkcard ▸ Finset.card_le_card (Finset.mem_powersetCard.mp hrem).1
  have hGU : G ⊆ S \ {x} := by
    intro y hy
    rw [Finset.mem_sdiff, Finset.mem_singleton]
    exact ⟨hGS hy, fun h => hxG (h ▸ hy)⟩
  have hdU : (S \ {x}).card ≤ 4 * G.card :=
    le_trans (Finset.card_le_card Finset.sdiff_subset) hdensity
  have hkNat : S.card / (2 * m) ≤ k :=
    hkcard ▸ point_block_remainder_lower S x hm hm4 hP hx
  have hkReal : (S.card : ℝ) / (2 * m) ≤ k := by
    have := point_block_remainder_lower_real S x hm hm4 hP hx
    rwa [hkcard] at this
  have hthreshold : S.card / (16 * m) ≤ k / 8 := by
    have h16 : S.card / (16 * m) = S.card / (2 * m) / 8 := by
      rw [Nat.div_div_eq_div_mul]
      congr 1
      ring
    rw [h16]
    exact Nat.div_le_div_right hkNat
  calc uniformMass ((S \ {x}).powersetCard k)
        (fun T => (T ∩ G).card < S.card / (16 * m))
      ≤ uniformMass ((S \ {x}).powersetCard k)
          (fun T => (T ∩ G).card < k / 8) :=
        uniformMass_mono _ _ _ (fun T h => lt_of_lt_of_le h hthreshold)
    _ ≤ Real.exp (-(k : ℝ) / 32) :=
        External.hypergeom_quarter_lower_tail _ G k hGU hdU hkU
    _ ≤ Real.exp (-(S.card : ℝ) / (64 * m)) := by
        apply Real.exp_le_exp.mpr
        have h64 : (S.card : ℝ) / (64 * m) = (S.card : ℝ) / (2 * m) / 32 := by
          rw [div_div]
          congr 1
          ring
        rw [neg_div, neg_div, neg_le_neg_iff, h64]
        linarith

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
  have hmS : m ≤ S.card := le_trans hm4 (Nat.div_le_self _ _)
  apply partitionMass_remainder_le S x hx hm hmS
    (fun T => (T ∩ G).card < S.card / (4 * m)) _ (Real.exp_pos _).le
  intro i hfiber
  obtain ⟨P, hPF⟩ := hfiber
  obtain ⟨hPmem, hidx⟩ := (mem_blockIndexFiber hm).mp hPF
  have hP := mem_balancedPartitions.mp hPmem
  have hrem := pointBlock_remainder_mem_powerset S x hm hmS hP hx i hidx
  set k := balancedBlockSize S.card m i - 1 with hk_def
  have hkcard : (pointBlock S P x \ {x}).card = k :=
    (Finset.mem_powersetCard.mp hrem).2
  have hkU : k ≤ (S \ {x}).card :=
    hkcard ▸ Finset.card_le_card (Finset.mem_powersetCard.mp hrem).1
  have hGU : G ⊆ S \ {x} := by
    intro y hy
    rw [Finset.mem_sdiff, Finset.mem_singleton]
    exact ⟨hGS hy, fun h => hxG (h ▸ hy)⟩
  have hdU : 3 * (S \ {x}).card ≤ 4 * G.card := by
    have := Finset.card_le_card (Finset.sdiff_subset (s := S) (t := {x}))
    omega
  have hkNat : S.card / (2 * m) ≤ k :=
    hkcard ▸ point_block_remainder_lower S x hm hm4 hP hx
  have hkReal : (S.card : ℝ) / (2 * m) ≤ k := by
    have := point_block_remainder_lower_real S x hm hm4 hP hx
    rwa [hkcard] at this
  have hthreshold : S.card / (4 * m) ≤ k / 2 := by
    have h4 : S.card / (4 * m) = S.card / (2 * m) / 2 := by
      rw [Nat.div_div_eq_div_mul]
      congr 1
      ring
    rw [h4]
    exact Nat.div_le_div_right hkNat
  calc uniformMass ((S \ {x}).powersetCard k)
        (fun T => (T ∩ G).card < S.card / (4 * m))
      ≤ uniformMass ((S \ {x}).powersetCard k)
          (fun T => (T ∩ G).card < k / 2) :=
        uniformMass_mono _ _ _ (fun T h => lt_of_lt_of_le h hthreshold)
    _ ≤ Real.exp (-(k : ℝ) / 24) :=
        External.hypergeom_three_quarters_lower_tail _ G k hGU hdU hkU
    _ ≤ Real.exp (-(S.card : ℝ) / (48 * m)) := by
        apply Real.exp_le_exp.mpr
        have h48 : (S.card : ℝ) / (48 * m) = (S.card : ℝ) / (2 * m) / 24 := by
          rw [div_div]
          congr 1
          ring
        rw [neg_div, neg_div, neg_le_neg_iff, h48]
        linarith

/-- Fubini for counting a finite family of partition events. -/
theorem partitionExpectation_card_eq_sum_mass {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (E : ZMod p → (Fin m → Finset (ZMod p)) → Prop)
    [∀ χ, DecidablePred (E χ)] :
    partitionExpectation (m := m) S
        (fun P => ((Finset.univ.filter fun χ => E χ P).card : ℝ)) =
      ∑ χ : ZMod p, partitionMass S (E χ) := by
  unfold partitionExpectation partitionMass uniformExpectation uniformMass
  rw [← Finset.sum_div, ← Nat.cast_sum, ← Nat.cast_sum]
  congr 2
  simp only [Finset.card_filter]
  exact Finset.sum_comm

/-- Average indicator bound for a deterministic subset of characters. -/
theorem partitionExpectation_filter_le {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (T : Finset (ZMod p))
    (E : ZMod p → (Fin m → Finset (ZMod p)) → Prop)
    [∀ χ, DecidablePred (E χ)]
    (hbound : ∀ χ ∈ T, partitionMass S (E χ) ≤ 1 / (S.card : ℝ) ^ 9) :
    partitionExpectation (m := m) S
      (fun P => ((T.filter fun χ => E χ P).card : ℝ)) ≤
        (T.card : ℝ) / (S.card : ℝ) ^ 9 := by
  have hrewrite :
      partitionExpectation (m := m) S
          (fun P => ((T.filter fun χ => E χ P).card : ℝ)) =
        ∑ χ ∈ T, partitionMass S (E χ) := by
    unfold partitionExpectation partitionMass uniformExpectation uniformMass
    rw [← Finset.sum_div, ← Nat.cast_sum, ← Nat.cast_sum]
    congr 2
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  rw [hrewrite]
  calc ∑ χ ∈ T, partitionMass S (E χ)
      ≤ ∑ _χ ∈ T, 1 / (S.card : ℝ) ^ 9 := Finset.sum_le_sum hbound
    _ = (T.card : ℝ) / (S.card : ℝ) ^ 9 := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring

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
  unfold uniformExpectation
  rw [Finset.product_eq_sprod, Finset.sum_product, Finset.card_product]
  push_cast
  ring

/-- Averaging over one coordinate extracts a fixed witness with at least the
global average success probability. -/
theorem exists_fiber_mass_ge_pair_mass {α : Type*} [DecidableEq α]
    (S : Finset α) (hS : S.Nonempty) (E : α → α → Prop)
    [DecidablePred fun q : α × α => E q.1 q.2]
    [∀ y, DecidablePred fun x => E x y] :
    ∃ y ∈ S,
      uniformMass S (fun x => E x y) ≥
        uniformMass (S.product S) (fun q => E q.1 q.2) := by
  have hN : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
  have hcount :
      ((S ×ˢ S).filter fun q : α × α => E q.1 q.2).card =
        ∑ y ∈ S, (S.filter fun x => E x y).card := by
    rw [Finset.card_filter, Finset.sum_product, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.card_filter]
  have hsum :
      ∑ _y ∈ S, uniformMass (S.product S) (fun q => E q.1 q.2) =
        ∑ y ∈ S, uniformMass S (fun x => E x y) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    unfold uniformMass
    rw [← Finset.sum_div, Finset.product_eq_sprod, Finset.card_product, hcount]
    push_cast
    field_simp
  obtain ⟨y, hy, hle⟩ := Finset.exists_le_of_sum_le hS hsum.le
  exact ⟨y, hy, hle⟩


end

end GrahamRearrangement.Section3
