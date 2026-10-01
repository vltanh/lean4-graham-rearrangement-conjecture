module

public import GrahamRearrangement.Preliminaries
public import GrahamRearrangement.Probability

@[expose] public section

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Section 3: definitions

Finite sample spaces and deterministic/Fourier quantities used in the proof of
Theorem 1.3.
-/

noncomputable section

/-- Uniform probability mass that a size-`m` subset of `S` has sum `z`. -/
def sliceMass {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (m : ℕ) (z : ZMod p) : ℝ :=
  uniformMass (S.powersetCard m) (fun R => subsetSum R = z)

theorem sliceMass_nonneg {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (z : ZMod p) :
    0 ≤ sliceMass S m z :=
  uniformMass_nonneg _ _

theorem sliceMass_le_one {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (z : ZMod p) :
    sliceMass S m z ≤ 1 :=
  uniformMass_le_one _ _

/-- The balanced size of block `i` when `n` points are split into `m` blocks.
The first `n % m` blocks have size `n / m + 1`; the rest have size `n / m`. -/
def balancedBlockSize (n m : ℕ) (i : Fin m) : ℕ :=
  n / m + if i.val < n % m then 1 else 0

def balancedPrefix (n m i : ℕ) : ℕ :=
  i * (n / m) + min i (n % m)

theorem balancedPrefix_zero (n m : ℕ) :
    balancedPrefix n m 0 = 0 := by
  simp [balancedPrefix]

theorem balancedPrefix_succ {n m i : ℕ}
    (hm : 0 < m) (hi : i < m) :
    balancedPrefix n m (i + 1) - balancedPrefix n m i =
      balancedBlockSize n m ⟨i,hi⟩ := by
  unfold balancedPrefix balancedBlockSize
  dsimp only
  rw [Nat.add_mul, one_mul]
  generalize n / m = q
  generalize n % m = r
  split_ifs with h <;> omega

theorem balancedPrefix_m {n m : ℕ} (hm : 0 < m) :
    balancedPrefix n m m = n := by
  unfold balancedPrefix
  have hmod : n % m < m := Nat.mod_lt n hm
  rw [Nat.min_eq_right (Nat.le_of_lt hmod)]
  exact Nat.div_add_mod n m

theorem balancedPrefix_mono {n m i j : ℕ}
    (hij : i ≤ j) :
    balancedPrefix n m i ≤ balancedPrefix n m j := by
  unfold balancedPrefix
  have h1 := Nat.mul_le_mul_right (n / m) hij
  have h2 := min_le_min_right (n % m) hij
  generalize n / m = q at *
  generalize n % m = r at *
  omega

def balancedBlockIndex (n m j : ℕ) : ℕ :=
  if j < (n % m) * (n / m + 1) then
    j / (n / m + 1)
  else
    n % m +
      (j - (n % m) * (n / m + 1)) / (n / m)

theorem balancedBlockIndex_lt
    (n m : ℕ) (hm : 0 < m) (hmn : m ≤ n)
    (j : ℕ) (hj : j < n) :
    balancedBlockIndex n m j < m := by
  have hq : 0 < n / m := Nat.div_pos hmn hm
  have hr : n % m < m := Nat.mod_lt n hm
  have hn : m * (n / m) + n % m = n := Nat.div_add_mod n m
  unfold balancedBlockIndex
  set q := n / m with hqdef
  set r := n % m with hrdef
  clear_value q r
  split_ifs with hfirst
  · have hdiv : j / (q + 1) < r :=
      (Nat.div_lt_iff_lt_mul (by omega)).2 hfirst
    omega
  · have hrq : r * q < m * q := Nat.mul_lt_mul_of_pos_right hr hq
    have hj2 : j - r * (q + 1) < (m - r) * q := by
      rw [Nat.sub_mul, mul_add_one]
      rw [mul_add_one] at hfirst
      omega
    have hdiv : (j - r * (q + 1)) / q < m - r :=
      (Nat.div_lt_iff_lt_mul hq).2 hj2
    omega

theorem balancedBlockIndex_range
    (n m : ℕ) (hm : 0 < m) (hmn : m ≤ n)
    (j : ℕ) (hj : j < n) :
    balancedPrefix n m (balancedBlockIndex n m j) ≤ j ∧
      j < balancedPrefix n m (balancedBlockIndex n m j + 1) := by
  have hq : 0 < n / m := Nat.div_pos hmn hm
  unfold balancedBlockIndex balancedPrefix
  set q := n / m with hqdef
  set r := n % m with hrdef
  clear_value q r
  split_ifs with hfirst
  · have hi : j / (q + 1) < r := (Nat.div_lt_iff_lt_mul (by omega)).2 hfirst
    have hdm := Nat.div_add_mod' j (q + 1)
    have hmod := Nat.lt_div_mul_add (a := j) (b := q + 1) (by omega)
    set i := j / (q + 1) with hi_def
    clear_value i
    rw [Nat.min_eq_left hi.le, Nat.min_eq_left (by omega : i + 1 ≤ r)]
    rw [mul_add_one] at hdm hmod
    rw [add_one_mul]
    constructor <;> omega
  · have hge : r * (q + 1) ≤ j := Nat.le_of_not_gt hfirst
    have hdm := Nat.div_add_mod' (j - r * (q + 1)) q
    have hmod := Nat.lt_div_mul_add (a := j - r * (q + 1)) hq
    set t := j - r * (q + 1) with ht_def
    set d := t / q with hd_def
    clear_value d t
    rw [Nat.min_eq_right (by omega : r ≤ r + d),
      Nat.min_eq_right (by omega : r ≤ r + d + 1)]
    rw [mul_add_one] at ht_def hge
    simp only [add_mul, one_mul]
    constructor <;> omega

def finSegment (n a b : ℕ) (hb : b ≤ n) : Finset (Fin n) :=
  (Finset.Ico a b).attachFin (fun x hx => lt_of_lt_of_le (Finset.mem_Ico.1 hx).2 hb)

theorem card_finSegment (n a b : ℕ) (hb : b ≤ n) :
    (finSegment n a b hb).card = b - a := by
  unfold finSegment
  rw [Finset.card_attachFin, Nat.card_Ico]

theorem mem_finSegment {n a b : ℕ} {hb : b ≤ n} {i : Fin n} :
    i ∈ finSegment n a b hb ↔ a ≤ i.val ∧ i.val < b := by
  unfold finSegment
  rw [Finset.mem_attachFin, Finset.mem_Ico]

/-- Ordered balanced partitions of `S` into `m` labelled blocks. -/
def IsBalancedPartition {p m : ℕ} (S : Finset (ZMod p))
    (P : Fin m → Finset (ZMod p)) : Prop :=
  (∀ i, P i ⊆ S) ∧
  (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
  (∀ x, x ∈ S ↔ ∃ i, x ∈ P i) ∧
  (∀ i, (P i).card = balancedBlockSize S.card m i)

def canonicalBalancedPartition {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hm : 0 < m) (hmS : m ≤ S.card) :
    Fin m → Finset (ZMod p) := by
  classical
  let e : Fin S.card ≃ {x // x ∈ S} :=
    Fintype.equivOfCardEq (by simp)
  exact fun i =>
    (finSegment S.card
      (balancedPrefix S.card m i.val)
      (balancedPrefix S.card m (i.val + 1))
      (le_trans (balancedPrefix_mono (show i.val + 1 ≤ m by omega))
        (by rw [balancedPrefix_m hm]))).image (fun j => (e j).1)

/-- Any enumeration of `S`, cut into consecutive balanced segments, gives a
balanced partition. -/
theorem isBalancedPartition_image_finSegment {p m : ℕ}
    (S : Finset (ZMod p)) (hm : 0 < m) (hmS : m ≤ S.card)
    (e : Fin S.card ≃ {x // x ∈ S})
    (hb : ∀ i : Fin m, balancedPrefix S.card m (i.val + 1) ≤ S.card) :
    IsBalancedPartition S (fun i : Fin m =>
      (finSegment S.card (balancedPrefix S.card m i.val)
        (balancedPrefix S.card m (i.val + 1)) (hb i)).image
          (fun j => (e j).1)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i x hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hx
    exact (e j).2
  · intro i j hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hxi
    obtain ⟨b, hb', hba⟩ := Finset.mem_image.mp hxj
    have hab : b = a := e.injective (Subtype.ext hba)
    subst hab
    have h1 := mem_finSegment.mp ha
    have h2 := mem_finSegment.mp hb'
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
    · have := balancedPrefix_mono (n := S.card) (m := m)
        (show i.val + 1 ≤ j.val by omega)
      omega
    · have := balancedPrefix_mono (n := S.card) (m := m)
        (show j.val + 1 ≤ i.val by omega)
      omega
  · intro x
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := e.surjective ⟨x, hx⟩
      have hi := balancedBlockIndex_lt S.card m hm hmS j.val j.isLt
      refine ⟨⟨balancedBlockIndex S.card m j.val, hi⟩, ?_⟩
      apply Finset.mem_image.mpr
      refine ⟨j, ?_, by rw [hj]⟩
      apply mem_finSegment.mpr
      exact balancedBlockIndex_range S.card m hm hmS j.val j.isLt
    · rintro ⟨i, hxi⟩
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hxi
      exact (e j).2
  · intro i
    dsimp only
    rw [Finset.card_image_of_injective _
      (fun a b h => e.injective (Subtype.ext h)), card_finSegment]
    exact balancedPrefix_succ hm i.isLt

theorem canonicalBalancedPartition_spec {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hm : 0 < m) (hmS : m ≤ S.card) :
    IsBalancedPartition S (canonicalBalancedPartition S hm hmS) := by
  unfold canonicalBalancedPartition
  exact isBalancedPartition_image_finSegment S hm hmS _ _

/-- The finite sample space of ordered balanced partitions. -/
def balancedPartitions {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) : Finset (Fin m → Finset (ZMod p)) := by
  classical
  exact Finset.univ.filter (IsBalancedPartition S)

/-- The block index containing `x` in a balanced partition; arbitrary outside
well-formed inputs. -/
def blockIndex {p m : ℕ} [NeZero p] (S : Finset (ZMod p))
    (P : Fin m → Finset (ZMod p)) (x : ZMod p) (hm : 0 < m := by assumption) : Fin m := by
  classical
  by_cases hP : IsBalancedPartition S P ∧ x ∈ S
  · have hex : ∃ i : Fin m, x ∈ P i := (hP.1.2.2.1 x).1 hP.2
    exact Classical.choose hex
  · exact ⟨0, hm⟩

theorem mem_blockIndex {p m : ℕ} [NeZero p] (S : Finset (ZMod p))
    (P : Fin m → Finset (ZMod p)) (x : ZMod p)
    (hm : 0 < m) (hP : IsBalancedPartition S P) (hx : x ∈ S) :
    x ∈ P (blockIndex S P x) := by
  classical
  unfold blockIndex
  rw [dite_eq_left ⟨hP, hx⟩]
  exact Classical.choose_spec ((hP.2.2.1 x).1 hx)

theorem blockIndex_eq_of_mem {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    {P : Fin m → Finset (ZMod p)}
    (hm : 0 < m) (hP : IsBalancedPartition S P)
    {x : ZMod p} (hxS : x ∈ S)
    {i : Fin m} (hxi : x ∈ P i) :
    blockIndex S P x = i := by
  have hxChosen := mem_blockIndex S P x hm hP hxS
  by_contra hne
  exact Finset.disjoint_left.mp
    (hP.2.1 (blockIndex S P x) i hne) hxChosen hxi

/-- The block containing a given point. -/
def pointBlock {p m : ℕ} [NeZero p] (S : Finset (ZMod p))
    (P : Fin m → Finset (ZMod p)) (x : ZMod p) (hm : 0 < m := by assumption) :
    Finset (ZMod p) :=
  P (blockIndex S P x hm)

theorem pointBlock_card {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    {P : Fin m → Finset (ZMod p)}
    (hm : 0 < m) (hP : IsBalancedPartition S P)
    {x : ZMod p} (hxS : x ∈ S) :
    (pointBlock S P x).card =
      balancedBlockSize S.card m (blockIndex S P x) := by
  exact hP.2.2.2 (blockIndex S P x)

theorem pointBlock_remainder_mem_powerset {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (x : ZMod p)
    (hm : 0 < m) (hmS : m ≤ S.card)
    {P : Fin m → Finset (ZMod p)}
    (hP : IsBalancedPartition S P) (hxS : x ∈ S)
    (i : Fin m) (hi : blockIndex S P x = i) :
    pointBlock S P x \ {x} ∈
      (S \ {x}).powersetCard
        (balancedBlockSize S.card m i - 1) := by
  have hxBlock : x ∈ pointBlock S P x := mem_blockIndex S P x hm hP hxS
  rw [Finset.mem_powersetCard]
  constructor
  · intro y hy
    rw [Finset.mem_sdiff] at hy ⊢
    exact ⟨hP.1 _ hy.1, hy.2⟩
  · rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hxBlock,
      pointBlock_card S hm hP hxS, hi]

/-- Conditional choices of one point from each block. -/
def blockChoices {p m : ℕ} [NeZero p]
    (P : Fin m → Finset (ZMod p)) : Finset (Fin m → ZMod p) :=
  Fintype.piFinset P

/-- The chosen subset generated by one point from each block. -/
def choiceSet {p m : ℕ} (X : Fin m → ZMod p) : Finset (ZMod p) :=
  Finset.univ.image X

/-- Sum of one point chosen from each block. -/
def choiceSum {p m : ℕ} (X : Fin m → ZMod p) : ZMod p :=
  ∑ i, X i

theorem blockChoices_mem_iff {p m : ℕ} [NeZero p]
    {P : Fin m → Finset (ZMod p)} {X : Fin m → ZMod p} :
    X ∈ blockChoices P ↔ ∀ i, X i ∈ P i := by
  unfold blockChoices
  exact Fintype.mem_piFinset

theorem choice_injective_of_partition {p m : ℕ} [NeZero p]
    {S : Finset (ZMod p)}
    {P : Fin m → Finset (ZMod p)} (hP : IsBalancedPartition S P)
    {X : Fin m → ZMod p} (hX : X ∈ blockChoices P) :
    Function.Injective X := by
  intro i j hij
  by_contra hne
  have hXi : X i ∈ P i := (blockChoices_mem_iff.mp hX) i
  have hXj : X j ∈ P j := (blockChoices_mem_iff.mp hX) j
  exact Finset.disjoint_left.mp (hP.2.1 i j hne) hXi
    (by simpa [hij] using hXj)

theorem choiceSet_card_of_partition {p m : ℕ} [NeZero p]
    {S : Finset (ZMod p)}
    {P : Fin m → Finset (ZMod p)} (hP : IsBalancedPartition S P)
    {X : Fin m → ZMod p} (hX : X ∈ blockChoices P) :
    (choiceSet X).card = m := by
  unfold choiceSet
  rw [Finset.card_image_of_injective _ (choice_injective_of_partition hP hX)]
  simp

theorem choiceSet_subset_of_partition {p m : ℕ} [NeZero p]
    {S : Finset (ZMod p)}
    {P : Fin m → Finset (ZMod p)} (hP : IsBalancedPartition S P)
    {X : Fin m → ZMod p} (hX : X ∈ blockChoices P) :
    choiceSet X ⊆ S := by
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨i,hi,rfl⟩
  exact hP.1 i ((blockChoices_mem_iff.mp hX) i)

theorem choiceSum_eq_subsetSum_choiceSet {p m : ℕ} [NeZero p]
    {S : Finset (ZMod p)}
    {P : Fin m → Finset (ZMod p)} (hP : IsBalancedPartition S P)
    {X : Fin m → ZMod p} (hX : X ∈ blockChoices P) :
    choiceSum X = subsetSum (choiceSet X) := by
  unfold choiceSum subsetSum choiceSet
  rw [Finset.sum_image]
  intro i hi j hj h
  exact choice_injective_of_partition hP hX h

def balancedChoiceMultiplicity (n m : ℕ) : ℕ :=
  ∏ i : Fin m, balancedBlockSize n m i

theorem blockChoices_card {p m : ℕ} [NeZero p]
    (P : Fin m → Finset (ZMod p)) :
    (blockChoices P).card = ∏ i, (P i).card := by
  unfold blockChoices
  exact Fintype.card_piFinset _

theorem blockChoices_card_balanced {p m : ℕ} [NeZero p]
    {S : Finset (ZMod p)} {P : Fin m → Finset (ZMod p)}
    (hP : IsBalancedPartition S P) :
    (blockChoices P).card = balancedChoiceMultiplicity S.card m := by
  rw [blockChoices_card]
  unfold balancedChoiceMultiplicity
  apply Finset.prod_congr rfl
  intro i hi
  exact hP.2.2.2 i

theorem balancedChoiceMultiplicity_pos (n m : ℕ)
    (hm : 0 < m) (hmn : m ≤ n) :
    0 < balancedChoiceMultiplicity n m := by
  unfold balancedChoiceMultiplicity
  apply Finset.prod_pos
  intro i hi
  unfold balancedBlockSize
  have hq : 0 < n / m := Nat.div_pos hmn hm
  split <;> omega

/-- Joint sample space: an ordered balanced partition and one selected point
from each block. -/
def balancedChoiceSpace {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p)) :
    Finset ((Fin m → Finset (ZMod p)) × (Fin m → ZMod p)) := by
  classical
  exact Finset.univ.filter fun q =>
    q.1 ∈ balancedPartitions S ∧ q.2 ∈ blockChoices q.1

theorem mem_balancedChoiceSpace {p m : ℕ} [NeZero p]
    {S : Finset (ZMod p)}
    {P : Fin m → Finset (ZMod p)}
    {X : Fin m → ZMod p} :
    (P,X) ∈ balancedChoiceSpace S ↔
      P ∈ balancedPartitions S ∧ X ∈ blockChoices P := by
  simp [balancedChoiceSpace]

theorem choiceSet_mem_powersetCard {p m : ℕ} [NeZero p]
    {S : Finset (ZMod p)}
    {P : Fin m → Finset (ZMod p)}
    {X : Fin m → ZMod p}
    (h : (P,X) ∈ balancedChoiceSpace S) :
    choiceSet X ∈ S.powersetCard m := by
  rcases mem_balancedChoiceSpace.mp h with ⟨hPmem,hX⟩
  have hP : IsBalancedPartition S P := by
    simpa [balancedPartitions] using hPmem
  exact Finset.mem_powersetCard.mpr
    ⟨choiceSet_subset_of_partition hP hX,
     choiceSet_card_of_partition hP hX⟩

/-- Conditional point mass of the block-choice sum. -/
def conditionalSumMass {p m : ℕ} [NeZero p]
    (P : Fin m → Finset (ZMod p)) (z : ZMod p) : ℝ :=
  uniformMass (blockChoices P) (fun X => choiceSum X = z)

/-- Average over the balanced-partition sample space. -/
def partitionExpectation {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    (F : (Fin m → Finset (ZMod p)) → ℝ) : ℝ :=
  uniformExpectation (balancedPartitions S) F

/-- Probability of an event over the uniformly random balanced partition. -/
def partitionMass {p m : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    (E : (Fin m → Finset (ZMod p)) → Prop)
    [DecidablePred E] : ℝ :=
  uniformMass (balancedPartitions S) E

/-- The paper's random-partition quantity `ψ(χ)`. -/
def psi {p m : ℕ} [NeZero p]
    (P : Fin m → Finset (ZMod p)) (χ : ZMod p) : ℝ :=
  ∑ i,
    (1 / ((P i).card : ℝ) ^ 2) *
      ∑ x ∈ P i, ∑ x' ∈ P i,
        zmodNorm (χ * x - χ * x') ^ 2

/-- The deterministic comparison quantity `Ψ(χ)`. -/
def Psi {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (m : ℕ) (χ : ZMod p) : ℝ :=
  (m : ℝ) / (S.card : ℝ) ^ 2 *
    ∑ x ∈ S, ∑ x' ∈ S,
      zmodNorm (χ * x - χ * x') ^ 2

/-- The dyadic low-`ψ` set `A₀`. -/
def A0 {p m : ℕ} [NeZero p]
    (P : Fin m → Finset (ZMod p)) : Finset (ZMod p) :=
  Finset.univ.filter fun χ => psi P χ < 1

/-- The dyadic shell `A_t={χ:t≤ψ(χ)<2t}`. -/
def At {p m : ℕ} [NeZero p]
    (P : Fin m → Finset (ZMod p)) (t : ℕ) : Finset (ZMod p) :=
  Finset.univ.filter fun χ => (t : ℝ) ≤ psi P χ ∧ psi P χ < 2 * t

/-- The deterministic low-energy set `B_t`. -/
def Bset {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (m t : ℕ) : Finset (ZMod p) :=
  Finset.univ.filter fun χ => Psi S m χ ≤ t

/-- Points of `S` within the `8 sqrt(t/m)` ball about `y` after dilation by `χ`. -/
def nearSet {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (m t : ℕ) (χ y : ZMod p) : Finset (ZMod p) :=
  S.filter fun x =>
    zmodNorm (χ * x - y) ≤ 8 * Real.sqrt ((t : ℝ) / m)

/-- The deterministic structured-character set `D_t`. -/
def Dset {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (m t : ℕ) : Finset (ZMod p) :=
  Finset.univ.filter fun χ =>
    χ ≠ 0 ∧ ∃ y : ZMod p, 3 * S.card ≤ 4 * (nearSet S m t χ y).card

/-- There is some positive scale at which `χ` belongs to `D_t`. -/
def HasDTime {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (m : ℕ) (χ : ZMod p) : Prop :=
  ∃ t : ℕ, 0 < t ∧ χ ∈ Dset S m t

/-- The smallest positive scale at which `χ ∈ D_t`, whenever such a scale
exists. This is the scale used in the paper to choose a center independent of
the later value of `t`. -/
def firstDTime {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (m : ℕ) (χ : ZMod p) : ℕ := by
  classical
  by_cases h : HasDTime S m χ
  · exact Nat.find h
  · exact 1

theorem firstDTime_spec {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (m : ℕ) (χ : ZMod p)
    (h : HasDTime S m χ) :
    0 < firstDTime S m χ ∧
      χ ∈ Dset S m (firstDTime S m χ) := by
  classical
  simp [firstDTime, h, Nat.find_spec h]

theorem firstDTime_le {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (m t : ℕ) (χ : ZMod p)
    (ht : 0 < t) (hχ : χ ∈ Dset S m t) :
    firstDTime S m χ ≤ t := by
  classical
  have hex : HasDTime S m χ := ⟨t, ht, hχ⟩
  simp [firstDTime, hex]
  exact Nat.find_min' hex ⟨ht, hχ⟩

theorem nearSet_mono_t {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (m t₁ t₂ : ℕ)
    (χ y : ZMod p) (htt : t₁ ≤ t₂) :
    nearSet S m t₁ χ y ⊆ nearSet S m t₂ χ y := by
  intro x hx
  simp only [nearSet, Finset.mem_filter] at hx ⊢
  refine ⟨hx.1, le_trans hx.2 ?_⟩
  gcongr

/-- The paper's center `yχ`, chosen once and for all from the smallest positive
scale at which `χ ∈ D_t`. The formal parameter `t` is intentionally ignored,
so the center is definitionally independent of `t`. -/
def centerAt {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (m : ℕ) (_t : ℕ) (χ : ZMod p) : ZMod p := by
  classical
  by_cases h : HasDTime S m χ
  · have hD :
        χ ∈ Dset S m (firstDTime S m χ) :=
      (firstDTime_spec S m χ h).2
    exact Classical.choose
      ((Finset.mem_filter.1 hD).2.2)
  · exact 0

theorem centerAt_independent_of_t {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (m t₁ t₂ : ℕ) (χ : ZMod p) :
    centerAt S m t₁ χ = centerAt S m t₂ χ := by
  rfl

theorem centerAt_spec {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (m t : ℕ) {χ : ZMod p} (ht : 0 < t)
    (hχ : χ ∈ Dset S m t) :
    3 * S.card ≤
      4 * (nearSet S m t χ (centerAt S m t χ)).card := by
  classical
  have hex : HasDTime S m χ := ⟨t, ht, hχ⟩
  have hD :
      χ ∈ Dset S m (firstDTime S m χ) :=
    (firstDTime_spec S m χ hex).2
  have hcenter :
      3 * S.card ≤
        4 * (nearSet S m (firstDTime S m χ) χ
          (centerAt S m t χ)).card := by
    simpa [centerAt, hex] using
      Classical.choose_spec ((Finset.mem_filter.1 hD).2.2)
  have hsubset :
      nearSet S m (firstDTime S m χ) χ (centerAt S m t χ) ⊆
        nearSet S m t χ (centerAt S m t χ) :=
    nearSet_mono_t S m (firstDTime S m χ) t χ
      (centerAt S m t χ) (firstDTime_le S m t χ ht hχ)
  exact le_trans hcenter (Nat.mul_le_mul_left 4 (Finset.card_le_card hsubset))

/-- The enlarged set `J_{χ,t} ⊆ Z_p` used in Lemmas 3.2 and 3.3. -/
def Jset {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (m t : ℕ) (χ : ZMod p) : Finset (ZMod p) :=
  Finset.univ.filter fun x =>
    zmodNorm (χ * x - centerAt S m t χ) ≤
      16 * Real.sqrt ((t : ℝ) / m)

/-- The set `Q_{t,δ}` from Lemma 3.4. -/
def Qset {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (m t : ℕ) (δ : ℝ) : Finset (ZMod p) :=
  Finset.univ.filter fun x =>
    (∑ χ ∈ Bset S m t, zmodNorm (χ * x) ^ 2) <
      δ * (Bset S m t).card

/-- Theorem 1.3 exactly in finite-cardinality probability language. -/
def Theorem13Statement : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (p : ℕ) (hp : p.Prime),
      letI : NeZero p := ⟨hp.ne_zero⟩
      ∀ (S : Finset (ZMod p)), 2 ≤ S.card →
      ∀ (m : ℕ),
        C * Real.log (S.card : ℝ) ≤ (m : ℝ) →
        (m : ℝ) ≤ (1 / 1000 : ℝ) * S.card / Real.log (S.card : ℝ) →
        ∀ z : ZMod p,
          sliceMass S m z ≤
            1 / (p : ℝ) + C / ((S.card : ℝ) * Real.sqrt (m : ℝ))

end

end GrahamRearrangement
