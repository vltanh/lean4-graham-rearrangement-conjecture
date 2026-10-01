module

public import GrahamRearrangement.BooleanSlice.Fourier

@[expose] public section

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Section 3: concentration and deterministic low-spectrum lemmas

Lemmas 3.1--3.7 and the proof of Lemma 3.4.
-/

noncomputable section

/-- The set of points farther than the Lemma 3.1 threshold from `χx'`. -/
def farSet {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (m t : ℕ) (χ x' : ZMod p) : Finset (ZMod p) :=
  S.filter fun x =>
    8 * Real.sqrt ((t : ℝ) / m) <
      zmodNorm (χ * x - χ * x')

theorem near_far_card {p m t : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (χ x' : ZMod p) :
    (nearSet S m t χ (χ * x')).card +
      (farSet S m t χ x').card = S.card := by
  classical
  have hdisj :
      Disjoint (nearSet S m t χ (χ * x')) (farSet S m t χ x') := by
    rw [Finset.disjoint_left]
    intro x hnear hfar
    have hn := (Finset.mem_filter.1 hnear).2
    have hf := (Finset.mem_filter.1 hfar).2
    linarith
  have hunion :
      nearSet S m t χ (χ * x') ∪ farSet S m t χ x' = S := by
    ext x
    simp only [nearSet, farSet, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩)
      · exact hx
      · exact hx
    · intro hx
      by_cases hle :
          zmodNorm (χ * x - χ * x') ≤
            8 * Real.sqrt ((t : ℝ) / m)
      · exact Or.inl ⟨hx, hle⟩
      · exact Or.inr ⟨hx, lt_of_not_ge hle⟩
  rw [← Finset.card_union_of_disjoint hdisj, hunion]

/-- If χ is not in D_t, every translate χx' has at least a quarter of S outside
the radius-8 ball. -/
theorem farSet_quarter {p m t : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (χ : ZMod p)
    (hχ0 : χ ≠ 0) (hχD : χ ∉ Dset S m t)
    {x' : ZMod p} (hx' : x' ∈ S) :
    S.card ≤ 4 * (farSet S m t χ x').card := by
  sorry

/-- Section 3 range implies the elementary bounds used by the random partition. -/
theorem section3_basic_bounds (SCard m : ℕ)
    (hS : 2 ≤ SCard)
    (hlower : (2 ^ 24 : ℝ) * Real.log (SCard : ℝ) ≤ m)
    (hupper : (m : ℝ) ≤
      (1 / 1000 : ℝ) * SCard / Real.log (SCard : ℝ)) :
    0 < m ∧ m ≤ SCard / 4 ∧ 10 ^ 7 ≤ SCard := by
  sorry

/-- The numerical exponential tail comparison used in Lemmas 3.1 and 3.3. -/
theorem section3_tail_nine (SCard m : ℕ)
    (hS : 2 ≤ SCard)
    (hmUpper : (m : ℝ) ≤
      (1 / 1000 : ℝ) * SCard / Real.log (SCard : ℝ))
    (c : ℝ) (hc : c ≤ 100) :
    (SCard : ℝ) * Real.exp (-(SCard : ℝ) / (c * m)) ≤
      1 / (SCard : ℝ) ^ 9 := by
  sorry

/-- Deterministic implication used in Lemma 3.1: if every point sees enough far
points in its own block, then ψ(χ)≥2t. -/
theorem psi_ge_two_of_far_rows {p m t : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hS : 2 ≤ S.card)
    (hm : 0 < m) (hm4 : m ≤ S.card / 4)
    {P : Fin m → Finset (ZMod p)} (hP : IsBalancedPartition S P)
    (χ : ZMod p)
    (hrow : ∀ x' ∈ S,
      S.card / (16 * m) ≤
        ((pointBlock S P x' \ {x'}) ∩ farSet S m t χ x').card) :
    (2 : ℝ) * t ≤ psi P χ := by
  sorry

/-- Lemma 3.1. -/
theorem lemma3_1 {p m t : ℕ} [NeZero p] (hp : p.Prime)
    (S : Finset (ZMod p)) (hS : 2 ≤ S.card)
    (hmLower : (2 ^ 24 : ℝ) * Real.log (S.card : ℝ) ≤ m)
    (hmUpper : (m : ℝ) ≤
      (1 / 1000 : ℝ) * S.card / Real.log (S.card : ℝ))
    (ht : 0 < t) (χ : ZMod p) (hχ0 : χ ≠ 0)
    (hχD : χ ∉ Dset S m t) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    partitionMass (m := m) S (fun P => psi P χ < 2 * t) ≤
      1 / (S.card : ℝ) ^ 9 := by
  sorry

/-- Lemma 3.2. -/
theorem lemma3_2 {p m t : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hm : 0 < m) (ht : 0 < t)
    (χ : ZMod p) (hχD : χ ∈ Dset S m t)
    (hχB : χ ∉ Bset S m (2000 * t)) :
    (200 : ℝ) * t / m * S.card ≤
      ∑ x ∈ S \ Jset S m t χ,
        zmodNorm (χ * x - centerAt S m t χ) ^ 2 := by
  sorry

/-- Deterministic implication used in Lemma 3.3. -/
theorem psi_ge_five_of_dense_rows {p m t : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hS : 2 ≤ S.card)
    (hm : 0 < m) (hm4 : m ≤ S.card / 4)
    {P : Fin m → Finset (ZMod p)} (hP : IsBalancedPartition S P)
    (χ : ZMod p) (hχD : χ ∈ Dset S m t)
    (hχB : χ ∉ Bset S m (2000 * t))
    (hrow : ∀ x ∈ S \ Jset S m t χ,
      S.card / (4 * m) ≤
        ((pointBlock S P x \ {x}) ∩
          nearSet S m t χ (centerAt S m t χ)).card) :
    (5 : ℝ) * t ≤ psi P χ := by
  sorry

/-- Lemma 3.3. -/
theorem lemma3_3 {p m t : ℕ} [NeZero p] (hp : p.Prime)
    (S : Finset (ZMod p)) (hS : 2 ≤ S.card)
    (hmLower : (2 ^ 24 : ℝ) * Real.log (S.card : ℝ) ≤ m)
    (hmUpper : (m : ℝ) ≤
      (1 / 1000 : ℝ) * S.card / Real.log (S.card : ℝ))
    (ht : 0 < t) (χ : ZMod p)
    (hχD : χ ∈ Dset S m t)
    (hχB : χ ∉ Bset S m (2000 * t)) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    partitionMass (m := m) S (fun P => psi P χ < 2 * t) ≤
      1 / (S.card : ℝ) ^ 9 := by
  sorry

/-- Lemma 3.5. -/
theorem lemma3_5 {p m t : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hS : S.Nonempty)
    (hm : 0 < m) (ht : 0 < t) :
    (9 : ℝ) / 10 * S.card ≤ (Qset S m t (10 * t / m)).card := by
  sorry

/-- The low-energy set is symmetric and contains zero. -/
theorem Bset_zero_neg {p m t : ℕ} [NeZero p]
    (S : Finset (ZMod p)) :
    (0 : ZMod p) ∈ Bset S m t ∧
      ∀ χ ∈ Bset S m t, -χ ∈ Bset S m t := by
  sorry

theorem character_sum_real_of_neg_symmetric
    {p : ℕ} [NeZero p]
    (B : Finset (ZMod p))
    (hsymm : ∀ χ ∈ B, -χ ∈ B)
    (x : ZMod p) :
    ((∑ χ ∈ B, ZMod.stdAddChar (χ * x)) : ℂ).im = 0 := by
  sorry

theorem symmetric_character_square_sum
    {p : ℕ} (hp : p.Prime)
    (B : Finset (ZMod p)) (hzero : 0 ∈ B)
    (hsymm : ∀ χ ∈ B, -χ ∈ B) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    ∑ x : ZMod p,
      ((∑ χ ∈ B, ZMod.stdAddChar (χ * x)).re) ^ 2 =
        (p : ℝ) * B.card := by
  sorry

/-- Lemma 3.6. -/
theorem lemma3_6 {p m t : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    ((Qset S m t (1 / 200)).card : ℝ) ≤
      (5 : ℝ) / 4 * p / (Bset S m t).card := by
  sorry

theorem Qset_mono_delta {p m t : ℕ} [NeZero p]
    (S : Finset (ZMod p)) {δ₁ δ₂ : ℝ} (hδ : δ₁ ≤ δ₂) :
    Qset S m t δ₁ ⊆ Qset S m t δ₂ := by
  intro x hx
  have hx' := (Finset.mem_filter.1 hx).2
  apply Finset.mem_filter.2
  refine ⟨Finset.mem_univ _, ?_⟩
  have hB : 0 ≤ ((Bset S m t).card : ℝ) := by positivity
  nlinarith

theorem finset_list_sum_comm {ι α : Type*} [DecidableEq ι]
    [AddCommMonoid α] (s : Finset ι) (xs : List α)
    (f : ι → α → α) :
    (∑ i ∈ s, (xs.map fun x => f i x).sum) =
      (xs.map fun x => ∑ i ∈ s, f i x).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp [ih, Finset.sum_add_distrib]

/-- Lemma 3.7. -/
theorem lemma3_7 {p m t k : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (δ : ℝ)
    (hk : 0 < k) (hδ : 0 < δ) :
    kfoldSumset (Qset S m t δ) k ⊆
      Qset S m t ((k : ℝ) ^ 2 * δ) := by
  sorry

/-- Lemma 3.4. -/
theorem lemma3_4 {p m t : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hSbig : 10 ^ 7 ≤ S.card)
    (hm : 0 < m) (ht : 0 < t) (htm : t ≤ m / 2000) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    ((Bset S m t).card : ℝ) ≤
      1 + 200 * p * Real.sqrt t /
        ((S.card : ℝ) * Real.sqrt m) := by
  sorry

end

end GrahamRearrangement
