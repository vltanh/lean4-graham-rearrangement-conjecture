module

public import Mathlib

@[expose] public section

open scoped BigOperators

namespace GrahamRearrangement

/-!
# Finite uniform probability

The paper only uses finite probability spaces.  We keep the core notions as
cardinality ratios so that every random-subset, random-partition, and random-bijection
statement has an explicit finite sample space.
-/

noncomputable section

/-- Uniform probability of an event on a finite sample space. -/
def uniformMass {Ω : Type*} [DecidableEq Ω] (space : Finset Ω)
    (event : Ω → Prop) [DecidablePred event] : ℝ :=
  ((space.filter event).card : ℝ) / (space.card : ℝ)

/-- Uniform expectation of a real-valued function on a finite sample space. -/
def uniformExpectation {Ω : Type*} [DecidableEq Ω] (space : Finset Ω)
    (f : Ω → ℝ) : ℝ :=
  (∑ ω ∈ space, f ω) / (space.card : ℝ)

/-- Conditional uniform mass, obtained by restricting the finite sample space. -/
def uniformConditionalMass {Ω : Type*} [DecidableEq Ω] (space : Finset Ω)
    (cond event : Ω → Prop) [DecidablePred cond] [DecidablePred event] : ℝ :=
  uniformMass (space.filter cond) event

theorem uniformMass_nonneg {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (event : Ω → Prop) [DecidablePred event] :
    0 ≤ uniformMass space event := by
  unfold uniformMass
  positivity

theorem uniformMass_le_one {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (event : Ω → Prop) [DecidablePred event] :
    uniformMass space event ≤ 1 := by
  unfold uniformMass
  by_cases h : space.card = 0
  · simp [h]
  · have hpos : (0 : ℝ) < space.card := by
      exact_mod_cast Nat.pos_of_ne_zero h
    apply (div_le_one hpos).2
    exact_mod_cast Finset.card_filter_le space event

theorem uniformMass_empty_of_forall_not
    {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (E : Ω → Prop) [DecidablePred E]
    (hE : ∀ ω, ¬ E ω) :
    uniformMass space E = 0 := by
  unfold uniformMass
  have hempty : space.filter E = ∅ := by
    ext ω
    simp [hE ω]
  rw [hempty]
  simp

theorem uniformMass_empty {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) :
    uniformMass space (fun _ => False) = 0 := by
  simp [uniformMass]

theorem uniformMass_univ {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (h : space.Nonempty) :
    uniformMass space (fun _ => True) = 1 := by
  simp [uniformMass, h.card_ne_zero]

theorem uniformMass_congr {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (E F : Ω → Prop)
    [DecidablePred E] [DecidablePred F]
    (h : ∀ ω ∈ space, (E ω ↔ F ω)) :
    uniformMass space E = uniformMass space F := by
  unfold uniformMass
  rw [Finset.filter_congr h]

theorem uniformMass_mono_on {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (E F : Ω → Prop)
    [DecidablePred E] [DecidablePred F]
    (hEF : ∀ ω ∈ space, E ω → F ω) :
    uniformMass space E ≤ uniformMass space F := by
  unfold uniformMass
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card (Finset.monotone_filter_right space hEF)

/-- Monotonicity of finite uniform mass. -/
theorem uniformMass_mono {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (E F : Ω → Prop)
    [DecidablePred E] [DecidablePred F]
    (hEF : ∀ ω, E ω → F ω) :
    uniformMass space E ≤ uniformMass space F :=
  uniformMass_mono_on space E F fun ω _ => hEF ω

/-- Finite union bound for two events. -/
theorem uniformMass_or_le_add {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (E F : Ω → Prop)
    [DecidablePred E] [DecidablePred F] :
    uniformMass space (fun ω => E ω ∨ F ω) ≤
      uniformMass space E + uniformMass space F := by
  unfold uniformMass
  rw [← add_div, Finset.filter_or]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_union_le _ _

/-- Finite union bound for an indexed family of events. -/
theorem uniformMass_exists_le_sum {Ω ι : Type*}
    [DecidableEq Ω] [DecidableEq ι]
    (space : Finset Ω) (I : Finset ι) (E : ι → Ω → Prop)
    [∀ i, DecidablePred (E i)] :
    uniformMass space (fun ω => ∃ i ∈ I, E i ω) ≤
      ∑ i ∈ I, uniformMass space (E i) := by
  unfold uniformMass
  rw [← Finset.sum_div]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  have hfilter :
      (space.filter fun ω => ∃ i ∈ I, E i ω) =
        I.biUnion (fun i => space.filter (E i)) := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_biUnion]
    constructor
    · rintro ⟨hω, i, hi, h⟩
      exact ⟨i, hi, hω, h⟩
    · rintro ⟨i, hi, hω, h⟩
      exact ⟨hω, i, hi, h⟩
  rw [hfilter]
  exact_mod_cast Finset.card_biUnion_le

/-- A pointwise bound averages to the same bound over a nonempty uniform space. -/
theorem uniformExpectation_le_const {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (hspace : space.Nonempty)
    (f : Ω → ℝ) (c : ℝ)
    (h : ∀ ω ∈ space, f ω ≤ c) :
    uniformExpectation space f ≤ c := by
  unfold uniformExpectation
  have hsum :
      (∑ ω ∈ space, f ω) ≤ space.card * c := by
    calc
      (∑ ω ∈ space, f ω) ≤ ∑ _ω ∈ space, c := by
        gcongr with ω hω
        exact h ω hω
      _ = space.card * c := by simp [mul_comm]
  have hden : (0 : ℝ) < space.card := by
    exact_mod_cast hspace.card_pos
  apply (div_le_iff₀ hden).2
  simpa [mul_comm] using hsum

theorem powersetCard_nonempty {α : Type*} [DecidableEq α]
    (S : Finset α) {m : ℕ} (hm : m ≤ S.card) :
    (S.powersetCard m).Nonempty := by
  obtain ⟨T, hTS, hcard⟩ := Finset.exists_subset_card_eq hm
  exact ⟨T, Finset.mem_powersetCard.2 ⟨hTS, hcard⟩⟩

theorem mem_powersetCard_card {α : Type*} [DecidableEq α]
    {S R : Finset α} {m : ℕ} (hR : R ∈ S.powersetCard m) :
    R.card = m :=
  (Finset.mem_powersetCard.1 hR).2

theorem card_sdiff_of_mem_powersetCard {α : Type*} [DecidableEq α]
    {S R : Finset α} {m : ℕ} (hR : R ∈ S.powersetCard m) :
    (S \ R).card = S.card - m := by
  rw [Finset.card_sdiff_of_subset (Finset.mem_powersetCard.1 hR).1,
    mem_powersetCard_card hR]

/-- Removing two exceptional events. -/
theorem uniformMass_le_two_exceptions
    {Ω : Type*} [DecidableEq Ω] (space : Finset Ω)
    (E A B : Ω → Prop)
    [DecidablePred E] [DecidablePred A] [DecidablePred B]
    (q : ℝ)
    (hrest :
      uniformMass space (fun ω => E ω ∧ ¬ A ω ∧ ¬ B ω) ≤ q) :
    uniformMass space E ≤ uniformMass space A + uniformMass space B + q := by
  have hmono :
      uniformMass space E ≤
        uniformMass space
          (fun ω => (A ω ∨ B ω) ∨ (E ω ∧ ¬ A ω ∧ ¬ B ω)) := by
    apply uniformMass_mono
    intro ω hE
    by_cases hA : A ω
    · exact Or.inl (Or.inl hA)
    by_cases hB : B ω
    · exact Or.inl (Or.inr hB)
    · exact Or.inr ⟨hE, hA, hB⟩
  have hor1 :=
    uniformMass_or_le_add space
      (fun ω => A ω ∨ B ω)
      (fun ω => E ω ∧ ¬ A ω ∧ ¬ B ω)
  have hor2 := uniformMass_or_le_add space A B
  linarith

/-- If three events have total mass below one in a nonempty finite space, some
outcome avoids all three. -/
theorem exists_avoiding_three_events
    {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (hspace : space.Nonempty)
    (E₁ E₂ E₃ : Ω → Prop)
    [DecidablePred E₁] [DecidablePred E₂] [DecidablePred E₃]
    (a₁ a₂ a₃ : ℝ)
    (h₁ : uniformMass space E₁ ≤ a₁)
    (h₂ : uniformMass space E₂ ≤ a₂)
    (h₃ : uniformMass space E₃ ≤ a₃)
    (hsum : a₁ + a₂ + a₃ < 1) :
    ∃ ω ∈ space, ¬ E₁ ω ∧ ¬ E₂ ω ∧ ¬ E₃ ω := by
  by_contra hnone
  have hcover : ∀ ω ∈ space, (E₁ ω ∨ E₂ ω) ∨ E₃ ω := by
    intro ω hω
    by_contra hc
    exact hnone ⟨ω, hω, fun h => hc (Or.inl (Or.inl h)),
      fun h => hc (Or.inl (Or.inr h)), fun h => hc (Or.inr h)⟩
  have hone :
      (1 : ℝ) ≤ uniformMass space (fun ω => (E₁ ω ∨ E₂ ω) ∨ E₃ ω) := by
    rw [← uniformMass_univ space hspace]
    exact uniformMass_mono_on space _ _ (fun ω hω _ => hcover ω hω)
  have h12 := uniformMass_or_le_add space E₁ E₂
  have h123 := uniformMass_or_le_add space (fun ω => E₁ ω ∨ E₂ ω) E₃
  linarith

theorem log_card_sdiff_le {α : Type*} [DecidableEq α]
    {S R : Finset α} (hne : (S \ R).Nonempty) :
    Real.log ((S \ R).card : ℝ) ≤ Real.log (S.card : ℝ) := by
  apply Real.log_le_log
  · exact_mod_cast hne.card_pos
  · exact_mod_cast Finset.card_le_card Finset.sdiff_subset

theorem card_pi_le_pow {ι α : Type*}
    [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (U : ι → Finset α) (M : ℕ)
    (hU : ∀ i, (U i).card ≤ M) :
    (Finset.univ.pi U).card ≤ M ^ Fintype.card ι := by
  classical
  rw [Finset.card_pi]
  calc
    (∏ i : ι, (U i).card) ≤ ∏ _i : ι, M := by
      gcongr with i
      exact hU i
    _ = M ^ Fintype.card ι := by simp

theorem card_product_le_mul {α β : Type*}
    [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β)
    (a b : ℕ) (hA : A.card ≤ a) (hB : B.card ≤ b) :
    (A.product B).card ≤ a * b := by
  have h : (A.product B).card = A.card * B.card := Finset.card_product A B
  rw [h]
  exact Nat.mul_le_mul hA hB

theorem card_eq_sum_card_fibers {α β : Type*}
    [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (f : α → β)
    (hmap : ∀ a ∈ A, f a ∈ B) :
    A.card = ∑ b ∈ B, (A.filter fun a => f a = b).card :=
  Finset.card_eq_sum_card_fiberwise fun a ha => hmap a ha

theorem uniformMass_bij
    {Ω Γ : Type*} [DecidableEq Ω] [DecidableEq Γ]
    (A : Finset Ω) (B : Finset Γ)
    (f : Ω → Γ)
    (hmem : ∀ ω ∈ A, f ω ∈ B)
    (hinj : Set.InjOn f A)
    (hsurj : ∀ γ ∈ B, ∃ ω ∈ A, f ω = γ)
    (E : Ω → Prop) (F : Γ → Prop)
    [DecidablePred E] [DecidablePred F]
    (hevent : ∀ ω ∈ A, E ω ↔ F (f ω)) :
    uniformMass A E = uniformMass B F := by
  unfold uniformMass
  have hcard : A.card = B.card := by
    apply Finset.card_nbij f
    · intro ω hω
      exact hmem ω (Finset.mem_coe.1 hω)
    · exact hinj
    · intro γ hγ
      obtain ⟨ω, hω, rfl⟩ := hsurj γ (Finset.mem_coe.1 hγ)
      exact ⟨ω, Finset.mem_coe.2 hω, rfl⟩
  have hecard : (A.filter E).card = (B.filter F).card := by
    apply Finset.card_nbij f
    · intro ω hω
      rw [Finset.mem_coe, Finset.mem_filter] at hω ⊢
      exact ⟨hmem ω hω.1, (hevent ω hω.1).1 hω.2⟩
    · intro ω hω ω' hω' h
      exact hinj (Finset.mem_coe.2 (Finset.mem_filter.1 (Finset.mem_coe.1 hω)).1)
        (Finset.mem_coe.2 (Finset.mem_filter.1 (Finset.mem_coe.1 hω')).1) h
    · intro γ hγ
      rw [Finset.mem_coe, Finset.mem_filter] at hγ
      obtain ⟨ω, hω, rfl⟩ := hsurj γ hγ.1
      exact ⟨ω, Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hω, (hevent ω hω).2 hγ.2⟩), rfl⟩
  rw [hcard, hecard]

theorem uniformMass_chain_rule
    {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω)
    (A B : Ω → Prop) [DecidablePred A] [DecidablePred B] :
    uniformMass space (fun ω => A ω ∧ B ω) =
      uniformMass space A *
        uniformConditionalMass space A B := by
  unfold uniformConditionalMass uniformMass
  rw [Finset.filter_filter]
  by_cases hA : (space.filter A).card = 0
  · have h0 : (space.filter fun ω => A ω ∧ B ω).card = 0 := by
      have hle : (space.filter fun ω => A ω ∧ B ω).card ≤ (space.filter A).card :=
        Finset.card_le_card (Finset.monotone_filter_right space fun _ _ h => h.1)
      omega
    simp [hA, h0]
  · have hApos : ((space.filter A).card : ℝ) ≠ 0 := by exact_mod_cast hA
    field_simp

/-- Cardinal form of an upper bound on uniform mass. -/
theorem card_filter_le_of_uniformMass_le {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (E : Ω → Prop) [DecidablePred E]
    (q : ℝ) (h : uniformMass space E ≤ q) :
    ((space.filter E).card : ℝ) ≤ q * space.card := by
  rcases Nat.eq_zero_or_pos space.card with h0 | hpos
  · have hle := Finset.card_filter_le space E
    have h0' : (space.filter E).card = 0 := by omega
    simp [h0, h0']
  · unfold uniformMass at h
    have hpos' : (0 : ℝ) < space.card := by exact_mod_cast hpos
    rwa [div_le_iff₀ hpos'] at h

/-- A conditional bound that holds on every fiber of a finite statistic also
holds after conditioning on any union of such fibers. -/
theorem uniformConditionalMass_le_of_fibers
    {Ω K : Type*} [DecidableEq Ω] [DecidableEq K]
    (space : Finset Ω) (key : Ω → K)
    (P : K → Prop) (B : Ω → Prop)
    [DecidablePred P] [DecidablePred B]
    (q : ℝ) (hq : 0 ≤ q)
    (hfiber :
      ∀ κ, P κ →
        uniformConditionalMass space (fun ω => key ω = κ) B ≤ q) :
    uniformConditionalMass space
      (fun ω => P (key ω)) B ≤ q := by
  unfold uniformConditionalMass
  set SP := space.filter (fun ω => P (key ω)) with hSP
  set Ks := SP.image key with hKs
  have hPK : ∀ κ ∈ Ks, P κ := by
    intro κ hκ
    obtain ⟨ω, hω, rfl⟩ := Finset.mem_image.1 hκ
    exact (Finset.mem_filter.1 hω).2
  have hden : SP.card = ∑ κ ∈ Ks, (space.filter fun ω => key ω = κ).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := key) (t := Ks)
      (fun ω hω => Finset.mem_image_of_mem key hω)]
    apply Finset.sum_congr rfl
    intro κ hκ
    congr 1
    ext ω
    simp only [hSP, Finset.mem_filter]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      exact ⟨⟨h1, h3 ▸ hPK κ hκ⟩, h3⟩
  have hnum : (SP.filter B).card =
      ∑ κ ∈ Ks, ((space.filter fun ω => key ω = κ).filter B).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := key) (t := Ks)
      (fun ω hω => Finset.mem_image_of_mem key (Finset.mem_filter.1 hω).1)]
    apply Finset.sum_congr rfl
    intro κ hκ
    congr 1
    ext ω
    simp only [hSP, Finset.mem_filter]
    constructor
    · rintro ⟨⟨⟨h1, _⟩, h2⟩, h3⟩
      exact ⟨⟨h1, h3⟩, h2⟩
    · rintro ⟨⟨h1, h3⟩, h2⟩
      exact ⟨⟨⟨h1, h3 ▸ hPK κ hκ⟩, h2⟩, h3⟩
  have hle : ((SP.filter B).card : ℝ) ≤ q * SP.card := by
    rw [hnum, hden]
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro κ hκ
    exact card_filter_le_of_uniformMass_le (space.filter fun ω => key ω = κ) B q
      (hfiber κ (hPK κ hκ))
  unfold uniformMass
  rcases Nat.eq_zero_or_pos SP.card with h0 | hpos
  · rw [h0, Nat.cast_zero, div_zero]
    exact hq
  · rw [div_le_iff₀ (by exact_mod_cast hpos)]
    exact hle

/-- An injective self-map sending a finite set into a set of no larger cardinality
maps it onto that set. -/
theorem perm_image_eq_of_mapsTo {α : Type*} [DecidableEq α]
    (π : Equiv.Perm α) {S T : Finset α} (hmaps : ∀ x ∈ S, π x ∈ T)
    (hcard : T.card ≤ S.card) :
    S.image π = T := by
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    exact hmaps x hx
  · rw [Finset.card_image_of_injective _ π.injective]
    exact hcard

/-- Equal-size subsets of a finite ground set can be carried to one another by
a permutation preserving the ground set and fixing its complement. -/
theorem exists_perm_maps_finset
    {α : Type*} [Fintype α] [DecidableEq α]
    (S A B : Finset α) (hAS : A ⊆ S) (hBS : B ⊆ S)
    (hcard : A.card = B.card) :
    ∃ π : Equiv.Perm α,
      A.image π = B ∧ S.image π = S ∧
      ∀ x ∉ S, π x = x := by
  have e₀ : {x // x ∈ A} ≃ {x // x ∈ B} :=
    Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_coe, hcard])
  let e : {y : {x // x ∈ S} // y.1 ∈ A} ≃ {y : {x // x ∈ S} // y.1 ∈ B} :=
    (Equiv.subtypeSubtypeEquivSubtype (p := fun x => x ∈ S) (q := fun x => x ∈ A)
        (fun h => hAS h)).trans
      (e₀.trans (Equiv.subtypeSubtypeEquivSubtype (p := fun x => x ∈ S)
        (q := fun x => x ∈ B) (fun h => hBS h)).symm)
  let τ : Equiv.Perm {x // x ∈ S} := e.extendSubtype
  let π : Equiv.Perm α := Equiv.Perm.ofSubtype τ
  have hπS : ∀ x (hx : x ∈ S), π x = (τ ⟨x, hx⟩ : α) := fun x hx =>
    Equiv.Perm.ofSubtype_apply_of_mem τ hx
  refine ⟨π, ?_, ?_, fun x hx => Equiv.Perm.ofSubtype_apply_of_not_mem τ hx⟩
  · apply perm_image_eq_of_mapsTo π _ hcard.symm.le
    intro x hx
    rw [hπS x (hAS hx)]
    exact Equiv.extendSubtype_mem e ⟨x, hAS hx⟩ hx
  · apply perm_image_eq_of_mapsTo π _ le_rfl
    intro x hx
    rw [hπS x hx]
    exact (τ ⟨x, hx⟩).2

-- `hvalues` is not needed for the proof but is part of the public statement.
set_option linter.unusedVariables false in
/-- A finite statistic with constant nonzero fiber cardinality is uniformly
distributed on its finite range. -/
theorem uniformMass_statistic_of_equal_fibers
    {Ω Γ : Type*} [DecidableEq Ω] [DecidableEq Γ]
    (space : Finset Ω) (values : Finset Γ)
    (f : Ω → Γ)
    (hmap : ∀ ω ∈ space, f ω ∈ values)
    (hvalues : values.Nonempty)
    (c : ℕ) (hc : 0 < c)
    (hfiber :
      ∀ γ ∈ values,
        (space.filter fun ω => f ω = γ).card = c)
    (E : Γ → Prop) [DecidablePred E] :
    uniformMass space (fun ω => E (f ω)) =
      uniformMass values E := by
  unfold uniformMass
  have hspaceCard : space.card = values.card * c := by
    rw [card_eq_sum_card_fibers space values f hmap]
    exact Finset.sum_const_nat hfiber
  have heventCard :
      (space.filter fun ω => E (f ω)).card = (values.filter E).card * c := by
    rw [card_eq_sum_card_fibers (space.filter fun ω => E (f ω)) (values.filter E) f
      (by
        intro ω hω
        rw [Finset.mem_filter] at hω ⊢
        exact ⟨hmap ω hω.1, hω.2⟩)]
    apply Finset.sum_const_nat
    intro γ hγ
    rw [Finset.mem_filter] at hγ
    rw [← hfiber γ hγ.1]
    congr 1
    ext ω
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      exact ⟨⟨h1, h3 ▸ hγ.2⟩, h3⟩
  rw [hspaceCard, heventCard]
  push_cast
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [mul_div_mul_right _ _ hc']

/-- Equal-fiber uniformity without choosing the common cardinality explicitly. -/
theorem uniformMass_statistic_of_pairwise_equal_fibers
    {Ω Γ : Type*} [DecidableEq Ω] [DecidableEq Γ]
    (space : Finset Ω) (values : Finset Γ)
    (f : Ω → Γ)
    (hmap : ∀ ω ∈ space, f ω ∈ values)
    (hvalues : values.Nonempty)
    (hspace : space.Nonempty)
    (heq :
      ∀ γ ∈ values, ∀ γ' ∈ values,
        (space.filter fun ω => f ω = γ).card =
          (space.filter fun ω => f ω = γ').card)
    (E : Γ → Prop) [DecidablePred E] :
    uniformMass space (fun ω => E (f ω)) =
      uniformMass values E := by
  obtain ⟨γ₀, hγ₀⟩ := hvalues
  have hcfiber :
      ∀ γ ∈ values,
        (space.filter fun ω => f ω = γ).card =
          (space.filter fun ω => f ω = γ₀).card :=
    fun γ hγ => heq γ hγ γ₀ hγ₀
  have hc : 0 < (space.filter fun ω => f ω = γ₀).card := by
    rcases Nat.eq_zero_or_pos (space.filter fun ω => f ω = γ₀).card with h0 | h0
    · exfalso
      have hcard := card_eq_sum_card_fibers space values f hmap
      rw [Finset.sum_const_nat (m := 0) (fun γ hγ => (hcfiber γ hγ).trans h0)] at hcard
      exact hspace.card_ne_zero (by simpa using hcard)
    · exact h0
  exact uniformMass_statistic_of_equal_fibers space values f hmap ⟨γ₀, hγ₀⟩
    _ hc hcfiber E

theorem card_biUnion_of_pairwise_disjoint
    {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (I : Finset ι) (A : ι → Finset α)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (A i) (A j)) :
    (I.biUnion A).card = ∑ i ∈ I, (A i).card := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
      have hdi :
          Disjoint (A i) (I.biUnion A) := by
        rw [Finset.disjoint_biUnion_right]
        intro j hj
        exact hdisj i (by simp) j (by simp [hj])
          (by intro h; subst j; exact hi hj)
      rw [Finset.biUnion_insert, Finset.card_union_of_disjoint hdi,
        ih (by
          intro a ha b hb hab
          exact hdisj a (by simp [ha]) b (by simp [hb]) hab)]
      simp [hi]

theorem finset_image_injective_of_injective
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    {f : α → β} (hf : Function.Injective f) :
    Function.Injective (fun A : Finset α => A.image f) :=
  Finset.image_injective hf

theorem card_biUnion_le_sum
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (I : Finset α) (A : α → Finset β) :
    (I.biUnion A).card ≤ ∑ i ∈ I, (A i).card := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
      rw [Finset.biUnion_insert]
      calc
        (A i ∪ I.biUnion A).card
          ≤ (A i).card + (I.biUnion A).card :=
            Finset.card_union_le _ _
        _ ≤ (A i).card + ∑ j ∈ I, (A j).card := by omega
        _ = ∑ j ∈ insert i I, (A j).card := by simp [hi]

theorem list_prod_eq_finset_prod_of_nodup
    {ι M : Type*} [DecidableEq ι] [CommMonoid M]
    (L : List ι) (hL : L.Nodup) (f : ι → M) :
    (L.map f).prod = ∏ i ∈ L.toFinset, f i := by
  induction L with
  | nil => simp
  | cons a L ih =>
      have ha : a ∉ L := (List.nodup_cons.mp hL).1
      have hLn : L.Nodup := (List.nodup_cons.mp hL).2
      rw [List.map_cons, List.prod_cons, ih hLn]
      simp [ha]

theorem perm_symm_fixes_of_fixes {α : Type*}
    (π : Equiv.Perm α) {x : α} (h : π x = x) :
    π.symm x = x := by
  apply π.injective
  simp [h]

theorem exists_injective_fin_enum
    {α : Type*} [DecidableEq α]
    (T : Finset α) (D : ℕ) (hD : D ≤ T.card) :
    ∃ f : Fin D → α,
      Function.Injective f ∧ ∀ i, f i ∈ T := by
  classical
  obtain ⟨U,hUT,hcard⟩ := Finset.exists_subset_card_eq hD
  let e : Fin D ≃ {x // x ∈ U} :=
    Fintype.equivOfCardEq (by simp [hcard])
  refine ⟨fun i => (e i).1, ?_, ?_⟩
  · intro i j h
    exact e.injective (Subtype.ext h)
  · intro i
    exact hUT (e i).2

theorem exists_perm_maps_nested_family
    {α : Type*} [Fintype α] [DecidableEq α]
    (T : Finset α) :
    ∀ (k : ℕ)
      (R R' : Fin k → Finset α),
      (∀ i, R i ⊆ T) →
      (∀ i, R' i ⊆ T) →
      (∀ i j, i ≤ j → R i ⊆ R j) →
      (∀ i j, i ≤ j → R' i ⊆ R' j) →
      (∀ i, (R i).card = (R' i).card) →
      ∃ π : Equiv.Perm α,
        T.image π = T ∧
        (∀ i, (R i).image π = R' i) ∧
        ∀ x ∉ T, π x = x := by
  intro k
  induction k generalizing T with
  | zero =>
      intro R R' _ _ _ _ _
      refine ⟨Equiv.refl α, ?_, fun i => i.elim0, fun x _ => rfl⟩
      simp
  | succ k ih =>
      intro R R' hR hR' hn hn' hc
      obtain ⟨π₁, hπ₁last, hπ₁T, hπ₁out⟩ :=
        exists_perm_maps_finset T (R (Fin.last k)) (R' (Fin.last k))
          (hR _) (hR' _) (hc _)
      obtain ⟨π₂, hπ₂T, hπ₂R, hπ₂out⟩ :=
        ih (R' (Fin.last k))
          (fun i => (R i.castSucc).image π₁) (fun i => R' i.castSucc)
          (fun i => by
            rw [← hπ₁last]
            exact Finset.image_subset_image (hn _ _ (Fin.le_last _)))
          (fun i => hn' _ _ (Fin.le_last _))
          (fun i j hij => Finset.image_subset_image
            (hn _ _ (Fin.castSucc_le_castSucc_iff.2 hij)))
          (fun i j hij => hn' _ _ (Fin.castSucc_le_castSucc_iff.2 hij))
          (fun i => by
            rw [Finset.card_image_of_injective _ π₁.injective]
            exact hc _)
      have himage :
          ∀ X : Finset α, X.image (π₁.trans π₂) = (X.image π₁).image π₂ := by
        intro X
        rw [Equiv.coe_trans, Finset.image_image]
      refine ⟨π₁.trans π₂, ?_, ?_, ?_⟩
      · rw [himage, hπ₁T]
        apply perm_image_eq_of_mapsTo π₂ _ le_rfl
        intro x hx
        by_cases hxR : x ∈ R' (Fin.last k)
        · have hmem : π₂ x ∈ (R' (Fin.last k)).image π₂ :=
            Finset.mem_image_of_mem _ hxR
          rw [hπ₂T] at hmem
          exact hR' _ hmem
        · rw [hπ₂out x hxR]
          exact hx
      · intro i
        induction i using Fin.lastCases with
        | last =>
            rw [himage, hπ₁last, hπ₂T]
        | cast j =>
            rw [himage]
            exact hπ₂R j
      · intro x hx
        have hxR : x ∉ R' (Fin.last k) := fun h => hx (hR' _ h)
        rw [Equiv.trans_apply, hπ₁out x hx, hπ₂out x hxR]

/-- An event and its complement have total mass one on a nonempty space. -/
theorem uniformMass_compl_eq_one {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (hspace : space.Nonempty)
    (E : Ω → Prop) [DecidablePred E] :
    uniformMass space E + uniformMass space (fun ω => ¬ E ω) = 1 := by
  unfold uniformMass
  rw [← add_div, div_eq_one_iff_eq (by exact_mod_cast hspace.card_ne_zero)]
  exact_mod_cast Finset.card_filter_add_card_filter_not E

/-- Cardinal form of a lower bound on uniform mass. -/
theorem card_filter_ge_of_uniformMass_ge {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (hspace : space.Nonempty)
    (E : Ω → Prop) [DecidablePred E] (c : ℝ)
    (h : c ≤ uniformMass space E) :
    c * space.card ≤ (space.filter E).card := by
  unfold uniformMass at h
  have hcard : (0 : ℝ) < space.card := by
    exact_mod_cast hspace.card_pos
  apply (le_div_iff₀ hcard).1
  simpa [mul_comm] using h

/-- Uniform probability of a singleton in a nonempty finite space. -/
theorem uniformMass_eq_singleton {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (ω : Ω) (hω : ω ∈ space) :
    uniformMass space (fun x => x = ω) = 1 / (space.card : ℝ) := by
  unfold uniformMass
  rw [Finset.filter_eq' space ω]
  simp [hω]

/-- Monotonicity of uniform expectation. -/
theorem uniformExpectation_mono {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (f g : Ω → ℝ)
    (hfg : ∀ ω ∈ space, f ω ≤ g ω) :
    uniformExpectation space f ≤ uniformExpectation space g := by
  unfold uniformExpectation
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  exact Finset.sum_le_sum hfg

theorem uniformExpectation_strictMono {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (hspace : space.Nonempty)
    (f g : Ω → ℝ)
    (hfg : ∀ ω ∈ space, f ω < g ω) :
    uniformExpectation space f < uniformExpectation space g := by
  unfold uniformExpectation
  exact div_lt_div_of_pos_right (Finset.sum_lt_sum_of_nonempty hspace hfg)
    (by exact_mod_cast hspace.card_pos)

theorem uniformExpectation_add {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (f g : Ω → ℝ) :
    uniformExpectation space (fun ω => f ω + g ω) =
      uniformExpectation space f + uniformExpectation space g := by
  unfold uniformExpectation
  rw [Finset.sum_add_distrib]
  ring

theorem uniformExpectation_smul {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (c : ℝ) (f : Ω → ℝ) :
    uniformExpectation space (fun ω => c * f ω) =
      c * uniformExpectation space f := by
  unfold uniformExpectation
  rw [← Finset.mul_sum]
  ring

/-- Average of a constant over a nonempty finite space. -/
theorem uniformExpectation_const {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (h : space.Nonempty) (c : ℝ) :
    uniformExpectation space (fun _ => c) = c := by
  simp [uniformExpectation, h.card_ne_zero]

/-- The indicator expectation equals the corresponding uniform mass. -/
theorem uniformExpectation_indicator {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (E : Ω → Prop) [DecidablePred E] :
    uniformExpectation space (fun ω => if E ω then 1 else 0) =
      uniformMass space E := by
  classical
  unfold uniformExpectation uniformMass
  congr 1
  simp [Finset.sum_boole]

end

end GrahamRearrangement
