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
  sorry

/-- Monotonicity of finite uniform mass. -/
theorem uniformMass_mono {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (E F : Ω → Prop)
    [DecidablePred E] [DecidablePred F]
    (hEF : ∀ ω, E ω → F ω) :
    uniformMass space E ≤ uniformMass space F := by
  sorry

theorem uniformMass_mono_on {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (E F : Ω → Prop)
    [DecidablePred E] [DecidablePred F]
    (hEF : ∀ ω ∈ space, E ω → F ω) :
    uniformMass space E ≤ uniformMass space F := by
  sorry

/-- Finite union bound for an indexed family of events. -/
theorem uniformMass_exists_le_sum {Ω ι : Type*}
    [DecidableEq Ω] [DecidableEq ι]
    (space : Finset Ω) (I : Finset ι) (E : ι → Ω → Prop)
    [∀ i, DecidablePred (E i)] :
    uniformMass space (fun ω => ∃ i ∈ I, E i ω) ≤
      ∑ i ∈ I, uniformMass space (E i) := by
  sorry

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
  sorry

/-- Removing two exceptional events. -/
theorem uniformMass_le_two_exceptions
    {Ω : Type*} [DecidableEq Ω] (space : Finset Ω)
    (E A B : Ω → Prop)
    [DecidablePred E] [DecidablePred A] [DecidablePred B]
    (q : ℝ)
    (hrest :
      uniformMass space (fun ω => E ω ∧ ¬ A ω ∧ ¬ B ω) ≤ q) :
    uniformMass space E ≤ uniformMass space A + uniformMass space B + q := by
  sorry

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
  sorry

theorem log_card_sdiff_le {α : Type*} [DecidableEq α]
    {S R : Finset α} (hne : (S \ R).Nonempty) :
    Real.log ((S \ R).card : ℝ) ≤ Real.log (S.card : ℝ) := by
  sorry

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
  sorry

theorem card_eq_sum_card_fibers {α β : Type*}
    [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (f : α → β)
    (hmap : ∀ a ∈ A, f a ∈ B) :
    A.card = ∑ b ∈ B, (A.filter fun a => f a = b).card := by
  sorry

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
  sorry

theorem uniformMass_chain_rule
    {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω)
    (A B : Ω → Prop) [DecidablePred A] [DecidablePred B] :
    uniformMass space (fun ω => A ω ∧ B ω) =
      uniformMass space A *
        uniformConditionalMass space A B := by
  sorry

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
  sorry

/-- Equal-size subsets of a finite ground set can be carried to one another by
a permutation preserving the ground set and fixing its complement. -/
theorem exists_perm_maps_finset
    {α : Type*} [Fintype α] [DecidableEq α]
    (S A B : Finset α) (hAS : A ⊆ S) (hBS : B ⊆ S)
    (hcard : A.card = B.card) :
    ∃ π : Equiv.Perm α,
      A.image π = B ∧ S.image π = S ∧
      ∀ x ∉ S, π x = x := by
  sorry

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
  sorry

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
  sorry

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
    Function.Injective (fun A : Finset α => A.image f) := by
  sorry

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
    Fintype.equivOfCardEq (by simpa [hcard])
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
  sorry

/-- Finite union bound for two events. -/
theorem uniformMass_or_le_add {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (E F : Ω → Prop)
    [DecidablePred E] [DecidablePred F] :
    uniformMass space (fun ω => E ω ∨ F ω) ≤
      uniformMass space E + uniformMass space F := by
  sorry

/-- An event and its complement have total mass one on a nonempty space. -/
theorem uniformMass_compl_eq_one {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (hspace : space.Nonempty)
    (E : Ω → Prop) [DecidablePred E] :
    uniformMass space E + uniformMass space (fun ω => ¬ E ω) = 1 := by
  sorry

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
  sorry

/-- Monotonicity of uniform expectation. -/
theorem uniformExpectation_mono {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (f g : Ω → ℝ)
    (hfg : ∀ ω ∈ space, f ω ≤ g ω) :
    uniformExpectation space f ≤ uniformExpectation space g := by
  sorry

theorem uniformExpectation_strictMono {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (hspace : space.Nonempty)
    (f g : Ω → ℝ)
    (hfg : ∀ ω ∈ space, f ω < g ω) :
    uniformExpectation space f < uniformExpectation space g := by
  sorry

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
  simpa [Finset.sum_boole]

end

end GrahamRearrangement
