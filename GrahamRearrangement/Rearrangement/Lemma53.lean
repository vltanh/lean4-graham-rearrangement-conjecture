module

public import GrahamRearrangement.Rearrangement.Lemma56

@[expose] public section

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Lemma 5.3

The blocked-choice event is split into the right-extending event E₁ and the
left-extending event E₂, bounded by Lemmas 5.5 and 5.6 respectively.
-/

noncomputable section

theorem swap_fixedOutside
    {n : ℕ} (b b' y : Fin n)
    (hby : paperPos b < paperPos y)
    (hyb' : paperPos y ≤ paperPos b') :
    FixedOutside b b' (Equiv.swap b y) := by
  intro i hi
  have hib : i ≠ b := by
    intro h
    subst h
    rcases hi with h | h <;> omega
  have hiy : i ≠ y := by
    intro h
    subst h
    rcases hi with h | h <;> omega
  exact Equiv.swap_apply_of_ne_of_ne hib hiy

/-- Failure of B₀ says that the subset-sum map is injective on the local
5D-window even after applying any admissible permutation fixing the prefix.
This is the precise local-injectivity statement used in the proof of Lemma 5.3. -/
theorem local_subset_sum_injective_after_admissible
    {n p D : ℕ}
    (σ : Fin n → ZMod p) (b : Fin n)
    (hb : b ∈ badRightEndpoints σ)
    (hbfar : paperPos b + 30 * D ≤ n)
    (h0 : ¬ BadEvent0 D σ)
    (π : Equiv.Perm (Fin n))
    (hadm : IsAdmissiblePermutation D π)
    (hfix : FixedBelow b π)
    {J J' : Finset (Fin n)}
    (hJ : J ⊆ forwardWindow b (5 * D))
    (hJ' : J' ⊆ forwardWindow b (5 * D))
    (hne : J ≠ J') :
    indexSetSum (applyPositionPerm σ π) J ≠
      indexSetSum (applyPositionPerm σ π) J' := by
  sorry

theorem local_nonzero_after_admissible
    {n p D : ℕ}
    (σ : Fin n → ZMod p) (b : Fin n)
    (hb : b ∈ badRightEndpoints σ)
    (hbfar : paperPos b + 30 * D ≤ n)
    (h0 : ¬ BadEvent0 D σ)
    (π : Equiv.Perm (Fin n))
    (hadm : IsAdmissiblePermutation D π)
    (hfix : FixedBelow b π)
    {J : Finset (Fin n)}
    (hJne : J.Nonempty)
    (hJ : J ⊆ forwardWindow b (5 * D)) :
    indexSetSum (applyPositionPerm σ π) J ≠ 0 := by
  sorry

def RightBlockedWitness {n p D : ℕ}
    (σ : Fin n → ZMod p) (b : Fin n)
    (π : Equiv.Perm (Fin n)) (y : Fin n) : Prop :=
  ∃ s t : Fin n,
    paperPos b < paperPos s ∧ paperPos s ≤ paperPos y ∧
    paperPos b + 5 * D < paperPos t ∧
    indexedIntervalSum
      (applyPositionPerm (applyPositionPerm σ π) (Equiv.swap b y))
      s t = 0

def LeftBlockedWitness {n p D : ℕ}
    (σ : Fin n → ZMod p) (b : Fin n)
    (π : Equiv.Perm (Fin n)) (y : Fin n) : Prop :=
  ∃ s t : Fin n,
    paperPos s < paperPos b ∧
    paperPos b ≤ paperPos t ∧ paperPos t < paperPos y ∧
    indexedIntervalSum
      (applyPositionPerm (applyPositionPerm σ π) (Equiv.swap b y))
      s t = 0

/-- This is the dichotomy in the first paragraph of the proof of Lemma 5.3:
a blocked interval cannot be wholly contained in the 5D-window, so it must
extend to the right or to the left. -/
theorem blocked_witness_has_side
    {n p D : ℕ}
    (σ : Fin n → ZMod p) (b : Fin n)
    (hb : b ∈ badRightEndpoints σ)
    (hbfar : paperPos b + 30 * D ≤ n)
    (h0 : ¬ BadEvent0 D σ)
    (π : Equiv.Perm (Fin n))
    (hadm : IsAdmissiblePermutation D π)
    (hfix : FixedBelow b π)
    {y : Fin n} (hy : y ∈ blockedCandidates D σ b π) :
    RightBlockedWitness (D := D) σ b π y ∨
      LeftBlockedWitness (D := D) σ b π y := by
  sorry

/-- At the pigeonhole stage only the blocked choices y_i are known to be
distinct. Distinctness of the far endpoints is proved separately below, just
as in the paper. -/
theorem blocked_family_side_split
    {n p D : ℕ} (hD : 0 < D)
    (σ : Fin n → ZMod p) (b : Fin n)
    (hb : b ∈ badRightEndpoints σ)
    (hbfar : paperPos b + 30 * D ≤ n)
    (h0 : ¬ BadEvent0 D σ)
    (π : Equiv.Perm (Fin n))
    (hadm : IsAdmissiblePermutation D π)
    (hfix : FixedBelow b π)
    (hblocked :
      2 * D ≤ (blockedCandidates D σ b π).card) :
    (∃ y : Fin D → Fin n,
      Function.Injective y ∧
      ∀ i, y i ∈ blockedCandidates D σ b π ∧
        RightBlockedWitness (D := D) σ b π (y i)) ∨
    (∃ y : Fin D → Fin n,
      Function.Injective y ∧
      ∀ i, y i ∈ blockedCandidates D σ b π ∧
        LeftBlockedWitness (D := D) σ b π (y i)) := by
  sorry

/-- The distinctness argument for the right endpoints t_i in E₁, exactly as
on pp. 25--26 of the paper. -/
theorem right_witness_endpoints_injective
    {n p D : ℕ}
    (σ : Fin n → ZMod p) (b b' : Fin n)
    (hgap : paperPos b' - paperPos b = 5 * D)
    (hb : b ∈ badRightEndpoints σ)
    (hbfar : paperPos b + 30 * D ≤ n)
    (h0 : ¬ BadEvent0 D σ)
    (π : Equiv.Perm (Fin n))
    (hadm : IsAdmissiblePermutation D π)
    (hfix : FixedBelow b π)
    (y s t : Fin D → Fin n)
    (hyinj : Function.Injective y)
    (hw : ∀ i,
      paperPos b < paperPos (y i) ∧
      paperPos (y i) ≤ paperPos b' ∧
      paperPos b < paperPos (s i) ∧
      paperPos (s i) ≤ paperPos (y i) ∧
      paperPos b' < paperPos (t i) ∧
      indexedIntervalSum
        (applyPositionPerm
          (applyPositionPerm σ π) (Equiv.swap b (y i)))
        (s i) (t i) = 0) :
    Function.Injective t := by
  sorry

/-- The analogous distinctness argument for the left endpoints s_i in E₂. -/
theorem left_witness_endpoints_injective
    {n p D : ℕ}
    (σ : Fin n → ZMod p) (b b' : Fin n)
    (hgap : paperPos b' - paperPos b = 5 * D)
    (hb : b ∈ badRightEndpoints σ)
    (hbfar : paperPos b + 30 * D ≤ n)
    (h0 : ¬ BadEvent0 D σ)
    (π : Equiv.Perm (Fin n))
    (hadm : IsAdmissiblePermutation D π)
    (hfix : FixedBelow b π)
    (y s t : Fin D → Fin n)
    (hyinj : Function.Injective y)
    (hw : ∀ i,
      paperPos b < paperPos (y i) ∧
      paperPos (y i) ≤ paperPos b' ∧
      paperPos (s i) < paperPos b ∧
      paperPos b ≤ paperPos (t i) ∧
      paperPos (t i) < paperPos (y i) ∧
      indexedIntervalSum
        (applyPositionPerm
          (applyPositionPerm σ π) (Equiv.swap b (y i)))
        (s i) (t i) = 0) :
    Function.Injective s := by
  sorry

theorem badEvent3_core_side_reduction
    {n p D : ℕ} (hD : 0 < D)
    (σ : Fin n → ZMod p)
    (h3 : BadEvent3 D σ)
    (h0 : ¬ BadEvent0 D σ)
    (h1 : ¬ BadEvent1 D σ) :
    RightRepairEvent D σ ∨ LeftRepairEvent D σ := by
  sorry

def rightRepairAtom {n p D : ℕ}
    (θ : RepairParams n D) (σ : Fin n → ZMod p) : Prop :=
  Lemma55Event σ θ.b θ.b' θ.u
    (fun i => Equiv.swap θ.b (θ.y i))

def leftRepairAtom {n p D : ℕ}
    (θ : RepairParams n D) (σ : Fin n → ZMod p) : Prop :=
  Lemma56Event σ θ.b θ.b' θ.u
    (fun i => Equiv.swap θ.b (θ.y i))

theorem rightRepairEvent_mass
    {α : ℝ} (hα0 : 0 < α) (hαh : α < 1 / 2)
    (P : Section5Parameters α)
    {p : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hreg : Section5Regime P p S) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    orderingEventMass S (RightRepairEvent P.D) ≤
      (1 / 100 : ℝ) := by
  sorry

theorem leftRepairEvent_mass
    {α : ℝ} (hα0 : 0 < α) (hαh : α < 1 / 2)
    (P : Section5Parameters α)
    {p : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hreg : Section5Regime P p S) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    orderingEventMass S (LeftRepairEvent P.D) ≤
      (1 / 100 : ℝ) := by
  sorry

/-- Lemma 5.3. -/
theorem lemma5_3
    {α : ℝ} (hα0 : 0 < α) (hαh : α < 1 / 2)
    (P : Section5Parameters α)
    {p : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hreg : Section5Regime P p S) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    orderingEventMass S (BadEvent3 P.D) ≤
      (1 / 25 : ℝ) := by
  sorry

end

end GrahamRearrangement
