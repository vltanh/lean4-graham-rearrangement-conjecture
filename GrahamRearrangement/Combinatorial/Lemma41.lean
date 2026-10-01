module

public import GrahamRearrangement.Combinatorial.External

@[expose] public section

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Lemma 4.1
-/

noncomputable section

theorem one_point_sum_event_card_le_one {p : ℕ} [NeZero p]
    (R U : Finset (ZMod p)) (hdisj : Disjoint R U)
    (z : ZMod p) :
    (U.filter fun x => subsetSum (insert x R) = z).card ≤ 1 := by
  sorry

theorem one_point_sum_mass_le {p : ℕ} [NeZero p]
    (R U : Finset (ZMod p)) (hU : U.Nonempty)
    (hdisj : Disjoint R U) (z : ZMod p) :
    uniformMass U (fun x => subsetSum (insert x R) = z) ≤
      1 / (U.card : ℝ) := by
  unfold uniformMass
  have hcard := one_point_sum_event_card_le_one R U hdisj z
  have hUpos : (0 : ℝ) < U.card := by
    exact_mod_cast hU.card_pos
  apply (div_le_div_iff_of_pos_right hUpos).2
  exact_mod_cast hcard

/-- Lemma 4.1. -/
theorem lemma4_1 {p m : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hm : 0 < m) (hmS : m ≤ S.card)
    (z : ZMod p) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    sliceMass S m z ≤ 1 / ((S.card - m + 1 : ℕ) : ℝ) := by
  sorry

/-- The max_z formulation stated in the paper. -/
theorem lemma4_1_max {p m : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hm : 0 < m) (hmS : m ≤ S.card) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    ∀ z : ZMod p,
      sliceMass S m z ≤ 1 / ((S.card - m + 1 : ℕ) : ℝ) := by
  intro z
  exact lemma4_1 hp S hm hmS z

end

end GrahamRearrangement
