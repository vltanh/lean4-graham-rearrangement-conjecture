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
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [Finset.mem_filter] at ha hb
  have haR : a ∉ R := Finset.disjoint_right.mp hdisj ha.1
  have hbR : b ∉ R := Finset.disjoint_right.mp hdisj hb.1
  rw [subsetSum_insert R a haR] at ha
  rw [subsetSum_insert R b hbR] at hb
  exact add_right_cancel (ha.2.trans hb.2.symm)

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
  let _ : NeZero p := ⟨hp.ne_zero⟩
  show sliceMass S m z ≤ 1 / ((S.card - m + 1 : ℕ) : ℝ)
  unfold sliceMass
  rw [Section4External.uniformSubset_twoStage S m hm hmS]
  apply uniformExpectation_le_const _ (powersetCard_nonempty S (by omega))
  intro R hR
  rw [Finset.mem_powersetCard] at hR
  have hcard : (S \ R).card = S.card - m + 1 := by
    rw [Finset.card_sdiff_of_subset hR.1, hR.2]
    omega
  have hne : (S \ R).Nonempty := by
    rw [← Finset.card_pos, hcard]
    omega
  calc
    uniformMass (S \ R) (fun x => subsetSum (insert x R) = z)
      ≤ 1 / ((S \ R).card : ℝ) :=
        one_point_sum_mass_le R (S \ R) hne Finset.disjoint_sdiff z
    _ = 1 / ((S.card - m + 1 : ℕ) : ℝ) := by rw [hcard]

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
