module

public import GrahamRearrangement.Rearrangement.External

@[expose] public section

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Lemma 5.1
-/

noncomputable section

def leftEndpointCandidates {n : ℕ} (b : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun a =>
    2 ≤ paperPos a ∧ paperPos a < paperPos b

def nearRightEnd {n : ℕ} (D : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun b => n ≤ paperPos b + 30 * D

theorem card_near_right_end_le {n D : ℕ} :
    (nearRightEnd (n := n) D).card ≤ 30 * D + 1 := by
  sorry

theorem badEndpoint_event_subset {n p : ℕ}
    (σ : Fin n → ZMod p) (b : Fin n) :
    b ∈ badRightEndpoints σ →
      ∃ a ∈ leftEndpointCandidates b,
        indexedIntervalSum σ a b = 0 := by
  intro hb
  rcases (mem_badRightEndpoints_iff σ b).1 hb with ⟨a, ha2, hab, hsum⟩
  exact ⟨a, by simp [leftEndpointCandidates, ha2, hab], hsum⟩

theorem fixed_interval_sum_mass {p : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    (a b : Fin S.card) (hab : a.val ≤ b.val) :
    orderingEventMass S (fun σ => indexedIntervalSum σ a b = 0) =
      sliceMass S (b.val - a.val + 1) 0 := by
  sorry

theorem endpoint_cor42_sum_bound {α : ℝ}
    (hα0 : 0 < α) (hαh : α < 1 / 2)
    (P : Section5Parameters α)
    {p : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hreg : Section5Regime P p S)
    (b : Fin S.card) :
    ∑ a ∈ leftEndpointCandidates b,
      ((1 / (p : ℝ) +
        chainConstant 1 * Real.sqrt (Real.log (S.card : ℝ)) /
          ((S.card : ℝ) *
            Real.sqrt ((b.val - a.val + 1 : ℕ) : ℝ))) +
       (1 / (p : ℝ) +
        chainConstant 1 * Real.sqrt (Real.log (S.card : ℝ)) /
          ((S.card : ℝ) *
            Real.sqrt ((S.card - (b.val - a.val + 1) : ℕ) : ℝ)))) ≤
      2 * (S.card : ℝ) / p +
        4 * chainConstant 1 *
          Real.sqrt (Real.log (S.card : ℝ)) /
            Real.sqrt (S.card : ℝ) := by
  sorry

theorem fixed_badEndpoint_mass_le_three {α : ℝ}
    (hα0 : 0 < α) (hαh : α < 1 / 2)
    (P : Section5Parameters α)
    {p : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hreg : Section5Regime P p S)
    (b : Fin S.card) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    orderingEventMass S (fun σ => b ∈ badRightEndpoints σ) ≤
      3 * (S.card : ℝ) ^ (-α) := by
  sorry

/-- Lemma 5.1. -/
theorem lemma5_1 {α : ℝ}
    (hα0 : 0 < α) (hαh : α < 1 / 2)
    (P : Section5Parameters α)
    {p : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hreg : Section5Regime P p S) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    orderingEventMass S (BadEvent1 P.D) ≤ 1 / 100 := by
  sorry

end

end GrahamRearrangement
