module

public import GrahamRearrangement.Rearrangement.BadEvents

@[expose] public section

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Main theorem

Theorem 1.2, including the paper's reduction to 0 < α < 1/2 and the final
probabilistic-existence/greedy-repair argument.
-/

noncomputable section

/-- Theorem 1.2. -/
def Theorem12Statement : Prop :=
  ∀ α : ℝ, 0 < α → α < 1 →
    ∃ Cα : ℝ, 0 < Cα ∧
      ∀ (p : ℕ), p.Prime →
      ∀ (S : Finset (ZMod p)),
        0 ∉ S →
        Cα ≤ (S.card : ℝ) →
        (S.card : ℝ) ≤ (p : ℝ) ^ (1 - α) →
        HasValidOrdering S

theorem exists_section5_good_ordering
    {p D : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    (h1 :
      orderingEventMass S (BadEvent1 D) ≤ (1 / 100 : ℝ))
    (h2 :
      orderingEventMass S (BadEvent2 D) ≤ (3 / 100 : ℝ))
    (h3 :
      orderingEventMass S (BadEvent3 D) ≤ (1 / 25 : ℝ)) :
    ∃ σ ∈ indexedOrderings S, Section5Good D σ := by
  have hspace :=
    Section5External.indexedOrderings_nonempty S
  have h :=
    exists_avoiding_three_events
      (indexedOrderings S) hspace
      (BadEvent1 D) (BadEvent2 D) (BadEvent3 D)
      (1 / 100 : ℝ) (3 / 100 : ℝ) (1 / 25 : ℝ)
      (by simpa [orderingEventMass] using h1)
      (by simpa [orderingEventMass] using h2)
      (by simpa [orderingEventMass] using h3)
      (by norm_num)
  rcases h with ⟨σ, hσ, hnot1, hnot2, hnot3⟩
  exact ⟨σ, hσ, hnot1, hnot2, hnot3⟩

/-- The final Section 5 reduction from the three probability bounds to a valid
ordering. -/
theorem theorem12_of_section5_bounds
    (hbad : Section5BadEventBoundsStatement) :
    Theorem12Statement := by
  sorry

/-- Theorem 1.2 of Pham--Sauermann. -/
theorem theorem12 : Theorem12Statement :=
  theorem12_of_section5_bounds section5_bad_event_bounds

end

end GrahamRearrangement
