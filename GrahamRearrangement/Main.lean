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
    Section5.indexedOrderings_nonempty S
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
  intro α hα0 hα1
  -- The paper's reduction: the statement for `β = min α (1/4) < 1/2` implies
  -- the statement for `α`, since `p ^ (1 - α) ≤ p ^ (1 - β)`.
  set β : ℝ := min α (1 / 4)
  have hβ0 : 0 < β := lt_min hα0 (by norm_num)
  have hβh : β < 1 / 2 := lt_of_le_of_lt (min_le_right α (1 / 4 : ℝ)) (by norm_num)
  have hβα : β ≤ α := min_le_left α (1 / 4 : ℝ)
  obtain ⟨Cβ, hCβ, hbounds⟩ := hbad β hβ0 hβh
  refine ⟨Cβ, hCβ, ?_⟩
  intro p hp S hzero hC hsize
  have : NeZero p := ⟨hp.ne_zero⟩
  have hpone : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_le
  have hpow : (p : ℝ) ^ (1 - α) ≤ (p : ℝ) ^ (1 - β) :=
    Auxiliary.rpow_exponent_mono_of_one_le hpone (by linarith)
  have hb := hbounds p hp S hzero hC (le_trans hsize hpow)
  have hDpos : 0 < Nat.ceil (3 / β) := section5D_pos hβ0 hβh
  obtain ⟨σ, hσmem, hgood⟩ :=
    exists_section5_good_ordering (D := Nat.ceil (3 / β)) S hb.1 hb.2.1 hb.2.2
  have hσ : IsIndexedOrdering S σ := by
    simpa only [indexedOrderings, Finset.mem_filter, Finset.mem_univ, true_and]
      using hσmem
  obtain ⟨π, -, hnozero⟩ := section5_local_repair hDpos σ hgood
  have hσ' : IsIndexedOrdering S (applyPositionPerm σ π) :=
    applyPositionPerm_isIndexedOrdering hσ π
  exact ⟨indexedToList (applyPositionPerm σ π),
    (valid_iff_noZeroPaperSegments hzero hσ').2 hnozero⟩

/-- Theorem 1.2 of Pham--Sauermann. -/
theorem theorem12 : Theorem12Statement :=
  theorem12_of_section5_bounds section5_bad_event_bounds

end

end GrahamRearrangement
