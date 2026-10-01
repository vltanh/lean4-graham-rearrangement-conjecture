module

public import GrahamRearrangement.BooleanSlice.Lemmas

@[expose] public section

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Section 3: proof of Theorem 1.3

This file combines Lemmas 3.1--3.7 with the dyadic Fourier reduction.
-/

noncomputable section

def lowPsiNonzero {p m : ℕ} [NeZero p]
    (P : Fin m → Finset (ZMod p)) (t : ℕ) : Finset (ZMod p) :=
  Finset.univ.filter fun χ => χ ≠ 0 ∧ psi P χ < 2 * t

theorem lowPsi_partition {p m t : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (P : Fin m → Finset (ZMod p)) :
    (lowPsiNonzero P t).card ≤
      (((Finset.univ.erase (0 : ZMod p)) \ Dset S m t).filter
        (fun χ => psi P χ < 2 * t)).card +
      ((Dset S m t \ Bset S m (2000 * t)).filter
        (fun χ => psi P χ < 2 * t)).card +
      (Bset S m (2000 * t) \ {0}).card := by
  sorry

/-- Expected number of nonzero characters with ψ(χ)<2t.  This is the estimate
immediately preceding the bounds for A₀ and A_t in the proof of Theorem 1.3. -/
theorem expected_lowPsi_bound {p m t : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hS : 2 ≤ S.card)
    (hmLower : (2 ^ 24 : ℝ) * Real.log (S.card : ℝ) ≤ m)
    (hmUpper : (m : ℝ) ≤
      (1 / 1000 : ℝ) * S.card / Real.log (S.card : ℝ))
    (ht : 0 < t) (htsmall : t ≤ m / (2000 ^ 2)) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    partitionExpectation (m := m) S
        (fun P => ((lowPsiNonzero P t).card : ℝ)) ≤
      (10 ^ 4 : ℝ) * p * Real.sqrt t /
        ((S.card : ℝ) * Real.sqrt m) := by
  sorry

theorem expected_A0_bound {p m : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hS : 2 ≤ S.card)
    (hmLower : (2 ^ 24 : ℝ) * Real.log (S.card : ℝ) ≤ m)
    (hmUpper : (m : ℝ) ≤
      (1 / 1000 : ℝ) * S.card / Real.log (S.card : ℝ)) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    partitionExpectation (m := m) S (fun P => ((A0 P).card : ℝ)) ≤
      1 + (10 ^ 4 : ℝ) * p /
        ((S.card : ℝ) * Real.sqrt m) := by
  sorry

theorem expected_At_bound {p m t : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hS : 2 ≤ S.card)
    (hmLower : (2 ^ 24 : ℝ) * Real.log (S.card : ℝ) ≤ m)
    (hmUpper : (m : ℝ) ≤
      (1 / 1000 : ℝ) * S.card / Real.log (S.card : ℝ))
    (ht : 0 < t) (htsmall : t ≤ m / 2 ^ 22) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    partitionExpectation (m := m) S (fun P => ((At P t).card : ℝ)) ≤
      (10 ^ 4 : ℝ) * p * Real.sqrt t /
        ((S.card : ℝ) * Real.sqrt m) := by
  sorry

theorem expected_At_trivial {p m t : ℕ} [NeZero p]
    (S : Finset (ZMod p)) :
    partitionExpectation (m := m) S (fun P => ((At P t).card : ℝ)) ≤ p := by
  sorry

/-- Theorem 1.3 with the paper's explicit choice C=2^24. -/
theorem theorem13_explicit :
    ∀ (p : ℕ) (hp : p.Prime),
      letI : NeZero p := ⟨hp.ne_zero⟩
      ∀ (S : Finset (ZMod p)), 2 ≤ S.card →
      ∀ (m : ℕ),
        (2 ^ 24 : ℝ) * Real.log (S.card : ℝ) ≤ (m : ℝ) →
        (m : ℝ) ≤ (1 / 1000 : ℝ) * S.card /
          Real.log (S.card : ℝ) →
        ∀ z : ZMod p,
          sliceMass S m z ≤
            1 / (p : ℝ) +
              (2 ^ 24 : ℝ) /
                ((S.card : ℝ) * Real.sqrt (m : ℝ)) := by
  sorry

/-- Theorem 1.3. -/
theorem theorem13 : Theorem13Statement := by
  refine ⟨(2 ^ 24 : ℝ), by norm_num, ?_⟩
  intro p hp
  letI : NeZero p := ⟨hp.ne_zero⟩
  intro S hS m hmLower hmUpper z
  exact theorem13_explicit p hp S hS m hmLower hmUpper z

end

end GrahamRearrangement
