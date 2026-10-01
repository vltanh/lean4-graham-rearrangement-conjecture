module

public import GrahamRearrangement.External.Hypergeometric.Hoeffding

@[expose] public section

open scoped BigOperators

namespace GrahamRearrangement.External.Hypergeometric

/-!
# Hypergeometric lower tails

The generic without-replacement Hoeffding inequality is transferred from the
sequential sampler to uniform fixed-cardinality subsets, then specialized to
the two constants used by Pham--Sauermann.
-/

noncomputable section

theorem withoutReplacementMass_success_to_subset
    {α : Type*} [DecidableEq α]
    (U G : Finset α) (k : ℕ) (hk : k ≤ U.card)
    (E : ℕ → Prop) [DecidablePred E] :
    withoutReplacementMass U k (fun xs => E (successCount G xs)) =
      uniformMass (U.powersetCard k)
        (fun T => E ((T ∩ G).card)) := by
  calc
    withoutReplacementMass U k (fun xs => E (successCount G xs))
      = withoutReplacementMass U k
          (fun xs => E ((xs.toFinset ∩ G).card)) := by
            apply withoutReplacementMass_congr_on_samples
            intro xs hxs
            rw [successCount_eq_card_toFinset G hxs.2.1]
    _ = uniformMass (U.powersetCard k)
          (fun T => E ((T ∩ G).card)) :=
        withoutReplacementMass_toFinset U k hk
          (fun T => E ((T ∩ G).card))

theorem hypergeomMean_eq_of_subset
    {α : Type*} [DecidableEq α]
    {U G : Finset α} (hGU : G ⊆ U)
    {k : ℕ} (hU : U.Nonempty) :
    hypergeomMean U G k =
      (k : ℝ) * (G.card : ℝ) / (U.card : ℝ) := by
  rw [hypergeomMean_of_nonempty hU,
    Finset.inter_eq_right.mpr hGU]

/-- Hoeffding lower tail for a uniformly random k-subset. -/
theorem uniformSubset_hoeffding_lower_tail
    {α : Type*} [DecidableEq α]
    (U G : Finset α) (k : ℕ) (hk : k ≤ U.card)
    (d : ℝ) (hd : 0 ≤ d) :
    uniformMass (U.powersetCard k)
      (fun T =>
        ((T ∩ G).card : ℝ) ≤ hypergeomMean U G k - d) ≤
      if k = 0 then 1 else Real.exp (-2 * d ^ 2 / k) := by
  rw [← withoutReplacementMass_success_to_subset
    U G k hk
    (fun r => (r : ℝ) ≤ hypergeomMean U G k - d)]
  exact withoutReplacement_lower_tail U G k hk d hd

theorem quarter_mean_lower
    {α : Type*} [DecidableEq α]
    {U G : Finset α} {k : ℕ}
    (hGU : G ⊆ U) (hdensity : U.card ≤ 4 * G.card)
    (hkpos : 0 < k) (hk : k ≤ U.card) :
    (k : ℝ) / 4 ≤ hypergeomMean U G k := by
  have hU : U.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le hkpos hk)
  rw [hypergeomMean_eq_of_subset hGU hU]
  have hUpos : (0 : ℝ) < U.card := by exact_mod_cast hU.card_pos
  have hdensityR : (U.card : ℝ) ≤ 4 * (G.card : ℝ) := by
    exact_mod_cast hdensity
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hkpos
  apply (le_div_iff₀ hUpos).2
  nlinarith

theorem three_quarters_mean_lower
    {α : Type*} [DecidableEq α]
    {U G : Finset α} {k : ℕ}
    (hGU : G ⊆ U) (hdensity : 3 * U.card ≤ 4 * G.card)
    (hkpos : 0 < k) (hk : k ≤ U.card) :
    3 * (k : ℝ) / 4 ≤ hypergeomMean U G k := by
  have hU : U.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le hkpos hk)
  rw [hypergeomMean_eq_of_subset hGU hU]
  have hUpos : (0 : ℝ) < U.card := by exact_mod_cast hU.card_pos
  have hdensityR : 3 * (U.card : ℝ) ≤ 4 * (G.card : ℝ) := by
    exact_mod_cast hdensity
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hkpos
  apply (le_div_iff₀ hUpos).2
  nlinarith

theorem nat_lt_div_implies_real_lt_div
    {r k q : ℕ} (hq : 0 < q)
    (h : r < k / q) :
    (r : ℝ) < (k : ℝ) / q := by
  sorry

/-- The density-1/4 specialization needed in Lemma 3.1. -/
theorem hypergeom_quarter_lower_tail_proved
    {α : Type*} [DecidableEq α]
    (U G : Finset α) (k : ℕ)
    (hGU : G ⊆ U) (hdensity : U.card ≤ 4 * G.card)
    (hk : k ≤ U.card) :
    uniformMass (U.powersetCard k)
      (fun T => (T ∩ G).card < k / 8) ≤
        Real.exp (-(k : ℝ) / 32) := by
  sorry

/-- The density-3/4 specialization needed in Lemma 3.3.  Hoeffding gives the
stronger exponent k/8; we weaken it to the paper's k/24. -/
theorem hypergeom_three_quarters_lower_tail_proved
    {α : Type*} [DecidableEq α]
    (U G : Finset α) (k : ℕ)
    (hGU : G ⊆ U) (hdensity : 3 * U.card ≤ 4 * G.card)
    (hk : k ≤ U.card) :
    uniformMass (U.powersetCard k)
      (fun T => (T ∩ G).card < k / 2) ≤
        Real.exp (-(k : ℝ) / 24) := by
  sorry

end

end GrahamRearrangement.External.Hypergeometric

namespace GrahamRearrangement.External

/-! Public wrappers preserving the names used by the paper formalization. -/

theorem hypergeom_quarter_lower_tail
    {α : Type*} [DecidableEq α]
    (U G : Finset α) (k : ℕ)
    (hGU : G ⊆ U) (hdensity : U.card ≤ 4 * G.card)
    (hk : k ≤ U.card) :
    uniformMass (U.powersetCard k)
      (fun T => (T ∩ G).card < k / 8) ≤
        Real.exp (-(k : ℝ) / 32) :=
  Hypergeometric.hypergeom_quarter_lower_tail_proved
    U G k hGU hdensity hk

theorem hypergeom_three_quarters_lower_tail
    {α : Type*} [DecidableEq α]
    (U G : Finset α) (k : ℕ)
    (hGU : G ⊆ U) (hdensity : 3 * U.card ≤ 4 * G.card)
    (hk : k ≤ U.card) :
    uniformMass (U.powersetCard k)
      (fun T => (T ∩ G).card < k / 2) ≤
        Real.exp (-(k : ℝ) / 24) :=
  Hypergeometric.hypergeom_three_quarters_lower_tail_proved
    U G k hGU hdensity hk

end GrahamRearrangement.External
