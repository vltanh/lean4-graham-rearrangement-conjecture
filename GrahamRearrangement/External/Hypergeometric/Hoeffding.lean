module

public import GrahamRearrangement.External.Hypergeometric.Sampling
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Probability.ProbabilityMassFunction.Integrals

@[expose] public section

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory

namespace GrahamRearrangement.External.Hypergeometric

/-!
# Finite Hoeffding inequality without replacement

We prove the lower-tail estimate needed by Pham--Sauermann.  The only analytic
ingredient is mathlib's proved Hoeffding lemma
`ProbabilityTheory.mgf_le_of_mem_Icc_of_integral_eq_zero`.
The without-replacement part is proved here by exposing one draw at a time.
-/

noncomputable section

theorem uniformExpectation_smul_left
    {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (c : ℝ) (f : Ω → ℝ) :
    uniformExpectation space (fun ω => c * f ω) =
      c * uniformExpectation space f := by
  sorry

theorem withoutReplacementExpectation_smul
    {α : Type*} [DecidableEq α]
    (U : Finset α) (k : ℕ) (c : ℝ) (f : List α → ℝ) :
    withoutReplacementExpectation U k (fun xs => c * f xs) =
      c * withoutReplacementExpectation U k f := by
  induction k generalizing U f with
  | zero => simp [withoutReplacementExpectation]
  | succ k ih =>
      rw [withoutReplacementExpectation_succ,
        withoutReplacementExpectation_succ]
      simp_rw [ih]
      exact uniformExpectation_smul_left U c _

theorem withoutReplacementExpectation_congr
    {α : Type*} [DecidableEq α]
    (U : Finset α) (k : ℕ) (f g : List α → ℝ)
    (h : ∀ xs, f xs = g xs) :
    withoutReplacementExpectation U k f =
      withoutReplacementExpectation U k g := by
  apply le_antisymm
  · exact withoutReplacementExpectation_mono U k f g
      (fun xs => (h xs).le)
  · exact withoutReplacementExpectation_mono U k g f
      (fun xs => (h xs).ge)

theorem withoutReplacementMass_le_one
    {α : Type*} [DecidableEq α]
    (U : Finset α) (k : ℕ) (hk : k ≤ U.card)
    (E : List α → Prop) [DecidablePred E] :
    withoutReplacementMass U k E ≤ 1 := by
  unfold withoutReplacementMass
  calc
    withoutReplacementExpectation U k
        (fun xs => if E xs then 1 else 0)
      ≤ withoutReplacementExpectation U k (fun _ => 1) := by
          apply withoutReplacementExpectation_mono
          intro xs
          split <;> norm_num
    _ = 1 := withoutReplacementExpectation_const U hk 1

/-- Hoeffding's lemma written for the repository's finite uniform expectation.
We pass to the finite subtype of points in the sample space, use mathlib's
uniform probability mass function, and translate the resulting finite sum back. -/
theorem finite_uniform_hoeffding_mgf
    {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (hspace : space.Nonempty)
    (X : Ω → ℝ) (a b t : ℝ)
    (hab : a ≤ b)
    (hX : ∀ ω ∈ space, X ω ∈ Set.Icc a b)
    (hmean : uniformExpectation space X = 0)
    (ht : 0 < t) :
    uniformExpectation space (fun ω => Real.exp (t * X ω)) ≤
      Real.exp ((b - a) ^ 2 * t ^ 2 / 8) := by
  sorry

def successIndicator {α : Type*} [DecidableEq α]
    (G : Finset α) (x : α) : ℝ :=
  if x ∈ G then 1 else 0

def successCount {α : Type*} [DecidableEq α]
    (G : Finset α) (xs : List α) : ℕ :=
  (xs.filter fun x => x ∈ G).length

@[simp] theorem successCount_nil {α : Type*} [DecidableEq α]
    (G : Finset α) :
    successCount G [] = 0 := by
  simp [successCount]

@[simp] theorem successCount_cons {α : Type*} [DecidableEq α]
    (G : Finset α) (x : α) (xs : List α) :
    successCount G (x :: xs) =
      (if x ∈ G then 1 else 0) + successCount G xs := by
  sorry

theorem successCount_eq_card_toFinset
    {α : Type*} [DecidableEq α]
    (G : Finset α) {xs : List α} (hxs : xs.Nodup) :
    successCount G xs = (xs.toFinset ∩ G).card := by
  sorry

def hypergeomMean {α : Type*} [DecidableEq α]
    (U G : Finset α) (k : ℕ) : ℝ :=
  if U.card = 0 then 0
  else (k : ℝ) * ((U ∩ G).card : ℝ) / (U.card : ℝ)

def exposureDrift {α : Type*} [DecidableEq α]
    (U G : Finset α) (k : ℕ) (x : α) : ℝ :=
  hypergeomMean U G (k + 1) -
    successIndicator G x -
    hypergeomMean (U.erase x) G k

theorem hypergeomMean_zero {α : Type*} [DecidableEq α] (U G : Finset α) :
    hypergeomMean U G 0 = 0 := by
  sorry

theorem hypergeomMean_of_nonempty
    {α : Type*} [DecidableEq α]
    {U G : Finset α} (hU : U.Nonempty) (k : ℕ) :
    hypergeomMean U G k =
      (k : ℝ) * ((U ∩ G).card : ℝ) / (U.card : ℝ) := by
  simp [hypergeomMean,hU.card_ne_zero]

theorem erase_inter_card
    {α : Type*} [DecidableEq α]
    {U G : Finset α} {x : α} (hxU : x ∈ U) :
    ((U.erase x) ∩ G).card =
      (U ∩ G).card - (if x ∈ G then 1 else 0) := by
  sorry

def exposureLower {α : Type*} [DecidableEq α]
    (U G : Finset α) (k : ℕ) : ℝ :=
  -(((U.card - (U ∩ G).card : ℕ) : ℝ) *
      ((U.card - (k + 1) : ℕ) : ℝ) /
      ((U.card : ℝ) * (U.card - 1 : ℕ)))

def exposureUpper {α : Type*} [DecidableEq α]
    (U G : Finset α) (k : ℕ) : ℝ :=
  ((U ∩ G).card : ℝ) *
      ((U.card - (k + 1) : ℕ) : ℝ) /
      ((U.card : ℝ) * (U.card - 1 : ℕ))

theorem exposureDrift_eq_lower_of_mem
    {α : Type*} [DecidableEq α]
    {U G : Finset α} {k : ℕ} {x : α}
    (hxU : x ∈ U) (hxG : x ∈ G)
    (hU2 : 2 ≤ U.card) :
    exposureDrift U G k x = exposureLower U G k := by
  sorry

theorem exposureDrift_eq_upper_of_not_mem
    {α : Type*} [DecidableEq α]
    {U G : Finset α} {k : ℕ} {x : α}
    (hxU : x ∈ U) (hxG : x ∉ G)
    (hU2 : 2 ≤ U.card) :
    exposureDrift U G k x = exposureUpper U G k := by
  sorry

theorem exposureDrift_mean_zero
    {α : Type*} [DecidableEq α]
    (U G : Finset α) (k : ℕ)
    (hU2 : 2 ≤ U.card) (hk : k + 1 ≤ U.card) :
    uniformExpectation U (exposureDrift U G k) = 0 := by
  sorry

theorem exposureDrift_mem_Icc
    {α : Type*} [DecidableEq α]
    (U G : Finset α) (k : ℕ)
    (hU2 : 2 ≤ U.card) (hk : k + 1 ≤ U.card) :
    ∀ x ∈ U,
      exposureDrift U G k x ∈
        Set.Icc (exposureLower U G k) (exposureUpper U G k) := by
  sorry

theorem exposureLower_le_upper
    {α : Type*} [DecidableEq α]
    (U G : Finset α) (k : ℕ) (hU2 : 2 ≤ U.card) :
    exposureLower U G k ≤ exposureUpper U G k := by
  sorry

theorem exposure_width_le_one
    {α : Type*} [DecidableEq α]
    (U G : Finset α) (k : ℕ)
    (hU2 : 2 ≤ U.card) (hk : k + 1 ≤ U.card) :
    exposureUpper U G k - exposureLower U G k ≤ 1 := by
  sorry

theorem exposure_mgf_le
    {α : Type*} [DecidableEq α]
    (U G : Finset α) (k : ℕ)
    (hU2 : 2 ≤ U.card) (hk : k + 1 ≤ U.card)
    (t : ℝ) (ht : 0 < t) :
    uniformExpectation U
        (fun x => Real.exp (t * exposureDrift U G k x)) ≤
      Real.exp (t ^ 2 / 8) := by
  have hU : U.Nonempty := Finset.card_pos.mp (by omega)
  have hmgf :=
    finite_uniform_hoeffding_mgf
      U hU (exposureDrift U G k)
      (exposureLower U G k) (exposureUpper U G k) t
      (exposureLower_le_upper U G k hU2)
      (exposureDrift_mem_Icc U G k hU2 hk)
      (exposureDrift_mean_zero U G k hU2 hk) ht
  have hwidth := exposure_width_le_one U G k hU2 hk
  have hsquare :
      (exposureUpper U G k - exposureLower U G k) ^ 2 ≤ 1 := by
    have hnonneg :
        0 ≤ exposureUpper U G k - exposureLower U G k :=
      sub_nonneg.mpr (exposureLower_le_upper U G k hU2)
    nlinarith
  exact le_trans hmgf (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg t]))

theorem centered_success_decomposition
    {α : Type*} [DecidableEq α]
    (U G : Finset α) (k : ℕ) (x : α) (xs : List α) :
    hypergeomMean U G (k + 1) -
        (successCount G (x :: xs) : ℝ) =
      exposureDrift U G k x +
        (hypergeomMean (U.erase x) G k -
          (successCount G xs : ℝ)) := by
  sorry

/-- Centered exponential moment for sampling without replacement. -/
theorem withoutReplacement_centered_mgf_le
    {α : Type*} [DecidableEq α]
    (U G : Finset α) (k : ℕ) (hk : k ≤ U.card)
    (t : ℝ) (ht : 0 ≤ t) :
    withoutReplacementExpectation U k
      (fun xs =>
        Real.exp (t *
          (hypergeomMean U G k - (successCount G xs : ℝ)))) ≤
      Real.exp (t ^ 2 * k / 8) := by
  sorry

/-- Exponential Markov applied to the centered without-replacement statistic. -/
theorem withoutReplacement_lower_tail
    {α : Type*} [DecidableEq α]
    (U G : Finset α) (k : ℕ) (hk : k ≤ U.card)
    (d : ℝ) (hd : 0 ≤ d) :
    withoutReplacementMass U k
      (fun xs =>
        (successCount G xs : ℝ) ≤ hypergeomMean U G k - d) ≤
      if k = 0 then 1 else
        Real.exp (-2 * d ^ 2 / k) := by
  sorry

end

end GrahamRearrangement.External.Hypergeometric
