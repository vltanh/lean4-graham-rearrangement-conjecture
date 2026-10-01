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
  unfold uniformExpectation
  rw [← Finset.mul_sum, mul_div_assoc]

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
  classical
  have : Nonempty space := hspace.to_subtype
  let : MeasurableSpace space := ⊤
  have : MeasurableSingletonClass space := ⟨fun _ => trivial⟩
  set μ : Measure space := (PMF.uniformOfFintype space).toMeasure with hμ
  -- integrals against `μ` are the repository's uniform expectations
  have hint : ∀ f : Ω → ℝ, ∫ ω, f ω.1 ∂μ = uniformExpectation space f := by
    intro f
    rw [hμ, PMF.integral_eq_sum]
    simp only [PMF.uniformOfFintype_apply, smul_eq_mul, ENNReal.toReal_inv,
      ENNReal.toReal_natCast, Fintype.card_coe]
    rw [← Finset.mul_sum, uniformExpectation, Finset.sum_coe_sort space f]
    ring
  have hm : AEMeasurable (fun ω : space => X ω.1) μ :=
    (measurable_of_countable _).aemeasurable
  have hb : ∀ᵐ ω ∂μ, X ω.1 ∈ Set.Icc a b :=
    Filter.Eventually.of_forall (fun ω => hX ω.1 ω.2)
  have hc : μ[fun ω : space => X ω.1] = 0 := by rw [hint X]; exact hmean
  have h := ProbabilityTheory.mgf_le_of_mem_Icc_of_integral_eq_zero hm hb hc ht
  rw [ProbabilityTheory.mgf, hint (fun ω => Real.exp (t * X ω))] at h
  refine h.trans_eq ?_
  congr 1
  push_cast [coe_nnnorm, Real.norm_eq_abs]
  rw [abs_of_nonneg (sub_nonneg.mpr hab)]
  ring

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
  by_cases hx : x ∈ G <;> simp [successCount, hx, Nat.add_comm]

theorem successCount_eq_card_toFinset
    {α : Type*} [DecidableEq α]
    (G : Finset α) {xs : List α} (hxs : xs.Nodup) :
    successCount G xs = (xs.toFinset ∩ G).card := by
  induction xs with
  | nil => simp [successCount]
  | cons x xs ih =>
      have hx : x ∉ xs := (List.nodup_cons.mp hxs).1
      have hnd := (List.nodup_cons.mp hxs).2
      rw [successCount_cons, ih hnd, List.toFinset_cons]
      by_cases hxG : x ∈ G
      · rw [ite_eq_left hxG, Finset.insert_inter_of_mem hxG,
          Finset.card_insert_of_notMem (fun h =>
            hx (List.mem_toFinset.mp (Finset.mem_inter.mp h).1)),
          Nat.add_comm]
      · rw [ite_eq_right hxG, Finset.insert_inter_of_notMem hxG, Nat.zero_add]

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
  simp [hypergeomMean]

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
  rw [Finset.erase_inter]
  by_cases hxG : x ∈ G
  · rw [ite_eq_left hxG, Finset.card_erase_of_mem (Finset.mem_inter.mpr ⟨hxU, hxG⟩)]
  · rw [ite_eq_right hxG, Nat.sub_zero,
      Finset.erase_eq_of_notMem (fun h => hxG (Finset.mem_inter.mp h).2)]

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

/-- A successful first draw gives the lower drift value.  The hypothesis
`k + 1 ≤ U.card` is needed because `exposureLower` uses the truncated
subtraction `U.card - (k + 1)`. -/
theorem exposureDrift_eq_lower_of_mem
    {α : Type*} [DecidableEq α]
    {U G : Finset α} {k : ℕ} {x : α}
    (hxU : x ∈ U) (hxG : x ∈ G)
    (hU2 : 2 ≤ U.card) (hk : k + 1 ≤ U.card) :
    exposureDrift U G k x = exposureLower U G k := by
  have hU : U.Nonempty := ⟨x, hxU⟩
  have hcard : (U.erase x).card = U.card - 1 := Finset.card_erase_of_mem hxU
  have heU : (U.erase x).Nonempty := Finset.card_pos.mp (by omega)
  have hg1 : 1 ≤ (U ∩ G).card :=
    Finset.card_pos.mpr ⟨x, Finset.mem_inter.mpr ⟨hxU, hxG⟩⟩
  have hgN : (U ∩ G).card ≤ U.card :=
    Finset.card_le_card Finset.inter_subset_left
  have hint : ((U.erase x) ∩ G).card = (U ∩ G).card - 1 := by
    rw [erase_inter_card hxU, ite_eq_left hxG]
  unfold exposureDrift exposureLower successIndicator
  rw [hypergeomMean_of_nonempty hU, hypergeomMean_of_nonempty heU, hcard,
    hint, ite_eq_left hxG]
  have hN1 : ((U.card - 1 : ℕ) : ℝ) = (U.card : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ U.card), Nat.cast_one]
  rw [hN1, Nat.cast_sub hg1, Nat.cast_sub hgN, Nat.cast_sub hk]
  have hN : (U.card : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ U.card := by exact_mod_cast hU2
    linarith
  have hN' : (U.card : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ U.card := by exact_mod_cast hU2
    linarith
  field_simp
  push_cast
  ring

/-- An unsuccessful first draw gives the upper drift value.  As above,
`k + 1 ≤ U.card` is needed because of the truncated subtraction. -/
theorem exposureDrift_eq_upper_of_not_mem
    {α : Type*} [DecidableEq α]
    {U G : Finset α} {k : ℕ} {x : α}
    (hxU : x ∈ U) (hxG : x ∉ G)
    (hU2 : 2 ≤ U.card) (hk : k + 1 ≤ U.card) :
    exposureDrift U G k x = exposureUpper U G k := by
  have hU : U.Nonempty := ⟨x, hxU⟩
  have hcard : (U.erase x).card = U.card - 1 := Finset.card_erase_of_mem hxU
  have heU : (U.erase x).Nonempty := Finset.card_pos.mp (by omega)
  have hint : ((U.erase x) ∩ G).card = (U ∩ G).card := by
    rw [erase_inter_card hxU, ite_eq_right hxG, Nat.sub_zero]
  unfold exposureDrift exposureUpper successIndicator
  rw [hypergeomMean_of_nonempty hU, hypergeomMean_of_nonempty heU, hcard,
    hint, ite_eq_right hxG]
  have hN1 : ((U.card - 1 : ℕ) : ℝ) = (U.card : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ U.card), Nat.cast_one]
  rw [hN1, Nat.cast_sub hk]
  have hN : (U.card : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ U.card := by exact_mod_cast hU2
    linarith
  have hN' : (U.card : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ U.card := by exact_mod_cast hU2
    linarith
  field_simp
  push_cast
  ring

theorem exposureDrift_mean_zero
    {α : Type*} [DecidableEq α]
    (U G : Finset α) (k : ℕ)
    (hU2 : 2 ≤ U.card) (hk : k + 1 ≤ U.card) :
    uniformExpectation U (exposureDrift U G k) = 0 := by
  unfold uniformExpectation
  rw [← Finset.sum_filter_add_sum_filter_not U (fun x => x ∈ G),
    Finset.sum_congr rfl (fun x hx => exposureDrift_eq_lower_of_mem
      (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2 hU2 hk),
    Finset.sum_congr rfl (fun x hx => exposureDrift_eq_upper_of_not_mem
      (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2 hU2 hk),
    Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
  have h1 : (U.filter (fun x => x ∈ G)).card = (U ∩ G).card := by
    rw [Finset.filter_mem_eq_inter]
  have h2 : (U.filter (fun x => x ∉ G)).card = U.card - (U ∩ G).card := by
    have := Finset.card_filter_add_card_filter_not (s := U) (fun x => x ∈ G)
    omega
  rw [h1, h2]
  unfold exposureLower exposureUpper
  ring

theorem exposureLower_le_upper
    {α : Type*} [DecidableEq α]
    (U G : Finset α) (k : ℕ) (hU2 : 2 ≤ U.card) :
    exposureLower U G k ≤ exposureUpper U G k := by
  unfold exposureLower exposureUpper
  have hleft :
      0 ≤ ((U.card - (U ∩ G).card : ℕ) : ℝ) *
        ((U.card - (k + 1) : ℕ) : ℝ) /
        ((U.card : ℝ) * (U.card - 1 : ℕ)) := by
    positivity
  have hright :
      0 ≤ ((U ∩ G).card : ℝ) *
        ((U.card - (k + 1) : ℕ) : ℝ) /
        ((U.card : ℝ) * (U.card - 1 : ℕ)) := by
    positivity
  linarith

theorem exposureDrift_mem_Icc
    {α : Type*} [DecidableEq α]
    (U G : Finset α) (k : ℕ)
    (hU2 : 2 ≤ U.card) (hk : k + 1 ≤ U.card) :
    ∀ x ∈ U,
      exposureDrift U G k x ∈
        Set.Icc (exposureLower U G k) (exposureUpper U G k) := by
  intro x hx
  have hle := exposureLower_le_upper U G k hU2
  by_cases hxG : x ∈ G
  · rw [exposureDrift_eq_lower_of_mem hx hxG hU2 hk]
    exact ⟨le_rfl, hle⟩
  · rw [exposureDrift_eq_upper_of_not_mem hx hxG hU2 hk]
    exact ⟨hle, le_rfl⟩

theorem exposure_width_le_one
    {α : Type*} [DecidableEq α]
    (U G : Finset α) (k : ℕ)
    (hU2 : 2 ≤ U.card) (hk : k + 1 ≤ U.card) :
    exposureUpper U G k - exposureLower U G k ≤ 1 := by
  unfold exposureUpper exposureLower
  have hgN : (U ∩ G).card ≤ U.card :=
    Finset.card_le_card Finset.inter_subset_left
  have h2 : (2 : ℝ) ≤ U.card := by exact_mod_cast hU2
  have hN1 : ((U.card - 1 : ℕ) : ℝ) = (U.card : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ U.card), Nat.cast_one]
  rw [hN1, Nat.cast_sub hgN, Nat.cast_sub hk]
  have hden : (0 : ℝ) < (U.card : ℝ) * ((U.card : ℝ) - 1) := by nlinarith
  rw [sub_neg_eq_add, ← add_div, div_le_one hden]
  push_cast
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith [mul_nonneg (Nat.cast_nonneg U.card : (0 : ℝ) ≤ U.card) hk0]

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
  unfold exposureDrift successIndicator
  rw [successCount_cons, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  ring

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
  induction k generalizing U with
  | zero =>
      simp [withoutReplacementExpectation_zero, hypergeomMean_zero]
  | succ k ih =>
      rcases ht.eq_or_lt with ht0 | htpos
      · subst ht0
        simpa using (withoutReplacementExpectation_const U hk (1 : ℝ)).le
      rw [withoutReplacementExpectation_succ]
      by_cases hU1 : U.card = 1
      · -- a single remaining element: the centered statistic vanishes
        obtain ⟨y, rfl⟩ := Finset.card_eq_one.mp hU1
        have hk0 : k = 0 := by
          rw [Finset.card_singleton] at hk
          omega
        subst hk0
        have hzero :
            (hypergeomMean {y} G (0 + 1) -
              (successCount G [y] : ℝ)) = 0 := by
          rw [hypergeomMean_of_nonempty (Finset.singleton_nonempty y)]
          by_cases hyG : y ∈ G
          · simp [Finset.singleton_inter_of_mem hyG, successCount, hyG]
          · simp [Finset.singleton_inter_of_notMem hyG, successCount, hyG]
        unfold uniformExpectation
        rw [Finset.sum_singleton, Finset.card_singleton,
          withoutReplacementExpectation_zero, hzero]
        simp only [mul_zero, Real.exp_zero, Nat.cast_one, div_one]
        exact Real.one_le_exp (by positivity)
      have hU2 : 2 ≤ U.card := by
        have : 1 ≤ U.card := le_trans (by omega) hk
        omega
      have hchild : ∀ x ∈ U, k ≤ (U.erase x).card := by
        intro x hx
        rw [Finset.card_erase_of_mem hx]
        omega
      calc
        uniformExpectation U
            (fun x =>
              withoutReplacementExpectation (U.erase x) k
                (fun xs =>
                  Real.exp (t *
                    (hypergeomMean U G (k + 1) -
                      (successCount G (x :: xs) : ℝ)))))
          ≤ uniformExpectation U
              (fun x =>
                Real.exp (t * exposureDrift U G k x) *
                  Real.exp (t ^ 2 * k / 8)) := by
            apply uniformExpectation_le_of_forall_mem
            intro x hx
            rw [withoutReplacementExpectation_congr (U.erase x) k _
              (fun xs =>
                Real.exp (t * exposureDrift U G k x) *
                  Real.exp (t *
                    (hypergeomMean (U.erase x) G k -
                      (successCount G xs : ℝ))))
              (fun xs => by
                rw [centered_success_decomposition, mul_add, Real.exp_add]),
              withoutReplacementExpectation_smul]
            gcongr
            exact ih (U.erase x) (hchild x hx)
        _ = uniformExpectation U
              (fun x => Real.exp (t * exposureDrift U G k x)) *
                Real.exp (t ^ 2 * k / 8) := by
            unfold uniformExpectation
            rw [← Finset.sum_mul]
            ring
        _ ≤ Real.exp (t ^ 2 / 8) * Real.exp (t ^ 2 * k / 8) := by
            gcongr
            exact exposure_mgf_le U G k hU2 hk t htpos
        _ = Real.exp (t ^ 2 * ((k + 1 : ℕ) : ℝ) / 8) := by
            rw [← Real.exp_add]
            congr 1
            push_cast
            ring

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
  by_cases hk0 : k = 0
  · subst hk0
    rw [ite_eq_left rfl]
    unfold withoutReplacementMass
    rw [withoutReplacementExpectation_zero]
    split_ifs <;> norm_num
  rw [ite_eq_right hk0]
  have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk0
  set t : ℝ := 4 * d / k with ht_def
  have ht : 0 ≤ t := by positivity
  have hpoint : ∀ xs,
      (if (successCount G xs : ℝ) ≤ hypergeomMean U G k - d
        then (1 : ℝ) else 0) ≤
        Real.exp (-t * d) *
          Real.exp (t *
            (hypergeomMean U G k - (successCount G xs : ℝ))) := by
    intro xs
    split_ifs with hE
    · rw [← Real.exp_add]
      apply Real.one_le_exp
      nlinarith [mul_nonneg ht (sub_nonneg.mpr hE)]
    · positivity
  unfold withoutReplacementMass
  calc
    _ ≤ withoutReplacementExpectation U k
          (fun xs =>
            Real.exp (-t * d) *
              Real.exp (t *
                (hypergeomMean U G k - (successCount G xs : ℝ)))) :=
        withoutReplacementExpectation_mono U k _ _ hpoint
    _ = Real.exp (-t * d) *
          withoutReplacementExpectation U k
            (fun xs =>
              Real.exp (t *
                (hypergeomMean U G k - (successCount G xs : ℝ)))) :=
        withoutReplacementExpectation_smul U k _ _
    _ ≤ Real.exp (-t * d) * Real.exp (t ^ 2 * k / 8) := by
        gcongr
        exact withoutReplacement_centered_mgf_le U G k hk t ht
    _ = Real.exp (-2 * d ^ 2 / k) := by
        rw [← Real.exp_add]
        congr 1
        rw [ht_def]
        field_simp
        ring

end

end GrahamRearrangement.External.Hypergeometric
