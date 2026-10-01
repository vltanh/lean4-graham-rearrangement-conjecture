module

public import GrahamRearrangement.Rearrangement.External

@[expose] public section

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Lemma 5.1
-/

noncomputable section

/-- Monotonicity of uniform mass, with both decidability instances left to
unification (so that it applies whatever instances the events carry). -/
private theorem l51_uniformMass_mono_of_imp {Ω : Type*} [DecidableEq Ω] (space : Finset Ω)
    {E F : Ω → Prop} {iE : DecidablePred E} {iF : DecidablePred F}
    (hEF : ∀ ω, E ω → F ω) :
    @uniformMass Ω _ space E iE ≤ @uniformMass Ω _ space F iF :=
  uniformMass_mono space E F hEF

def leftEndpointCandidates {n : ℕ} (b : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun a =>
    2 ≤ paperPos a ∧ paperPos a < paperPos b

def nearRightEnd {n : ℕ} (D : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun b => n ≤ paperPos b + 30 * D

private theorem l51_mem_leftEndpointCandidates {n : ℕ} {b a : Fin n} :
    a ∈ leftEndpointCandidates b ↔ 1 ≤ a.val ∧ a.val < b.val := by
  unfold leftEndpointCandidates
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, paperPos]
  omega

private theorem l51_mem_nearRightEnd {n D : ℕ} {b : Fin n} :
    b ∈ nearRightEnd (n := n) D ↔ n ≤ b.val + 1 + 30 * D := by
  unfold nearRightEnd
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, paperPos]

theorem card_near_right_end_le {n D : ℕ} :
    (nearRightEnd (n := n) D).card ≤ 30 * D + 1 := by
  classical
  have h := Finset.card_le_card_of_injOn (s := nearRightEnd (n := n) D)
    (t := Finset.range (30 * D + 1)) (fun b : Fin n => n - paperPos b)
    (by
      intro b hb
      rw [Finset.mem_coe, l51_mem_nearRightEnd] at hb
      simp only [Finset.mem_coe, Finset.mem_range, paperPos]
      omega)
    (by
      intro b hb c hc h
      rw [Finset.mem_coe, l51_mem_nearRightEnd] at hb hc
      simp only [paperPos] at h
      have := b.isLt
      have := c.isLt
      exact Fin.ext (by omega))
  simpa using h

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
  have h :=
    Section5External.fixedIndexSet_sumMass S (indexInterval a b) (0 : ZMod p)
  rw [card_indexInterval a b hab] at h
  rw [← h]
  unfold orderingEventMass
  apply uniformMass_congr
  intro σ _
  rw [indexSetSum_indexInterval]

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
  have hC : 0 ≤ chainConstant 1 := le_of_lt (chainConstant_pos 1)
  refine le_trans ?_
    (External.two_sided_interval_kernel_sum_le S.card p (chainConstant 1) hC)
  apply Finset.sum_le_sum_of_injOn (fun a : Fin S.card => b.val - a.val + 1)
  · intro a ha a' ha' h
    rw [Finset.mem_coe, l51_mem_leftEndpointCandidates] at ha ha'
    simp only at h
    exact Fin.ext (by omega)
  · intro r hr
    rcases Finset.mem_image.1 hr with ⟨a, ha, rfl⟩
    rw [l51_mem_leftEndpointCandidates] at ha
    have := b.isLt
    simp only [Finset.mem_Icc]
    omega
  · intro a _
    exact le_rfl
  · intro r _ _
    positivity

theorem fixed_badEndpoint_mass_le_three {α : ℝ}
    (hα0 : 0 < α) (hαh : α < 1 / 2)
    (P : Section5Parameters α)
    {p : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hreg : Section5Regime P p S)
    (b : Fin S.card) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    orderingEventMass S (fun σ => b ∈ badRightEndpoints σ) ≤
      3 * (S.card : ℝ) ^ (-α) := by
  let : NeZero p := ⟨hp.ne_zero⟩
  have hS : 2 ≤ S.card := section5_card_ge_two hα0 hαh hreg
  calc
    orderingEventMass S (fun σ => b ∈ badRightEndpoints σ)
      ≤ ∑ a ∈ leftEndpointCandidates b,
          orderingEventMass S
            (fun σ => indexedIntervalSum σ a b = 0) := by
          unfold orderingEventMass
          refine le_trans ?_ (uniformMass_exists_le_sum
            (indexedOrderings S) (leftEndpointCandidates b)
              (fun a σ => indexedIntervalSum σ a b = 0))
          apply l51_uniformMass_mono_of_imp
          intro σ hb
          exact badEndpoint_event_subset σ b hb
    _ = ∑ a ∈ leftEndpointCandidates b,
        sliceMass S (b.val - a.val + 1) 0 := by
          apply Finset.sum_congr rfl
          intro a ha
          have hab : a.val ≤ b.val := by
            rw [l51_mem_leftEndpointCandidates] at ha
            omega
          exact fixed_interval_sum_mass S a b hab
    _ ≤ ∑ a ∈ leftEndpointCandidates b,
      ((1 / (p : ℝ) +
        chainConstant 1 * Real.sqrt (Real.log (S.card : ℝ)) /
          ((S.card : ℝ) *
            Real.sqrt ((b.val - a.val + 1 : ℕ) : ℝ))) +
       (1 / (p : ℝ) +
        chainConstant 1 * Real.sqrt (Real.log (S.card : ℝ)) /
          ((S.card : ℝ) *
            Real.sqrt ((S.card - (b.val - a.val + 1) : ℕ) : ℝ)))) := by
          apply Finset.sum_le_sum
          intro a ha
          rw [l51_mem_leftEndpointCandidates] at ha
          have hr : 0 < b.val - a.val + 1 := by omega
          have hrS : b.val - a.val + 1 < S.card := by
            have := b.isLt
            omega
          exact corollary42_one_bound hp S hS hr hrS 0
    _ ≤ 2 * (S.card : ℝ) / p +
        4 * chainConstant 1 *
          Real.sqrt (Real.log (S.card : ℝ)) /
            Real.sqrt (S.card : ℝ) :=
          endpoint_cor42_sum_bound hα0 hαh P hp S hreg b
    _ ≤ 3 * (S.card : ℝ) ^ (-α) := by
          have hpBound := section5_card_over_p hα0 hαh hp hreg
          have hC :=
            section5_chainConstant_bound hreg 1 (Or.inl rfl)
          have h2 : 2 * (S.card : ℝ) / p = 2 * ((S.card : ℝ) / p) := by ring
          rw [h2]
          linarith

/-- Lemma 5.1. -/
theorem lemma5_1 {α : ℝ}
    (hα0 : 0 < α) (hαh : α < 1 / 2)
    (P : Section5Parameters α)
    {p : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hreg : Section5Regime P p S) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    orderingEventMass S (BadEvent1 P.D) ≤ 1 / 100 := by
  let : NeZero p := ⟨hp.ne_zero⟩
  have hsubset : ∀ σ : Fin S.card → ZMod p, BadEvent1 P.D σ →
      ∃ b ∈ nearRightEnd P.D, b ∈ badRightEndpoints σ := by
    intro σ h
    rcases h with ⟨b, hb, hnear⟩
    refine ⟨b, ?_, hb⟩
    rw [l51_mem_nearRightEnd]
    simp only [paperPos] at hnear
    omega
  have hcardpos : 0 < (S.card : ℝ) := by
    have := section5_card_ge_two hα0 hαh hreg
    exact_mod_cast (show 0 < S.card by omega)
  have hrpow_nonneg : 0 ≤ (S.card : ℝ) ^ (-α) :=
    Real.rpow_nonneg (le_of_lt hcardpos) _
  calc
    orderingEventMass S (BadEvent1 P.D)
      ≤ ∑ b ∈ nearRightEnd (n := S.card) P.D,
          orderingEventMass S (fun σ => b ∈ badRightEndpoints σ) := by
          unfold orderingEventMass
          refine le_trans ?_ (uniformMass_exists_le_sum
            (indexedOrderings S) (nearRightEnd P.D)
              (fun b σ => b ∈ badRightEndpoints σ))
          exact l51_uniformMass_mono_of_imp _ hsubset
    _ ≤ ∑ _b ∈ nearRightEnd (n := S.card) P.D,
          3 * (S.card : ℝ) ^ (-α) := by
          apply Finset.sum_le_sum
          intro b _
          exact fixed_badEndpoint_mass_le_three hα0 hαh P hp S hreg b
    _ = ((nearRightEnd (n := S.card) P.D).card : ℝ) *
          (3 * (S.card : ℝ) ^ (-α)) := by simp
    _ ≤ (30 * P.D + 1 : ℝ) *
          (3 * (S.card : ℝ) ^ (-α)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast
            (card_near_right_end_le (n := S.card) (D := P.D))
    _ ≤ 1 / 100 := by
          have hpow := section5_Calpha_power hα0 P
          have hcard := hreg.2.1
          have hDpos := section5Parameters_D_pos hα0 hαh P
          have hDR : (1 : ℝ) ≤ P.D := by exact_mod_cast hDpos
          have hnum :
              (30 * P.D + 1 : ℝ) * 3 ≤ 100 * P.D := by
            nlinarith
          have hlarge :
              100 * (P.D : ℝ) * 100 ≤ (10 ^ 4 : ℝ) * (2 : ℝ) ^ (40 * P.D) := by
            have := External.nat_le_two_pow_40 P.D
            nlinarith
          have hpowercard :
              (10 ^ 4 : ℝ) * (2 : ℝ) ^ (40 * P.D) ≤
                (S.card : ℝ) ^ α := by
            have hmono :=
              Real.rpow_le_rpow (le_of_lt P.Cα_pos) hcard (le_of_lt hα0)
            exact le_trans hpow hmono
          have hSα : 0 < (S.card : ℝ) ^ α := Real.rpow_pos_of_pos hcardpos α
          have hneg : (S.card : ℝ) ^ (-α) * (S.card : ℝ) ^ α = 1 := by
            rw [← Real.rpow_add hcardpos]
            simp
          nlinarith

end

end GrahamRearrangement
