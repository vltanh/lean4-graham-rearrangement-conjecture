module

public import GrahamRearrangement.Rearrangement.Lemma51

@[expose] public section

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Lemma 5.4 and equation (5.1)
-/

noncomputable section

/-- Monotonicity of uniform mass, with both decidability instances left to
unification (so that it applies whatever instances the events carry). -/
private theorem l54_uniformMass_mono_on {Ω : Type*} [DecidableEq Ω] (space : Finset Ω)
    {E F : Ω → Prop} {iE : DecidablePred E} {iF : DecidablePred F}
    (hEF : ∀ ω ∈ space, E ω → F ω) :
    @uniformMass Ω _ space E iE ≤ @uniformMass Ω _ space F iF :=
  uniformMass_mono_on space E F hEF

private theorem l54_mem_leftEndpointCandidates {n : ℕ} {b a : Fin n} :
    a ∈ leftEndpointCandidates b ↔ 1 ≤ a.val ∧ a.val < b.val := by
  unfold leftEndpointCandidates
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, paperPos]
  omega

private theorem l54_mem_forwardWindow {n r : ℕ} {b x : Fin n} :
    x ∈ forwardWindow b r ↔ b.val ≤ x.val ∧ x.val ≤ b.val + r := by
  unfold forwardWindow
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

private theorem l54_mem_indexHalfOpen {n : ℕ} {a b x : Fin n} :
    x ∈ indexHalfOpen a b ↔ a.val ≤ x.val ∧ x.val < b.val := by
  unfold indexHalfOpen
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

def exposedWindow {n : ℕ} (D : ℕ) (b : Fin n) : Finset (Fin n) :=
  forwardWindow b (20 * D)

theorem exposedWindow_card {n D : ℕ} (b : Fin n)
    (hfit : paperPos b + 20 * D ≤ n) :
    (exposedWindow D b).card = 20 * D + 1 := by
  unfold exposedWindow
  apply card_forwardWindow_eq
  simp [paperPos] at hfit ⊢
  omega

theorem collision_event_determined
    {n p : ℕ} {F J J' : Finset (Fin n)}
    (hJ : J ⊆ F) (hJ' : J' ⊆ F)
    {σ τ : Fin n → ZMod p}
    (hag : AgreesOn F σ τ) :
    (indexSetSum σ J = indexSetSum σ J') ↔
      (indexSetSum τ J = indexSetSum τ J') := by
  have hsumJ : indexSetSum σ J = indexSetSum τ J := by
    unfold indexSetSum
    apply Finset.sum_congr rfl
    intro i hi
    exact hag i (hJ hi)
  have hsumJ' : indexSetSum σ J' = indexSetSum τ J' := by
    unfold indexSetSum
    apply Finset.sum_congr rfl
    intro i hi
    exact hag i (hJ' hi)
  rw [hsumJ, hsumJ']

theorem conditional_badEndpoint_mass_le_four
    {α : ℝ} (hα0 : 0 < α) (hαh : α < 1 / 2)
    (P : Section5Parameters α)
    {p : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hreg : Section5Regime P p S)
    (b : Fin S.card)
    (hbfit : paperPos b + 30 * P.D ≤ S.card)
    (τ : Fin S.card → ZMod p) (hτ : IsIndexedOrdering S τ) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    orderingConditionalMass S
      (fun σ => AgreesOn (exposedWindow P.D b) σ τ)
      (fun σ => b ∈ badRightEndpoints σ) ≤
        4 * (S.card : ℝ) ^ (-α) := by
  let : NeZero p := ⟨hp.ne_zero⟩
  have hn50 := section5_card_ge_fiftyD hreg
  have hD : 0 < P.D := section5Parameters_D_pos hα0 hαh P
  have hS2 : 2 ≤ S.card := section5_card_ge_two hα0 hαh hreg
  have hbval : b.val + 1 + 30 * P.D ≤ S.card := by
    simpa only [paperPos] using hbfit
  have hFcard : (exposedWindow P.D b).card = 20 * P.D + 1 :=
    exposedWindow_card b (by omega)
  have himage : (indexImageSet τ (exposedWindow P.D b)).card =
      (exposedWindow P.D b).card :=
    Section5.exposed_image_card S hτ (exposedWindow P.D b)
  have hsub : indexImageSet τ (exposedWindow P.D b) ⊆ S :=
    Section5.exposedImage_subset S hτ (exposedWindow P.D b)
  have hTcard : (S \ indexImageSet τ (exposedWindow P.D b)).card =
      S.card - (20 * P.D + 1) := by
    rw [Finset.card_sdiff_of_subset hsub, himage, hFcard]
  set T := S \ indexImageSet τ (exposedWindow P.D b) with hT
  have hT2 : 2 ≤ T.card := by rw [hTcard]; omega
  have hTpos : (0 : ℝ) < T.card := by exact_mod_cast (show 0 < T.card by omega)
  have hTleS : T.card ≤ S.card := by rw [hTcard]; omega
  have hS4T : S.card ≤ 4 * T.card := by rw [hTcard]; omega
  have hSpos : (0 : ℝ) < S.card := by exact_mod_cast (show 0 < S.card by omega)
  let I : Fin S.card → Finset (Fin S.card) := fun a => indexHalfOpen a b
  let z : Fin S.card → ZMod p := fun _ => -τ b
  have hdisj : ∀ a ∈ leftEndpointCandidates b,
      Disjoint (exposedWindow P.D b) (I a) := by
    intro a _
    rw [Finset.disjoint_left]
    intro i hiF hiI
    rw [exposedWindow, l54_mem_forwardWindow] at hiF
    rw [l54_mem_indexHalfOpen] at hiI
    omega
  have hsubset :
      ∀ σ : Fin S.card → ZMod p,
        AgreesOn (exposedWindow P.D b) σ τ → b ∈ badRightEndpoints σ →
        ∃ a ∈ leftEndpointCandidates b, indexSetSum σ (I a) = z a := by
    intro σ hag hb
    rcases (mem_badRightEndpoints_iff σ b).1 hb with ⟨a, ha2, hab, hzero⟩
    simp only [paperPos] at ha2 hab
    refine ⟨a, ?_, ?_⟩
    · rw [l54_mem_leftEndpointCandidates]
      omega
    · have hsplit := interval_sum_eq_halfOpen_add_endpoint σ a b (by omega)
      have hbF : b ∈ exposedWindow P.D b := by
        rw [exposedWindow, l54_mem_forwardWindow]
        omega
      have hsigma_b : σ b = τ b := hag b hbF
      rw [hzero, hsigma_b] at hsplit
      exact eq_neg_of_add_eq_zero_left hsplit.symm
  have hstep1 :
      orderingConditionalMass S
        (fun σ => AgreesOn (exposedWindow P.D b) σ τ)
        (fun σ => b ∈ badRightEndpoints σ) ≤
      ∑ a ∈ leftEndpointCandidates b, sliceMass T (I a).card (z a) := by
    refine le_trans ?_
      (Section5.conditional_index_family_sumMass_le_zmod S τ hτ
        (exposedWindow P.D b) (leftEndpointCandidates b) I z hdisj)
    unfold orderingConditionalMass uniformConditionalMass
    apply l54_uniformMass_mono_on
    intro σ hσ hb
    exact hsubset σ (Finset.mem_filter.1 hσ).2 hb
  have hC1 : 0 ≤ chainConstant 1 := le_of_lt (chainConstant_pos 1)
  have hstep2 :
      ∑ a ∈ leftEndpointCandidates b, sliceMass T (I a).card (z a) ≤
        2 * (T.card : ℝ) / p +
          4 * chainConstant 1 * Real.sqrt (Real.log (T.card : ℝ)) /
            Real.sqrt (T.card : ℝ) := by
    refine le_trans ?_
      (Auxiliary.two_sided_interval_kernel_sum_le T.card p (chainConstant 1) hC1)
    apply Finset.sum_le_sum_of_injOn (fun a => (I a).card)
    · intro a ha a' ha' h
      rw [Finset.mem_coe, l54_mem_leftEndpointCandidates] at ha ha'
      simp only [I] at h
      rw [card_indexHalfOpen a b (by omega), card_indexHalfOpen a' b (by omega)] at h
      exact Fin.ext (by omega)
    · intro r hr
      rcases Finset.mem_image.1 hr with ⟨a, ha, rfl⟩
      rw [l54_mem_leftEndpointCandidates] at ha
      simp only [I]
      rw [card_indexHalfOpen a b (by omega), Finset.mem_Icc]
      omega
    · intro a ha
      rw [l54_mem_leftEndpointCandidates] at ha
      have hcard : (I a).card = b.val - a.val := card_indexHalfOpen a b (by omega)
      have hr : 0 < (I a).card := by rw [hcard]; omega
      have hrT : (I a).card < T.card := by rw [hcard, hTcard]; omega
      exact corollary42_one_bound hp T hT2 hr hrT (z a)
    · intro r _ _
      positivity
  have hpBound := section5_card_over_p hα0 hαh hp hreg
  have hCb := section5_chainConstant_bound hreg 1 (Or.inl rfl)
  have hpT : (T.card : ℝ) / p ≤ (S.card : ℝ) ^ (-α) := by
    refine le_trans ?_ hpBound
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg p)
    exact_mod_cast hTleS
  have hlog : Real.sqrt (Real.log (T.card : ℝ)) ≤ Real.sqrt (Real.log (S.card : ℝ)) :=
    Real.sqrt_le_sqrt (Real.log_le_log hTpos (by exact_mod_cast hTleS))
  have hroot : Real.sqrt (S.card : ℝ) ≤ 2 * Real.sqrt (T.card : ℝ) := by
    have h4 : Real.sqrt (S.card : ℝ) ≤ Real.sqrt (4 * (T.card : ℝ)) :=
      Real.sqrt_le_sqrt (by exact_mod_cast hS4T)
    have h2 : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    rw [Real.sqrt_mul (by norm_num), h2] at h4
    exact h4
  have hSroot : 0 < Real.sqrt (S.card : ℝ) := Real.sqrt_pos.2 hSpos
  have hTroot : 0 < Real.sqrt (T.card : ℝ) := Real.sqrt_pos.2 hTpos
  have hCT :
      4 * chainConstant 1 * Real.sqrt (Real.log (T.card : ℝ)) / Real.sqrt (T.card : ℝ) ≤
        2 * (S.card : ℝ) ^ (-α) := by
    have hnum : 4 * chainConstant 1 * Real.sqrt (Real.log (T.card : ℝ)) ≤
        4 * chainConstant 1 * Real.sqrt (Real.log (S.card : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    calc 4 * chainConstant 1 * Real.sqrt (Real.log (T.card : ℝ)) / Real.sqrt (T.card : ℝ)
        ≤ 4 * chainConstant 1 * Real.sqrt (Real.log (S.card : ℝ)) /
            (Real.sqrt (S.card : ℝ) / 2) :=
          div_le_div₀ (by positivity) hnum (by positivity) (by linarith)
      _ = 2 * (4 * chainConstant 1 * Real.sqrt (Real.log (S.card : ℝ)) /
            Real.sqrt (S.card : ℝ)) := by
          field_simp
      _ ≤ 2 * (S.card : ℝ) ^ (-α) := by linarith
  have h2T : 2 * (T.card : ℝ) / p = 2 * ((T.card : ℝ) / p) := by ring
  calc orderingConditionalMass S
        (fun σ => AgreesOn (exposedWindow P.D b) σ τ)
        (fun σ => b ∈ badRightEndpoints σ)
      ≤ ∑ a ∈ leftEndpointCandidates b, sliceMass T (I a).card (z a) := hstep1
    _ ≤ 2 * (T.card : ℝ) / p +
          4 * chainConstant 1 * Real.sqrt (Real.log (T.card : ℝ)) /
            Real.sqrt (T.card : ℝ) := hstep2
    _ ≤ 4 * (S.card : ℝ) ^ (-α) := by
          rw [h2T]
          linarith

/-- Equation (5.1). -/
theorem equation_5_1
    {α : ℝ} (hα0 : 0 < α) (hαh : α < 1 / 2)
    (P : Section5Parameters α)
    {p : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hreg : Section5Regime P p S)
    (b : Fin S.card)
    (hbfit : paperPos b + 30 * P.D ≤ S.card)
    (J J' : Finset (Fin S.card))
    (hJ : J ⊆ exposedWindow P.D b)
    (hJ' : J' ⊆ exposedWindow P.D b)
    (hne : J ≠ J') :
    letI : NeZero p := ⟨hp.ne_zero⟩
    orderingEventMass S
      (fun σ =>
        b ∈ badRightEndpoints σ ∧
          indexSetSum σ J = indexSetSum σ J') ≤
      8 / (S.card : ℝ) ^ (1 + α) := by
  let : NeZero p := ⟨hp.ne_zero⟩
  have hn50 := section5_card_ge_fiftyD hreg
  have hD : 0 < P.D := section5Parameters_D_pos hα0 hαh P
  have hS2 : 2 ≤ S.card := section5_card_ge_two hα0 hαh hreg
  have hFcard : (exposedWindow P.D b).card = 20 * P.D + 1 :=
    exposedWindow_card b (by omega)
  have hnpos : (0 : ℝ) < S.card := by exact_mod_cast (show 0 < S.card by omega)
  have hcollision :
      orderingEventMass S (fun σ => indexSetSum σ J = indexSetSum σ J') ≤
        2 / (S.card : ℝ) := by
    have hraw := Section5.distinct_index_subset_sums_mass_le S
      (exposedWindow P.D b) J J' hJ hJ' hne (by rw [hFcard]; omega)
    rw [hFcard] at hraw
    refine le_trans hraw ?_
    have hm : S.card ≤ 2 * (S.card - (20 * P.D + 1) + 1) := by omega
    have hmpos : (0 : ℝ) < ((S.card - (20 * P.D + 1) + 1 : ℕ) : ℝ) := by positivity
    rw [div_le_div_iff₀ hmpos hnpos]
    have : (S.card : ℝ) ≤ 2 * ((S.card - (20 * P.D + 1) + 1 : ℕ) : ℝ) := by
      exact_mod_cast hm
    linarith
  have hdetermined : ∀ σ τ : Fin S.card → ZMod p,
      AgreesOn (exposedWindow P.D b) σ τ →
        ((indexSetSum σ J = indexSetSum σ J') ↔
          (indexSetSum τ J = indexSetSum τ J')) :=
    fun σ τ hag => collision_event_determined hJ hJ' hag
  have hfiber : ∀ τ, IsIndexedOrdering S τ →
      indexSetSum τ J = indexSetSum τ J' →
      orderingConditionalMass S
        (fun σ => AgreesOn (exposedWindow P.D b) σ τ)
        (fun σ => b ∈ badRightEndpoints σ) ≤ 4 * (S.card : ℝ) ^ (-α) :=
    fun τ hτ _ => conditional_badEndpoint_mass_le_four hα0 hαh P hp S hreg b hbfit τ hτ
  have hjoint := Section5.joint_event_le_of_agreesOn_fibers S
    (exposedWindow P.D b)
    (fun σ => indexSetSum σ J = indexSetSum σ J')
    (fun σ => b ∈ badRightEndpoints σ)
    (2 / (S.card : ℝ)) (4 * (S.card : ℝ) ^ (-α)) hcollision hdetermined hfiber
    (by positivity)
  have hSα : 0 < (S.card : ℝ) ^ α := Real.rpow_pos_of_pos hnpos α
  calc orderingEventMass S
        (fun σ => b ∈ badRightEndpoints σ ∧ indexSetSum σ J = indexSetSum σ J')
      = orderingEventMass S
          (fun σ => indexSetSum σ J = indexSetSum σ J' ∧ b ∈ badRightEndpoints σ) := by
        unfold orderingEventMass
        exact uniformMass_congr _ _ _ (fun σ _ => and_comm)
    _ ≤ 2 / (S.card : ℝ) * (4 * (S.card : ℝ) ^ (-α)) := hjoint
    _ = 8 / (S.card : ℝ) ^ (1 + α) := by
        rw [Real.rpow_add hnpos, Real.rpow_one, Real.rpow_neg (le_of_lt hnpos)]
        field_simp
        ring

def bad0Parameters {n : ℕ} (D : ℕ) :
    Finset (Fin n × Finset (Fin n) × Finset (Fin n)) := by
  classical
  exact Finset.univ.biUnion fun b =>
    if hfit : paperPos b + 30 * D ≤ n then
      (forwardWindow b (20 * D)).powerset.biUnion fun J =>
        ((forwardWindow b (20 * D)).powerset.filter
          (fun J' => J ≠ J')).image fun J' => (b, J, J')
    else ∅

theorem mem_bad0Parameters {n D : ℕ}
    {b : Fin n} {J J' : Finset (Fin n)} :
    (b, J, J') ∈ bad0Parameters (n := n) D ↔
      paperPos b + 30 * D ≤ n ∧
      J ⊆ forwardWindow b (20 * D) ∧
      J' ⊆ forwardWindow b (20 * D) ∧ J ≠ J' := by
  classical
  unfold bad0Parameters
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨b0, -, hmem⟩
    split_ifs at hmem with hfit
    · rw [Finset.mem_biUnion] at hmem
      obtain ⟨J0, hJ0, hmem⟩ := hmem
      rw [Finset.mem_image] at hmem
      obtain ⟨J1, hJ1, heq⟩ := hmem
      rw [Finset.mem_filter, Finset.mem_powerset] at hJ1
      rw [Finset.mem_powerset] at hJ0
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      exact ⟨hfit, hJ0, hJ1.1, hJ1.2⟩
    · simp at hmem
  · rintro ⟨hfit, hJ, hJ', hne⟩
    refine ⟨b, Finset.mem_univ _, ?_⟩
    rw [dite_eq_left hfit, Finset.mem_biUnion]
    refine ⟨J, Finset.mem_powerset.2 hJ, ?_⟩
    rw [Finset.mem_image]
    exact ⟨J', Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hJ', hne⟩, rfl⟩

theorem bad0Parameters_card_le {n D : ℕ} :
    (bad0Parameters (n := n) D).card ≤ n * 2 ^ (40 * D + 2) := by
  classical
  unfold bad0Parameters
  refine le_trans Finset.card_biUnion_le ?_
  refine le_trans (Finset.sum_le_sum (g := fun _ => 2 ^ (40 * D + 2)) ?_) ?_
  · intro b _
    split_ifs with hfit
    · refine le_trans Finset.card_biUnion_le ?_
      refine le_trans (Finset.sum_le_sum
        (g := fun _ => (forwardWindow b (20 * D)).powerset.card) ?_) ?_
      · intro J _
        exact le_trans Finset.card_image_le (Finset.card_filter_le _ _)
      · rw [Finset.sum_const, smul_eq_mul, Finset.card_powerset]
        have hw := card_forwardWindow_le b (20 * D)
        have hp : 2 ^ (forwardWindow b (20 * D)).card ≤ 2 ^ (20 * D + 1) :=
          Nat.pow_le_pow_right (by norm_num) hw
        calc 2 ^ (forwardWindow b (20 * D)).card * 2 ^ (forwardWindow b (20 * D)).card
            ≤ 2 ^ (20 * D + 1) * 2 ^ (20 * D + 1) := Nat.mul_le_mul hp hp
          _ = 2 ^ (40 * D + 2) := by
              rw [← pow_add]
              congr 1
              omega
    · simp
  · simp

/-- Lemma 5.4. -/
theorem lemma5_4
    {α : ℝ} (hα0 : 0 < α) (hαh : α < 1 / 2)
    (P : Section5Parameters α)
    {p : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hreg : Section5Regime P p S) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    orderingEventMass S (BadEvent0 P.D) ≤ (1 / 100 : ℝ) := by
  let : NeZero p := ⟨hp.ne_zero⟩
  have hcover : ∀ σ ∈ indexedOrderings S, BadEvent0 P.D σ →
      ∃ θ ∈ bad0Parameters (n := S.card) P.D,
        θ.1 ∈ badRightEndpoints σ ∧
          indexSetSum σ θ.2.1 = indexSetSum σ θ.2.2 := by
    intro σ _ h0
    rcases h0 with ⟨b, hb, hbfit, J, J', hJ, hJ', hne, hsum⟩
    exact ⟨(b, J, J'), mem_bad0Parameters.2 ⟨hbfit, hJ, hJ', hne⟩, hb, hsum⟩
  have hbound : ∀ θ ∈ bad0Parameters (n := S.card) P.D,
      uniformMass (indexedOrderings S)
        (fun σ => θ.1 ∈ badRightEndpoints σ ∧
          indexSetSum σ θ.2.1 = indexSetSum σ θ.2.2) ≤
        8 / (S.card : ℝ) ^ (1 + α) := by
    rintro ⟨b, J, J'⟩ hθ
    obtain ⟨hbfit, hJ, hJ', hne⟩ := mem_bad0Parameters.1 hθ
    exact equation_5_1 hα0 hαh P hp S hreg b hbfit J J' hJ hJ' hne
  have hmass := Section5.witness_union_bound (indexedOrderings S)
    (bad0Parameters (n := S.card) P.D) (BadEvent0 P.D)
    (fun θ σ => θ.1 ∈ badRightEndpoints σ ∧
      indexSetSum σ θ.2.1 = indexSetSum σ θ.2.2)
    (8 / (S.card : ℝ) ^ (1 + α)) hcover hbound
  have hΘ : (bad0Parameters (n := S.card) P.D).card ≤
      S.card * 2 ^ (40 * P.D + 2) := bad0Parameters_card_le
  have hS2 : 2 ≤ S.card := section5_card_ge_two hα0 hαh hreg
  have hnpos : (0 : ℝ) < S.card := by exact_mod_cast (show 0 < S.card by omega)
  have hpow := section5_Calpha_power hα0 P
  have hmono := Real.rpow_le_rpow (le_of_lt P.Cα_pos) hreg.2.1 (le_of_lt hα0)
  have hden : (10 ^ 4 : ℝ) * 2 ^ (40 * P.D) ≤ (S.card : ℝ) ^ α :=
    le_trans hpow hmono
  have hSα : 0 < (S.card : ℝ) ^ α := Real.rpow_pos_of_pos hnpos α
  have h8 : 0 ≤ 8 / (S.card : ℝ) ^ (1 + α) := by positivity
  have h2pos : (0 : ℝ) < 2 ^ (40 * P.D) := by positivity
  calc orderingEventMass S (BadEvent0 P.D)
      ≤ ((bad0Parameters (n := S.card) P.D).card : ℝ) *
          (8 / (S.card : ℝ) ^ (1 + α)) := hmass
    _ ≤ ((S.card * 2 ^ (40 * P.D + 2) : ℕ) : ℝ) *
          (8 / (S.card : ℝ) ^ (1 + α)) := by
        apply mul_le_mul_of_nonneg_right _ h8
        exact_mod_cast hΘ
    _ = (2 : ℝ) ^ (40 * P.D) * 32 / (S.card : ℝ) ^ α := by
        rw [Real.rpow_add hnpos, Real.rpow_one]
        push_cast
        rw [pow_add]
        field_simp
        ring
    _ ≤ 1 / 100 := by
        rw [div_le_div_iff₀ hSα (by norm_num)]
        linarith

end

end GrahamRearrangement
