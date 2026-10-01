module

public import GrahamRearrangement.Rearrangement.Lemma54

@[expose] public section

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Lemma 5.2
-/

noncomputable section

/-- Monotonicity of uniform mass, with both decidability instances left to
unification (so that it applies whatever instances the events carry). -/
private theorem l52_uniformMass_mono_on {Ω : Type*} [DecidableEq Ω] (space : Finset Ω)
    {E F : Ω → Prop} {iE : DecidablePred E} {iF : DecidablePred F}
    (hEF : ∀ ω ∈ space, E ω → F ω) :
    @uniformMass Ω _ space E iE ≤ @uniformMass Ω _ space F iF :=
  uniformMass_mono_on space E F hEF

private theorem l52_mem_forwardWindow {n r : ℕ} {b x : Fin n} :
    x ∈ forwardWindow b r ↔ b.val ≤ x.val ∧ x.val ≤ b.val + r := by
  unfold forwardWindow
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

private theorem l52_mem_indexHalfOpen {n : ℕ} {a b x : Fin n} :
    x ∈ indexHalfOpen a b ↔ a.val ≤ x.val ∧ x.val < b.val := by
  unfold indexHalfOpen
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

private theorem l52_mem_indexInterval {n : ℕ} {a b x : Fin n} :
    x ∈ indexInterval a b ↔ a.val ≤ x.val ∧ x.val ≤ b.val := by
  unfold indexInterval
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

/-- Splitting a paper interval sum `Σ[a,d]` at `c < d`, as `Σ[a,c] + Σ[c+1,d]`. -/
private theorem l52_indexedIntervalSum_split {n p : ℕ} (σ : Fin n → ZMod p)
    (a c d c' : Fin n) (hac : a.val ≤ c.val) (hcd : c.val < d.val)
    (hc' : c'.val = c.val + 1) :
    indexedIntervalSum σ a d =
      indexedIntervalSum σ a c + indexedIntervalSum σ c' d := by
  unfold indexedIntervalSum
  rw [hc']
  have hsplit : Finset.Icc a.val d.val =
      Finset.Icc a.val c.val ∪ Finset.Icc (c.val + 1) d.val := by
    ext x
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  rw [hsplit, Finset.sum_union]
  rw [Finset.disjoint_left]
  intro x hx hy
  simp only [Finset.mem_Icc] at hx hy
  omega

def Lemma52Witness {n p D : ℕ}
    (σ : Fin n → ZMod p) (b₀ : Fin n)
    (b : Fin D → Fin n) : Prop :=
  (∀ i, paperPos b₀ < paperPos (b i) ∧
    paperPos (b i) ≤ paperPos b₀ + 20 * D) ∧
  ∃ a : Fin D → Fin n,
    StrictMono a ∧
    (∀ i, paperPos (a i) < paperPos b₀) ∧
    ∀ i, indexedIntervalSum σ (a i) (b i) = 0

noncomputable instance {n p D : ℕ} (b₀ : Fin n) (b : Fin D → Fin n) :
    DecidablePred fun σ : Fin n → ZMod p => Lemma52Witness σ b₀ b :=
  Classical.decPred _

def lemma52ChoiceSet {n : ℕ} (b : Fin n) (D : ℕ) :
    Finset (Fin n) :=
  (forwardWindow b (20 * D)).erase b

theorem mem_lemma52ChoiceSet {n D : ℕ} {b x : Fin n} :
    x ∈ lemma52ChoiceSet b D ↔
      paperPos b < paperPos x ∧
        paperPos x ≤ paperPos b + 20 * D := by
  simp [lemma52ChoiceSet,forwardWindow,paperPos]
  omega

theorem card_lemma52ChoiceSet_le {n D : ℕ} (b : Fin n) :
    (lemma52ChoiceSet b D).card ≤ 20 * D := by
  have hb : b ∈ forwardWindow b (20 * D) := by
    simp [forwardWindow]
  unfold lemma52ChoiceSet
  rw [Finset.card_erase_of_mem hb]
  have hw := card_forwardWindow_le b (20 * D)
  omega

def lemma52Parameters (n D : ℕ) :
    Finset (Fin n × (Fin D → Fin n)) := by
  classical
  exact Finset.univ.biUnion fun b =>
    if hfit : paperPos b + 30 * D ≤ n then
      (Fintype.piFinset fun _ : Fin D => lemma52ChoiceSet b D).image
        (fun v => (b,v))
    else ∅

theorem mem_lemma52Parameters {n D : ℕ}
    {b : Fin n} {v : Fin D → Fin n} :
    (b,v) ∈ lemma52Parameters n D ↔
      paperPos b + 30 * D ≤ n ∧
      ∀ i, paperPos b < paperPos (v i) ∧
        paperPos (v i) ≤ paperPos b + 20 * D := by
  classical
  unfold lemma52Parameters
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨b0, -, hmem⟩
    split_ifs at hmem with hfit
    · rw [Finset.mem_image] at hmem
      obtain ⟨w, hw, heq⟩ := hmem
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      rw [Fintype.mem_piFinset] at hw
      exact ⟨hfit, fun i => mem_lemma52ChoiceSet.1 (hw i)⟩
    · simp at hmem
  · rintro ⟨hfit, hv⟩
    refine ⟨b, Finset.mem_univ _, ?_⟩
    rw [dite_eq_left hfit, Finset.mem_image]
    exact ⟨v, Fintype.mem_piFinset.2 (fun i => mem_lemma52ChoiceSet.2 (hv i)), rfl⟩

theorem lemma52Parameters_card_le (n D : ℕ) :
    (lemma52Parameters n D).card ≤ n * (20 * D) ^ D := by
  classical
  unfold lemma52Parameters
  refine le_trans Finset.card_biUnion_le ?_
  refine le_trans (Finset.sum_le_sum (g := fun _ => (20 * D) ^ D) ?_) ?_
  · intro b _
    split_ifs with hfit
    · refine le_trans Finset.card_image_le ?_
      rw [Fintype.card_piFinset]
      calc ∏ _i : Fin D, (lemma52ChoiceSet b D).card
          ≤ (20 * D) ^ (Finset.univ : Finset (Fin D)).card :=
            Finset.prod_le_pow_card _ _ _ (fun i _ => card_lemma52ChoiceSet_le b)
        _ = (20 * D) ^ D := by simp
    · simp
  · simp

theorem badEvent2_core_has_witness
    {n p D : ℕ} (hD : 0 < D)
    (σ : Fin n → ZMod p)
    (h2 : BadEvent2 D σ)
    (h0 : ¬ BadEvent0 D σ)
    (h1 : ¬ BadEvent1 D σ) :
    ∃ θ ∈ lemma52Parameters n D,
      θ.1 ∈ badRightEndpoints σ ∧
      Lemma52Witness σ θ.1 θ.2 := by
  classical
  obtain ⟨b₀, hb₀, b, hbinj, hbmem, hbwin⟩ :=
    Section5.dense_window_extract (badRightEndpoints σ) hD h2
  have hb₀fit : paperPos b₀ + 30 * D ≤ n := by
    by_contra h
    exact h1 ⟨b₀, hb₀, by omega⟩
  choose a ha2 hab hzero using
    fun i => (mem_badRightEndpoints_iff σ (b i)).1 (hbmem i)
  have hwin : ∀ i, b₀.val < (b i).val ∧ (b i).val ≤ b₀.val + 20 * D := by
    intro i
    have := hbwin i
    simp only [paperPos] at this
    omega
  have habv : ∀ i, 1 ≤ (a i).val ∧ (a i).val < (b i).val := by
    intro i
    have h2' := ha2 i
    have h3' := hab i
    simp only [paperPos] at h2' h3'
    omega
  -- A nonempty zero-sum interval inside the window contradicts `¬ B₀`.
  have hkey : ∀ c d : Fin n, b₀.val ≤ c.val → c.val ≤ d.val →
      d.val ≤ b₀.val + 20 * D → indexedIntervalSum σ c d ≠ 0 := by
    intro c d hc hcd hd hzero'
    apply h0
    refine ⟨b₀, hb₀, hb₀fit, indexInterval c d, ∅, ?_, Finset.empty_subset _, ?_, ?_⟩
    · intro x hx
      rw [l52_mem_indexInterval] at hx
      rw [l52_mem_forwardWindow]
      omega
    · intro h
      have hc : c ∈ indexInterval c d := by
        rw [l52_mem_indexInterval]
        omega
      rw [h] at hc
      simp at hc
    · rw [indexSetSum_indexInterval, hzero']
      simp [indexSetSum]
  have hinj_aux : ∀ i j, a i = a j → (b i).val < (b j).val → False := by
    intro i j hij hlt
    let c' : Fin n := ⟨(b i).val + 1, by have := (b j).isLt; omega⟩
    have hsplit := l52_indexedIntervalSum_split σ (a j) (b i) (b j) c'
      (by rw [← hij]; exact le_of_lt (habv i).2) hlt rfl
    rw [hzero j, ← hij, hzero i, zero_add] at hsplit
    exact hkey c' (b j) (by simp only [c']; have := hwin i; omega)
      (by simp only [c']; omega) (hwin j).2 hsplit.symm
  have hainj : Function.Injective a := by
    intro i j hij
    by_contra hne
    have hbij : b i ≠ b j := fun h => hne (hbinj h)
    have hval : (b i).val ≠ (b j).val := fun h => hbij (Fin.ext h)
    rcases Nat.lt_or_gt_of_ne hval with hlt | hlt
    · exact hinj_aux i j hij hlt
    · exact hinj_aux j i hij.symm hlt
  have hab₀ : ∀ i, paperPos (a i) < paperPos b₀ := by
    intro i
    by_contra hnot
    simp only [paperPos, not_lt] at hnot
    exact hkey (a i) (b i) (by omega) (le_of_lt (habv i).2) (hwin i).2 (hzero i)
  obtain ⟨ρ, hmono⟩ := Section5.exists_sorting_perm a hainj
  refine ⟨(b₀, b ∘ ρ), ?_, hb₀, ?_⟩
  · exact mem_lemma52Parameters.mpr ⟨hb₀fit, fun i => hbwin (ρ i)⟩
  · exact ⟨fun i => hbwin (ρ i), a ∘ ρ, hmono, fun i => hab₀ (ρ i),
      fun i => hzero (ρ i)⟩

def lemma52PrefixTuples {n k : ℕ} (b₀ : Fin n) :
    Finset (Fin k → Fin n) :=
  Finset.univ.filter fun a =>
    StrictMono a ∧ ∀ i, paperPos (a i) < paperPos b₀

def lemma52PrefixIntervals {n k : ℕ}
    (b₀ : Fin n) (a : Fin k → Fin n) :
    Fin k → Finset (Fin n) :=
  fun i => indexHalfOpen (a (reverseIndex k i)) b₀

def lemma52PrefixSizes {n k : ℕ}
    (b₀ : Fin n) (a : Fin k → Fin n) :
    Fin k → ℕ :=
  fun i => (lemma52PrefixIntervals b₀ a i).card

theorem lemma52PrefixSizes_valid {n k : ℕ}
    (b₀ : Fin n) (Tcard : ℕ) (hroom : b₀.val < Tcard)
    {a : Fin k → Fin n} (ha : a ∈ lemma52PrefixTuples b₀) :
    IsChainSizeTuple Tcard (lemma52PrefixSizes b₀ a) := by
  have hdata := (Finset.mem_filter.mp ha).2
  have hlt : ∀ i, (a (reverseIndex k i)).val < b₀.val := by
    intro i
    have hai := hdata.2 (reverseIndex k i)
    simp only [paperPos] at hai
    omega
  have hsize : ∀ i, lemma52PrefixSizes b₀ a i = b₀.val - (a (reverseIndex k i)).val := by
    intro i
    exact card_indexHalfOpen _ _ (le_of_lt (hlt i))
  constructor
  · intro i j hij
    rw [hsize, hsize]
    have hrev : reverseIndex k j < reverseIndex k i := by
      rw [Fin.lt_def, reverseIndex_apply_val, reverseIndex_apply_val]
      rw [Fin.lt_def] at hij
      have := j.isLt
      omega
    have haa := hdata.1 hrev
    rw [Fin.lt_def] at haa
    have := hlt i
    omega
  · intro i
    rw [hsize]
    have := hlt i
    omega

theorem lemma52PrefixIntervals_nested {n k : ℕ}
    (b₀ : Fin n) {a : Fin k → Fin n}
    (ha : a ∈ lemma52PrefixTuples b₀) :
    ∀ i j, i ≤ j →
      lemma52PrefixIntervals b₀ a i ⊆
        lemma52PrefixIntervals b₀ a j := by
  intro i j hij x hx
  have hdata := (Finset.mem_filter.mp ha).2
  have hrev : reverseIndex k j ≤ reverseIndex k i := by
    rw [Fin.le_def, reverseIndex_apply_val, reverseIndex_apply_val]
    rw [Fin.le_def] at hij
    omega
  have haa := hdata.1.monotone hrev
  rw [Fin.le_def] at haa
  unfold lemma52PrefixIntervals at hx ⊢
  rw [l52_mem_indexHalfOpen] at hx ⊢
  omega

theorem lemma52PrefixSizes_injective {n k : ℕ}
    (b₀ : Fin n) :
    Set.InjOn (lemma52PrefixSizes b₀)
      (lemma52PrefixTuples (k := k) b₀ : Set (Fin k → Fin n)) := by
  intro a ha a' ha' h
  funext i
  let r := reverseIndex k i
  have hai := (Finset.mem_filter.mp ha).2.2 i
  have hai' := (Finset.mem_filter.mp ha').2.2 i
  have hle : (a i).val ≤ b₀.val := by
    simp [paperPos] at hai
    omega
  have hle' : (a' i).val ≤ b₀.val := by
    simp [paperPos] at hai'
    omega
  have hr := congrFun h r
  have hri :
      lemma52PrefixSizes b₀ a r = b₀.val - (a i).val := by
    simpa [lemma52PrefixSizes,lemma52PrefixIntervals,r,
      reverseIndex_involutive] using
      card_indexHalfOpen (a i) b₀ hle
  have hri' :
      lemma52PrefixSizes b₀ a' r = b₀.val - (a' i).val := by
    simpa [lemma52PrefixSizes,lemma52PrefixIntervals,r,
      reverseIndex_involutive] using
      card_indexHalfOpen (a' i) b₀ hle'
  rw [hri,hri'] at hr
  exact Fin.ext (by omega)

theorem lemma52_prefix_chain_bound
    {p k : ℕ} [NeZero p]
    (S : Finset (ZMod p))
    (τ : Fin S.card → ZMod p) (hτ : IsIndexedOrdering S τ)
    (F : Finset (Fin S.card)) (b₀ : Fin S.card)
    (hFright : ∀ x ∈ F, b₀.val ≤ x.val)
    (hroom : b₀.val < (S \ indexImageSet τ F).card)
    (target : Fin k → ZMod p)
    (C : ℝ) (hC : 0 ≤ C)
    (hchain :
      ∀ m : Fin k → ℕ, IsChainSizeTuple (S \ indexImageSet τ F).card m →
        ∀ z : Fin k → ZMod p, chainMass (S \ indexImageSet τ F) m z ≤
          chainUpperBound p (S \ indexImageSet τ F).card C m) :
    orderingConditionalMass S
      (fun σ => AgreesOn F σ τ)
      (fun σ =>
        ∃ a : Fin k → Fin S.card,
          StrictMono a ∧
          (∀ i, paperPos (a i) < paperPos b₀) ∧
          ∀ i, indexSetSum σ (indexHalfOpen (a i) b₀) = target i) ≤
      lemma43LHS p (S \ indexImageSet τ F).card k C := by
  classical
  let A := lemma52PrefixTuples (k := k) b₀
  let I := fun a : Fin k → Fin S.card => lemma52PrefixIntervals b₀ a
  let m := fun a : Fin k → Fin S.card => lemma52PrefixSizes b₀ a
  let z := fun _a : Fin k → Fin S.card => fun i => target (reverseIndex k i)
  have hdisj : ∀ a ∈ A, ∀ i, Disjoint F (I a i) := by
    intro a _ i
    rw [Finset.disjoint_left]
    intro x hxF hxI
    have hxright := hFright x hxF
    simp only [I, lemma52PrefixIntervals] at hxI
    rw [l52_mem_indexHalfOpen] at hxI
    omega
  have hnested : ∀ a ∈ A, ∀ i j, i ≤ j → I a i ⊆ I a j :=
    fun a ha => lemma52PrefixIntervals_nested b₀ ha
  have hvalid : ∀ a ∈ A, IsChainSizeTuple (S \ indexImageSet τ F).card (m a) :=
    fun a ha => lemma52PrefixSizes_valid b₀ _ hroom ha
  have hinj : Set.InjOn m A := lemma52PrefixSizes_injective b₀
  have hchain' : ∀ a ∈ A,
      chainMass (S \ indexImageSet τ F) (m a) (z a) ≤
        chainUpperBound p (S \ indexImageSet τ F).card C (m a) :=
    fun a ha => hchain (m a) (hvalid a ha) (z a)
  have hgeneric :=
    Section5.conditional_chain_witness_union_bound
      S τ hτ F A I m z C hdisj hnested (fun _ _ _ => rfl) hvalid hinj hchain' hC
  refine le_trans ?_ hgeneric
  unfold orderingConditionalMass uniformConditionalMass
  apply l52_uniformMass_mono_on
  intro σ _ h
  rcases h with ⟨a, hmono, hbefore, hsum⟩
  refine ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmono, hbefore⟩, ?_⟩
  intro i
  exact hsum (reverseIndex k i)

theorem lemma52_fixed_parameter_mass_le
    {α : ℝ} (hα0 : 0 < α) (hαh : α < 1 / 2)
    (P : Section5Parameters α)
    {p : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hreg : Section5Regime P p S)
    (θ : Fin S.card × (Fin P.D → Fin S.card))
    (hθ : θ ∈ lemma52Parameters S.card P.D)
    (hbfit : paperPos θ.1 + 30 * P.D ≤ S.card) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    orderingEventMass S
      (fun σ => Lemma52Witness σ θ.1 θ.2) ≤
      (P.D + 1 : ℝ) * (2 : ℝ) ^ P.D /
        (S.card : ℝ) ^ 3 := by
  let : NeZero p := ⟨hp.ne_zero⟩
  have hn50 := section5_card_ge_fiftyD hreg
  have hD : 0 < P.D := section5Parameters_D_pos hα0 hαh P
  have hS2 : 2 ≤ S.card := section5_card_ge_two hα0 hαh hreg
  have hbval : θ.1.val + 1 + 30 * P.D ≤ S.card := by
    simpa only [paperPos] using hbfit
  have hfiber :
      ∀ τ, IsIndexedOrdering S τ →
        orderingConditionalMass S
          (fun σ => AgreesOn (forwardWindow θ.1 (20 * P.D)) σ τ)
          (fun σ => Lemma52Witness σ θ.1 θ.2) ≤
        (P.D + 1 : ℝ) * (2 : ℝ) ^ P.D / (S.card : ℝ) ^ 3 := by
    intro τ hτ
    have hFcard : (forwardWindow θ.1 (20 * P.D)).card = 20 * P.D + 1 :=
      card_forwardWindow_eq θ.1 (20 * P.D) (by omega)
    have himage := Section5.exposed_image_card S hτ (forwardWindow θ.1 (20 * P.D))
    have hsub := Section5.exposedImage_subset S hτ (forwardWindow θ.1 (20 * P.D))
    have hTcard : (S \ indexImageSet τ (forwardWindow θ.1 (20 * P.D))).card =
        S.card - (20 * P.D + 1) := by
      rw [Finset.card_sdiff_of_subset hsub, himage, hFcard]
    set T := S \ indexImageSet τ (forwardWindow θ.1 (20 * P.D)) with hT
    have hT2 : 2 ≤ T.card := by rw [hTcard]; omega
    have hhalf : S.card / 2 ≤ T.card := by rw [hTcard]; omega
    have hTle : T.card ≤ S.card := by rw [hTcard]; omega
    let target : Fin P.D → ZMod p :=
      fun i => - indexSetSum τ (indexInterval θ.1 (θ.2 i))
    have hchain :
        ∀ m : Fin P.D → ℕ, IsChainSizeTuple T.card m →
          ∀ z : Fin P.D → ZMod p,
            chainMass T m z ≤ chainUpperBound p T.card (chainConstant P.D) m :=
      fun m hm z => chainConstant_spec P.D hD p hp T hT2 m hm z
    have hFright : ∀ x ∈ forwardWindow θ.1 (20 * P.D), θ.1.val ≤ x.val := by
      intro x hx
      rw [l52_mem_forwardWindow] at hx
      exact hx.1
    have hroom : θ.1.val < T.card := by rw [hTcard]; omega
    have hcond :
        orderingConditionalMass S
          (fun σ => AgreesOn (forwardWindow θ.1 (20 * P.D)) σ τ)
          (fun σ => Lemma52Witness σ θ.1 θ.2) ≤
          lemma43LHS p T.card P.D (chainConstant P.D) := by
      refine le_trans ?_
        (lemma52_prefix_chain_bound S τ hτ (forwardWindow θ.1 (20 * P.D)) θ.1
          hFright hroom target (chainConstant P.D) (chainConstant_pos P.D).le hchain)
      unfold orderingConditionalMass uniformConditionalMass
      apply l52_uniformMass_mono_on
      intro σ hσ hw
      have hag := (Finset.mem_filter.1 hσ).2
      rcases hw with ⟨hbwin, a, hmono, hab₀, hzero⟩
      refine ⟨a, hmono, hab₀, ?_⟩
      intro i
      have hab1 : (a i).val < θ.1.val := by
        have := hab₀ i
        simp only [paperPos] at this
        omega
      have hb0b : θ.1.val < (θ.2 i).val ∧ (θ.2 i).val ≤ θ.1.val + 20 * P.D := by
        have := hbwin i
        simp only [paperPos] at this
        omega
      have hz := hzero i
      rw [← indexSetSum_indexInterval] at hz
      have hunion : indexInterval (a i) (θ.2 i) =
          indexHalfOpen (a i) θ.1 ∪ indexInterval θ.1 (θ.2 i) := by
        ext x
        rw [Finset.mem_union, l52_mem_indexInterval, l52_mem_indexHalfOpen,
          l52_mem_indexInterval]
        omega
      have hdisj : Disjoint (indexHalfOpen (a i) θ.1) (indexInterval θ.1 (θ.2 i)) := by
        rw [Finset.disjoint_left]
        intro x hx hy
        rw [l52_mem_indexHalfOpen] at hx
        rw [l52_mem_indexInterval] at hy
        omega
      rw [hunion] at hz
      unfold indexSetSum at hz
      rw [Finset.sum_union hdisj] at hz
      have htail : ∑ x ∈ indexInterval θ.1 (θ.2 i), σ x =
          indexSetSum τ (indexInterval θ.1 (θ.2 i)) := by
        unfold indexSetSum
        apply Finset.sum_congr rfl
        intro x hx
        apply hag x
        rw [l52_mem_forwardWindow]
        rw [l52_mem_indexInterval] at hx
        omega
      rw [htail] at hz
      exact eq_neg_of_add_eq_zero_left hz
    have h43 :=
      lemma4_3 P.D hD (chainConstant P.D) (chainConstant_pos P.D) p hp T.card hT2
    have hCpos := chainConstant_pos P.D
    have hbase : lemma43Base p T.card (chainConstant P.D) ≤ 2 * (S.card : ℝ) ^ (-α) :=
      Section5.half_ground_lemma43Base_le hS2 hhalf hTle (le_of_lt hCpos)
        (section5_card_over_p hα0 hαh hp hreg)
        (section5_chainConstant_bound hreg P.D (Or.inr rfl))
    have hbase0 : 0 ≤ lemma43Base p T.card (chainConstant P.D) := by
      unfold lemma43Base
      positivity
    have hpow : (2 * (S.card : ℝ) ^ (-α)) ^ P.D ≤ (2 : ℝ) ^ P.D / (S.card : ℝ) ^ 3 :=
      Section5.two_neg_alpha_pow_le_cube (by omega) hα0
        (section5Parameters_alphaD hα0 P)
    have hDnn : (0 : ℝ) ≤ (P.D : ℝ) + 1 := by positivity
    calc orderingConditionalMass S
          (fun σ => AgreesOn (forwardWindow θ.1 (20 * P.D)) σ τ)
          (fun σ => Lemma52Witness σ θ.1 θ.2)
        ≤ lemma43LHS p T.card P.D (chainConstant P.D) := hcond
      _ ≤ lemma43RHS p T.card P.D (chainConstant P.D) := h43
      _ = (P.D + 1 : ℝ) * (lemma43Base p T.card (chainConstant P.D)) ^ P.D := by
          unfold lemma43RHS lemma43Base
          rfl
      _ ≤ (P.D + 1 : ℝ) * (2 * (S.card : ℝ) ^ (-α)) ^ P.D :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbase0 hbase P.D) hDnn
      _ ≤ (P.D + 1 : ℝ) * ((2 : ℝ) ^ P.D / (S.card : ℝ) ^ 3) :=
          mul_le_mul_of_nonneg_left hpow hDnn
      _ = (P.D + 1 : ℝ) * (2 : ℝ) ^ P.D / (S.card : ℝ) ^ 3 := by ring
  exact Section5.event_le_of_agreesOn_fibers S (forwardWindow θ.1 (20 * P.D))
    (fun σ => Lemma52Witness σ θ.1 θ.2) _ hfiber

/-- Lemma 5.2. -/
theorem lemma5_2
    {α : ℝ} (hα0 : 0 < α) (hαh : α < 1 / 2)
    (P : Section5Parameters α)
    {p : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hreg : Section5Regime P p S) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    orderingEventMass S (BadEvent2 P.D) ≤ (3 / 100 : ℝ) := by
  let : NeZero p := ⟨hp.ne_zero⟩
  have hD := section5Parameters_D_pos hα0 hαh P
  have hcover : ∀ σ ∈ indexedOrderings S,
      (BadEvent2 P.D σ ∧ ¬ BadEvent0 P.D σ ∧ ¬ BadEvent1 P.D σ) →
        ∃ θ ∈ lemma52Parameters S.card P.D, Lemma52Witness σ θ.1 θ.2 := by
    intro σ _ hcore
    obtain ⟨θ, hθ, _, hw⟩ :=
      badEvent2_core_has_witness hD σ hcore.1 hcore.2.1 hcore.2.2
    exact ⟨θ, hθ, hw⟩
  have hparam : ∀ θ ∈ lemma52Parameters S.card P.D,
      uniformMass (indexedOrderings S) (fun σ => Lemma52Witness σ θ.1 θ.2) ≤
        (P.D + 1 : ℝ) * (2 : ℝ) ^ P.D / (S.card : ℝ) ^ 3 := by
    intro θ hθ
    have hb : paperPos θ.1 + 30 * P.D ≤ S.card := (mem_lemma52Parameters.mp hθ).1
    exact lemma52_fixed_parameter_mass_le hα0 hαh P hp S hreg θ hθ hb
  have hCore := Section5.witness_union_bound (indexedOrderings S)
    (lemma52Parameters S.card P.D)
    (fun σ => BadEvent2 P.D σ ∧ ¬ BadEvent0 P.D σ ∧ ¬ BadEvent1 P.D σ)
    (fun θ σ => Lemma52Witness σ θ.1 θ.2)
    ((P.D + 1 : ℝ) * (2 : ℝ) ^ P.D / (S.card : ℝ) ^ 3) hcover hparam
  have hcount := lemma52Parameters_card_le S.card P.D
  have hS2 : 2 ≤ S.card := section5_card_ge_two hα0 hαh hreg
  have hnpos : (0 : ℝ) < S.card := by exact_mod_cast (show 0 < S.card by omega)
  have hCore100 :
      uniformMass (indexedOrderings S)
        (fun σ => BadEvent2 P.D σ ∧ ¬ BadEvent0 P.D σ ∧ ¬ BadEvent1 P.D σ) ≤
        (1 / 100 : ℝ) := by
    refine le_trans hCore ?_
    have hnC := hreg.2.1
    have h40 := P.hundred_ge_40
    have h100 := P.second_ge_100
    have hC2 := P.Cα_second
    have hD7 : 7 ≤ P.D := by
      rw [P.D_eq]
      exact section5D_ge_seven hα0 hαh
    have hDplus : (P.D + 1 : ℝ) ≤ (5 * P.D : ℝ) ^ (2 * P.D) :=
      Auxiliary.D_plus_one_le_fiveD_pow P.D hD7
    have hX : 100 * (5 * P.D : ℝ) ^ (2 * P.D) ≤ S.card := by linarith
    have hY : (40 * P.D : ℝ) ^ P.D ≤ S.card := by linarith
    have hkey : 100 * ((P.D + 1 : ℝ) * (40 * P.D : ℝ) ^ P.D) ≤ (S.card : ℝ) ^ 2 := by
      calc 100 * ((P.D + 1 : ℝ) * (40 * P.D : ℝ) ^ P.D)
          ≤ 100 * ((5 * P.D : ℝ) ^ (2 * P.D) * (40 * P.D : ℝ) ^ P.D) := by
            gcongr
        _ = (100 * (5 * P.D : ℝ) ^ (2 * P.D)) * (40 * P.D : ℝ) ^ P.D := by ring
        _ ≤ (S.card : ℝ) * (S.card : ℝ) :=
            mul_le_mul hX hY (by positivity) (by positivity)
        _ = (S.card : ℝ) ^ 2 := by ring
    have hw0 : 0 ≤ (P.D + 1 : ℝ) * (2 : ℝ) ^ P.D / (S.card : ℝ) ^ 3 := by positivity
    have h40eq : (40 * (P.D : ℝ)) ^ P.D = (20 * (P.D : ℝ)) ^ P.D * 2 ^ P.D := by
      rw [← mul_pow]
      ring_nf
    calc ((lemma52Parameters S.card P.D).card : ℝ) *
          ((P.D + 1 : ℝ) * (2 : ℝ) ^ P.D / (S.card : ℝ) ^ 3)
        ≤ ((S.card * (20 * P.D) ^ P.D : ℕ) : ℝ) *
          ((P.D + 1 : ℝ) * (2 : ℝ) ^ P.D / (S.card : ℝ) ^ 3) := by
          apply mul_le_mul_of_nonneg_right _ hw0
          exact_mod_cast hcount
      _ = (P.D + 1 : ℝ) * (40 * P.D : ℝ) ^ P.D / (S.card : ℝ) ^ 2 := by
          rw [h40eq]
          push_cast
          field_simp
      _ ≤ (1 / 100 : ℝ) := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          linarith
  have h0 := lemma5_4 hα0 hαh P hp S hreg
  have h1 := lemma5_1 hα0 hαh P hp S hreg
  have htotal := uniformMass_le_two_exceptions (indexedOrderings S)
    (BadEvent2 P.D) (BadEvent0 P.D) (BadEvent1 P.D) (1 / 100 : ℝ) hCore100
  unfold orderingEventMass at h0 h1 ⊢
  linarith

end

end GrahamRearrangement
