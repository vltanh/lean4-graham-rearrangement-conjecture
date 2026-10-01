module

public import GrahamRearrangement.Rearrangement.Lemma54

@[expose] public section

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Lemma 5.2
-/

noncomputable section

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
  sorry

theorem lemma52Parameters_card_le (n D : ℕ) :
    (lemma52Parameters n D).card ≤ n * (20 * D) ^ D := by
  sorry

theorem badEvent2_core_has_witness
    {n p D : ℕ} (hD : 0 < D)
    (σ : Fin n → ZMod p)
    (h2 : BadEvent2 D σ)
    (h0 : ¬ BadEvent0 D σ)
    (h1 : ¬ BadEvent1 D σ) :
    ∃ θ ∈ lemma52Parameters n D,
      θ.1 ∈ badRightEndpoints σ ∧
      Lemma52Witness σ θ.1 θ.2 := by
  sorry

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
  sorry

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
  sorry

theorem lemma52PrefixIntervals_nested {n k : ℕ}
    (b₀ : Fin n) {a : Fin k → Fin n}
    (ha : a ∈ lemma52PrefixTuples b₀) :
    ∀ i j, i ≤ j →
      lemma52PrefixIntervals b₀ a i ⊆
        lemma52PrefixIntervals b₀ a j := by
  sorry

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
    (C : ℝ)
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
  sorry

/-- Lemma 5.2. -/
theorem lemma5_2
    {α : ℝ} (hα0 : 0 < α) (hαh : α < 1 / 2)
    (P : Section5Parameters α)
    {p : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hreg : Section5Regime P p S) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    orderingEventMass S (BadEvent2 P.D) ≤ (3 / 100 : ℝ) := by
  sorry

end

end GrahamRearrangement
