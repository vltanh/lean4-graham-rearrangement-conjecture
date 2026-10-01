module

public import GrahamRearrangement.Rearrangement.Lemma51

@[expose] public section

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Lemma 5.4 and equation (5.1)
-/

noncomputable section

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
  sorry

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
  sorry

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
  sorry

theorem bad0Parameters_card_le {n D : ℕ} :
    (bad0Parameters (n := n) D).card ≤ n * 2 ^ (40 * D + 2) := by
  sorry

/-- Lemma 5.4. -/
theorem lemma5_4
    {α : ℝ} (hα0 : 0 < α) (hαh : α < 1 / 2)
    (P : Section5Parameters α)
    {p : ℕ} (hp : p.Prime)
    (S : Finset (ZMod p)) (hreg : Section5Regime P p S) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    orderingEventMass S (BadEvent0 P.D) ≤ (1 / 100 : ℝ) := by
  sorry

end

end GrahamRearrangement
