module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.ZMod.Defs
import GrahamRearrangement

/-!
# Proofs of the results of `Challenge.lean`

Each theorem restates the corresponding theorem of `Challenge.lean` verbatim and proves it from
the formalization in `GrahamRearrangement/`, translating between the paper's vocabulary used
there and the Mathlib-only statements of the challenge.
-/

@[expose] public section

open Finset

namespace PhamSauermann

/-- The paper's `ℙ[Σ(R) = z]` for a uniformly random `m`-subset `R` of `S`, in the
challenge's vocabulary. -/
private theorem sliceMass_eq {p : ℕ} [NeZero p] (S : Finset (ZMod p)) (m : ℕ) (z : ZMod p) :
    GrahamRearrangement.sliceMass S m z =
      (#{R ∈ S.powersetCard m | ∑ x ∈ R, x = z} : ℝ) / (#S).choose m := by
  unfold GrahamRearrangement.sliceMass GrahamRearrangement.uniformMass
  rw [Finset.card_powersetCard]
  congr 2

/-- **Theorem 1.2** (Pham–Sauermann). For every `0 < α < 1` there is a constant `C_α > 0`
such that, for every prime `p`, every subset `S ⊆ ℤ_p ∖ {0}` with `C_α ≤ |S| ≤ p^(1-α)` has a
valid ordering: an enumeration `s₁, …, s_{|S|}` of the elements of `S` whose partial sums
`s₁ + ⋯ + s_k` (`1 ≤ k ≤ |S|`) are pairwise distinct.

Combined with earlier work (Bedert–Kravitz for small sets, Bedert–Bucić–Kravitz–Montgomery–
Müyesser for large sets), the paper deduces Graham's conjecture for all sufficiently large
primes. Those earlier results are not formalized here. -/
theorem theorem_1_2 (α : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (p : ℕ), p.Prime →
      ∀ S : Finset (ZMod p), 0 ∉ S →
        C ≤ (#S : ℝ) → (#S : ℝ) ≤ (p : ℝ) ^ (1 - α) →
        ∃ l : List (ZMod p), l.Nodup ∧ l.toFinset = S ∧
          Function.Injective fun k : Fin l.length => (l.take (k + 1)).sum := by
  obtain ⟨C, hC, h⟩ := GrahamRearrangement.theorem12 α hα₀ hα₁
  refine ⟨C, hC, fun p hp S h0 hlo hhi => ?_⟩
  obtain ⟨l, ⟨hnd, hS⟩, hps⟩ := h p hp S h0 hlo hhi
  refine ⟨l, hnd, hS, fun i j hij => ?_⟩
  have hlen := GrahamRearrangement.length_partialSums l
  have hi := GrahamRearrangement.getElem_partialSums l i i.isLt
  have hj := GrahamRearrangement.getElem_partialSums l j j.isLt
  simp only [GrahamRearrangement.listPrefixSum] at hi hj
  have h' : (GrahamRearrangement.partialSums l)[(i : ℕ)]'(by omega) =
      (GrahamRearrangement.partialSums l)[(j : ℕ)]'(by omega) := by
    rw [hi, hj]
    exact hij
  exact Fin.ext ((List.Nodup.getElem_inj_iff hps).1 h')

/-- **Theorem 1.3** (anticoncentration on a Boolean slice). There is an absolute constant
`C > 0` such that the following holds. Let `p` be a prime, `S ⊆ ℤ_p` with `|S| ≥ 2`, and let
`m` be an integer with `C log |S| ≤ m ≤ 10⁻³ |S| / log |S|`. If `R` is a uniformly random
`m`-element subset of `S`, then `ℙ[Σ(R) = z] ≤ 1/p + C / (|S| √m)` for every `z ∈ ℤ_p`. -/
theorem theorem_1_3 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (p : ℕ), p.Prime →
      ∀ S : Finset (ZMod p), 2 ≤ #S →
      ∀ m : ℕ, C * Real.log #S ≤ m → (m : ℝ) ≤ (1 / 1000 : ℝ) * #S / Real.log #S →
      ∀ z : ZMod p,
        (#{R ∈ S.powersetCard m | ∑ x ∈ R, x = z} : ℝ) / (#S).choose m ≤
          1 / p + C / (#S * Real.sqrt m) := by
  obtain ⟨C, hC, h⟩ := GrahamRearrangement.theorem13
  refine ⟨C, hC, fun p hp S hS m hlo hhi z => ?_⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have h2 := h p hp S hS m hlo hhi z
  rwa [sliceMass_eq] at h2

/-- **Corollary 1.4.** For every `0 < ε < 1` there is a constant `C'_ε > 0` such that the
following holds. Let `p` be a prime, `S ⊆ ℤ_p` with `|S| ≥ 2`, and let `m` be a positive
integer with `m ≤ (1 - ε) |S|`. If `R` is a uniformly random `m`-element subset of `S`, then
`ℙ[Σ(R) = z] ≤ 1/p + C'_ε √(log |S|) / (|S| √m)` for every `z ∈ ℤ_p`. -/
theorem corollary_1_4 (ε : ℝ) (hε₀ : 0 < ε) (hε₁ : ε < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (p : ℕ), p.Prime →
      ∀ S : Finset (ZMod p), 2 ≤ #S →
      ∀ m : ℕ, 0 < m → (m : ℝ) ≤ (1 - ε) * #S →
      ∀ z : ZMod p,
        (#{R ∈ S.powersetCard m | ∑ x ∈ R, x = z} : ℝ) / (#S).choose m ≤
          1 / p + C * Real.sqrt (Real.log #S) / (#S * Real.sqrt m) := by
  obtain ⟨C, hC, h⟩ := GrahamRearrangement.corollary14 ε hε₀ hε₁
  refine ⟨C, hC, fun p hp S hS m hm hmS z => ?_⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have h2 := h p hp S hS m hm hmS z
  rwa [sliceMass_eq] at h2

end PhamSauermann
