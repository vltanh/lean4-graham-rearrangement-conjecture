module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.ZMod.Defs

/-!
# On Graham's rearrangement conjecture

The three results stated in the introduction of H. T. Pham and L. Sauermann,
*On Graham's rearrangement conjecture*, arXiv:2602.15797v1 (2026).

Throughout, `p` is a prime, `ZMod p` is the cyclic group `ℤ_p`, and `S` is a finite subset
of `ZMod p`. The statements use only Mathlib's vocabulary.

* An *ordering* of `S` is a list `l` of the elements of `S`, each appearing once
  (`l.Nodup ∧ l.toFinset = S`). Its partial sums are `s₁, s₁ + s₂, …, s₁ + ⋯ + s_{|S|}`; the
  `k`-th of them is `(l.take k).sum`. An ordering is *valid* if its partial sums are pairwise
  distinct. Graham's rearrangement conjecture (1971) asserts that every `S ⊆ ℤ_p ∖ {0}` has a
  valid ordering.
* For `m ≤ |S|`, the probability that a uniformly random `m`-element subset `R` of `S` has
  sum `Σ(R) = z` is the proportion of the `m`-element subsets of `S` with sum `z`:
  `#{R ∈ S.powersetCard m | ∑ x ∈ R, x = z} / (|S| choose m)`.
* `Real.log` is the natural logarithm, as in the paper.

Each theorem below states the paper's result exactly as the paper does, with the constant
quantified in the same way. The proofs are in `Solution.lean`.
-/

@[expose] public section

open Finset

namespace PhamSauermann

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
  sorry

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
  sorry

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
  sorry

end PhamSauermann
