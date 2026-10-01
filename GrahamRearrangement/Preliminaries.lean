module

public import GrahamRearrangement.Introduction
public import GrahamRearrangement.External
public import Mathlib.Algebra.Order.Round
public import Mathlib.Analysis.Calculus.Taylor

@[expose] public section

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Section 2: Preliminaries

This module follows Section 2 of the paper.  Facts 2.1--2.5 are proved here
from mathlib theorems and explicit finite/algebraic arguments; no project axiom
is used.
-/

noncomputable section

/-- The paper's distance `‖y‖_ℤ` to the nearest integer. -/
def distToInt (y : ℝ) : ℝ :=
  min (Int.fract y) (1 - Int.fract y)

theorem distToInt_eq_abs_sub_round (y : ℝ) :
    distToInt y = |y - (round y : ℝ)| := by
  symm
  simpa [distToInt] using (abs_sub_round_eq_min y)

theorem distToInt_nonneg (y : ℝ) : 0 ≤ distToInt y := by
  rw [distToInt_eq_abs_sub_round]
  exact abs_nonneg _

theorem distToInt_le_half (y : ℝ) : distToInt y ≤ 1 / 2 := by
  rw [distToInt_eq_abs_sub_round]
  simpa using (abs_sub_round y)

theorem distToInt_le_abs_sub_int (y : ℝ) (z : ℤ) :
    distToInt y ≤ |y - (z : ℝ)| := by
  rw [distToInt_eq_abs_sub_round]
  exact round_le y z

theorem distToInt_add_int (y : ℝ) (z : ℤ) :
    distToInt (y + z) = distToInt y := by
  sorry

theorem abs_list_sum_le_sum_abs (xs : List ℝ) :
    |xs.sum| ≤ (xs.map (fun x => |x|)).sum := by
  sorry

theorem cauchySchwarz_list (xs : List ℝ) :
    xs.sum ^ 2 ≤
      (xs.length : ℝ) * (xs.map fun x => x ^ 2).sum := by
  sorry

/-- The nearest-integer triangle step in the proof of Fact 2.1. -/
theorem distToInt_sum_le (ys : List ℝ) :
    distToInt ys.sum ≤ (ys.map distToInt).sum := by
  sorry

/-- Fact 2.1, following the paper: choose nearest integers, use the triangle
inequality, and then Cauchy--Schwarz. -/
theorem fact2_1 (ys : List ℝ) :
    distToInt ys.sum ^ 2 ≤
      (ys.length : ℝ) * (ys.map fun y => distToInt y ^ 2).sum := by
  sorry

/-- The exact third-order Lagrange remainder formula used for the lower
inequality in Fact 2.2. -/
theorem cos_two_pi_taylor3 {y : ℝ} (hy0 : 0 ≤ y) :
    ∃ ξ ∈ Set.Icc (0 : ℝ) y,
      Real.cos (2 * Real.pi * y) =
        1 - ((2 * Real.pi) ^ 2 / 2) * y ^ 2 +
          ((2 * Real.pi) ^ 3 * Real.sin (2 * Real.pi * ξ) / 6) * y ^ 3 := by
  sorry

/-- The fourth-order Lagrange remainder formula used for the upper inequality
in Fact 2.2. -/
theorem cos_two_pi_taylor4 {y : ℝ} (hy0 : 0 ≤ y) :
    ∃ ξ ∈ Set.Icc (0 : ℝ) y,
      Real.cos (2 * Real.pi * y) =
        1 - ((2 * Real.pi) ^ 2 / 2) * y ^ 2 +
          ((2 * Real.pi) ^ 4 * Real.cos (2 * Real.pi * ξ) / 24) * y ^ 4 := by
  sorry

theorem cos_nearest_integer_reduction (y : ℝ) :
    Real.cos (2 * Real.pi * y) =
      Real.cos (2 * Real.pi * distToInt y) := by
  sorry

/-- Fact 2.2. The proof follows the two Taylor expansions in the paper. -/
theorem fact2_2 (y : ℝ) :
    1 - 20 * distToInt y ^ 2 ≤ Real.cos (2 * Real.pi * y) ∧
      Real.cos (2 * Real.pi * y) ≤ 1 - 2 * distToInt y ^ 2 := by
  sorry

/-- The paper's `‖x‖ₚ`, written using the canonical representative. -/
def zmodNorm {p : ℕ} [NeZero p] (x : ZMod p) : ℝ :=
  distToInt ((x.val : ℝ) / (p : ℝ))

theorem zmodNorm_nonneg {p : ℕ} [NeZero p] (x : ZMod p) :
    0 ≤ zmodNorm x := distToInt_nonneg _

theorem zmodNorm_le_half {p : ℕ} [NeZero p] (x : ZMod p) :
    zmodNorm x ≤ 1 / 2 := distToInt_le_half _

theorem zmodNorm_neg {p : ℕ} [NeZero p] (x : ZMod p) :
    zmodNorm (-x) = zmodNorm x := by
  sorry

theorem representative_sum_shift {p : ℕ} [NeZero p]
    (xs : List (ZMod p)) :
    ∃ q : ℤ,
      (xs.map fun x => (x.val : ℤ)).sum =
        ((xs.sum).val : ℤ) + (p : ℤ) * q := by
  have hcast :
      (((xs.map fun x => (x.val : ℤ)).sum : ℤ) : ZMod p) = xs.sum := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
        simp [ih]
  exact (ZMod.intCast_eq_iff p
    ((xs.map fun x => (x.val : ℤ)).sum) xs.sum).1 hcast

theorem distToInt_rep_sum_eq_zmodNorm {p : ℕ} [NeZero p]
    (xs : List (ZMod p)) :
    distToInt
        ((xs.map fun x => (x.val : ℝ) / (p : ℝ)).sum) =
      zmodNorm xs.sum := by
  sorry

/-- Fact 2.3, following the representative argument in the paper. -/
theorem fact2_3_general {p : ℕ} [NeZero p] (xs : List (ZMod p)) :
    zmodNorm xs.sum ^ 2 ≤
      (xs.length : ℝ) * (xs.map fun x => zmodNorm x ^ 2).sum := by
  sorry

/-- Fact 2.3. -/
theorem fact2_3 {p : ℕ} [NeZero p] (hp : p.Prime) (xs : List (ZMod p)) :
    zmodNorm xs.sum ^ 2 ≤
      (xs.length : ℝ) * (xs.map fun x => zmodNorm x ^ 2).sum :=
  fact2_3_general xs

/-- The `k`-fold sumset `kA` from Fact 2.4. -/
def kfoldSumset {p : ℕ} (A : Finset (ZMod p)) : ℕ → Finset (ZMod p)
  | 0 => {0}
  | k + 1 => kfoldSumset A k + A

@[simp] theorem kfoldSumset_zero {p : ℕ} (A : Finset (ZMod p)) :
    kfoldSumset A 0 = {0} := rfl

@[simp] theorem kfoldSumset_succ {p k : ℕ} (A : Finset (ZMod p)) :
    kfoldSumset A (k + 1) = kfoldSumset A k + A := rfl

/-- Membership in the k-fold sumset is equivalent to a sum of a length-k list
whose entries all lie in A. -/
theorem mem_kfoldSumset {p k : ℕ} [NeZero p]
    (A : Finset (ZMod p)) (x : ZMod p) :
    x ∈ kfoldSumset A k ↔
      ∃ xs : List (ZMod p),
        xs.length = k ∧ (∀ y ∈ xs, y ∈ A) ∧ xs.sum = x := by
  sorry

theorem kfoldSumset_empty {p k : ℕ}
    (hk : 0 < k) :
    kfoldSumset (∅ : Finset (ZMod p)) k = ∅ := by
  cases k with
  | zero => omega
  | succ k => simp [kfoldSumset]

theorem univ_add_nonempty {p : ℕ} [NeZero p]
    {A : Finset (ZMod p)} (hA : A.Nonempty) :
    (Finset.univ : Finset (ZMod p)) + A = Finset.univ := by
  sorry

/-- A proper k-fold sumset has every positive prefix proper. -/
theorem kfoldSumset_prefix_proper {p k : ℕ} [NeZero p]
    {A : Finset (ZMod p)} (hA : A.Nonempty)
    (hproper : kfoldSumset A (k + 1) ≠ Finset.univ) :
    kfoldSumset A k ≠ Finset.univ := by
  intro hk
  apply hproper
  rw [kfoldSumset_succ, hk, univ_add_nonempty hA]

/-- Fact 2.4, exactly as in the paper. The only external input is the ordinary
two-set Cauchy--Davenport theorem. -/
theorem fact2_4 {p k : ℕ} [NeZero p] (hp : p.Prime)
    (A : Finset (ZMod p)) (hk : 0 < k)
    (hproper : kfoldSumset A k ≠ Finset.univ) :
    (1 : ℤ) + (k : ℤ) * ((A.card : ℤ) - 1) ≤
      ((kfoldSumset A k).card : ℤ) := by
  sorry

/-- The paper's character `eₚ(x)=exp(2πix/p)`. -/
def ep (p : ℕ) [NeZero p] (x : ZMod p) : ℂ :=
  Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I *
    (((x.val : ℝ) / (p : ℝ) : ℝ) : ℂ))

theorem ep_eq_stdAddChar {p : ℕ} [NeZero p] (x : ZMod p) :
    ep p x = ZMod.stdAddChar x := by
  sorry

theorem stdAddChar_re_eq_cos {p : ℕ} [NeZero p] (x : ZMod p) :
    (ZMod.stdAddChar x).re =
      Real.cos (2 * Real.pi * ((x.val : ℝ) / (p : ℝ))) := by
  sorry

/-- Fact 2.5. -/
theorem fact2_5 {p : ℕ} [NeZero p] (hp : p.Prime) (x : ZMod p) :
    (ep p x).re ≤ 1 - 2 * zmodNorm x ^ 2 := by
  sorry

/-- Finite-index form of Fact 2.3 used later. -/
theorem fact2_3_finset {p : ℕ} [NeZero p] {ι : Type*}
    [DecidableEq ι] (s : Finset ι) (f : ι → ZMod p) :
    zmodNorm (∑ i ∈ s, f i) ^ 2 ≤
      (s.card : ℝ) * ∑ i ∈ s, zmodNorm (f i) ^ 2 := by
  sorry

end

end GrahamRearrangement
