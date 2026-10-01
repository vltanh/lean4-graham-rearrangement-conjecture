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
  simp only [distToInt, Int.fract_add_intCast]

theorem distToInt_neg (y : ℝ) : distToInt (-y) = distToInt y := by
  apply le_antisymm
  · calc distToInt (-y) ≤ |-y - ((-round y : ℤ) : ℝ)| := distToInt_le_abs_sub_int _ _
      _ = |y - round y| := by rw [← abs_neg]; push_cast; ring_nf
      _ = distToInt y := (distToInt_eq_abs_sub_round y).symm
  · calc distToInt y ≤ |y - ((-round (-y) : ℤ) : ℝ)| := distToInt_le_abs_sub_int _ _
      _ = |-y - round (-y)| := by rw [← abs_neg]; push_cast; ring_nf
      _ = distToInt (-y) := (distToInt_eq_abs_sub_round (-y)).symm

/-- The two-term nearest-integer triangle inequality: with `z₁, z₂` the nearest
integers to `a, b`, `‖a + b‖_ℤ ≤ |(a + b) - (z₁ + z₂)| ≤ ‖a‖_ℤ + ‖b‖_ℤ`. -/
theorem distToInt_add_le (a b : ℝ) :
    distToInt (a + b) ≤ distToInt a + distToInt b := by
  calc distToInt (a + b) ≤ |a + b - ((round a + round b : ℤ) : ℝ)| :=
        distToInt_le_abs_sub_int _ _
    _ = |(a - round a) + (b - round b)| := by push_cast; ring_nf
    _ ≤ |a - round a| + |b - round b| := abs_add_le _ _
    _ = distToInt a + distToInt b := by
        rw [distToInt_eq_abs_sub_round, distToInt_eq_abs_sub_round]

theorem abs_list_sum_le_sum_abs (xs : List ℝ) :
    |xs.sum| ≤ (xs.map (fun x => |x|)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.sum_cons, List.map_cons]
      exact (abs_add_le x xs.sum).trans (by linarith)

theorem cauchySchwarz_list (xs : List ℝ) :
    xs.sum ^ 2 ≤
      (xs.length : ℝ) * (xs.map fun x => x ^ 2).sum := by
  have h := Multiset.sq_sum_le_card_mul_sum_sq (xs : Multiset ℝ)
  simpa using h

/-- The nearest-integer triangle step in the proof of Fact 2.1. -/
theorem distToInt_sum_le (ys : List ℝ) :
    distToInt ys.sum ≤ (ys.map distToInt).sum := by
  induction ys with
  | nil => simp [distToInt]
  | cons y ys ih =>
      simp only [List.sum_cons, List.map_cons]
      exact (distToInt_add_le y ys.sum).trans (by linarith)

/-- Fact 2.1, following the paper: choose nearest integers, use the triangle
inequality, and then Cauchy--Schwarz. -/
theorem fact2_1 (ys : List ℝ) :
    distToInt ys.sum ^ 2 ≤
      (ys.length : ℝ) * (ys.map fun y => distToInt y ^ 2).sum := by
  have htri := distToInt_sum_le ys
  have hsq : distToInt ys.sum ^ 2 ≤ ((ys.map distToInt).sum) ^ 2 :=
    pow_le_pow_left₀ (distToInt_nonneg _) htri 2
  have hcs := cauchySchwarz_list (ys.map distToInt)
  rw [List.length_map, List.map_map] at hcs
  exact hsq.trans hcs

/-- Iterated derivatives of `u ↦ cos (2πu)`. -/
theorem iteratedDeriv_cos_two_pi (k : ℕ) (x : ℝ) :
    iteratedDeriv k (fun u : ℝ => Real.cos (2 * Real.pi * u)) x =
      (2 * Real.pi) ^ k * iteratedDeriv k Real.cos (2 * Real.pi * x) := by
  rw [iteratedDeriv_comp_const_mul Real.contDiff_cos (2 * Real.pi)]

theorem contDiff_cos_two_pi {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun u : ℝ => Real.cos (2 * Real.pi * u)) := by
  fun_prop

/-- The Taylor polynomial of `u ↦ cos (2πu)` at `0`, evaluated at `y > 0`. -/
theorem taylorWithinEval_cos_two_pi (n : ℕ) {y : ℝ} (hy : 0 < y) :
    taylorWithinEval (fun u : ℝ => Real.cos (2 * Real.pi * u)) n (Set.uIcc 0 y) 0 y =
      ∑ k ∈ Finset.range (n + 1),
        ((Nat.factorial k : ℝ)⁻¹ * y ^ k) *
          ((2 * Real.pi) ^ k * iteratedDeriv k Real.cos 0) := by
  rw [taylor_within_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hy.ne)
    contDiff_cos_two_pi.contDiffAt Set.left_mem_uIcc,
    iteratedDeriv_cos_two_pi]
  simp

/-- The exact third-order Lagrange remainder formula used for the lower
inequality in Fact 2.2. -/
theorem cos_two_pi_taylor3 {y : ℝ} (hy0 : 0 ≤ y) :
    ∃ ξ ∈ Set.Icc (0 : ℝ) y,
      Real.cos (2 * Real.pi * y) =
        1 - ((2 * Real.pi) ^ 2 / 2) * y ^ 2 +
          ((2 * Real.pi) ^ 3 * Real.sin (2 * Real.pi * ξ) / 6) * y ^ 3 := by
  rcases hy0.eq_or_lt with hy | hy
  · subst hy
    exact ⟨0, by simp, by simp⟩
  obtain ⟨ξ, hξ, hTaylor⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv
      (f := fun u : ℝ => Real.cos (2 * Real.pi * u))
      (x := y) (x₀ := 0) (n := 2) hy.ne contDiff_cos_two_pi.contDiffOn
  rw [Set.uIoo_of_le hy0] at hξ
  refine ⟨ξ, Set.Ioo_subset_Icc_self hξ, ?_⟩
  rw [taylorWithinEval_cos_two_pi 2 hy, iteratedDeriv_cos_two_pi] at hTaylor
  simp [Finset.sum_range_succ, Nat.factorial] at hTaylor
  linarith

/-- The fourth-order Lagrange remainder formula used for the upper inequality
in Fact 2.2. -/
theorem cos_two_pi_taylor4 {y : ℝ} (hy0 : 0 ≤ y) :
    ∃ ξ ∈ Set.Icc (0 : ℝ) y,
      Real.cos (2 * Real.pi * y) =
        1 - ((2 * Real.pi) ^ 2 / 2) * y ^ 2 +
          ((2 * Real.pi) ^ 4 * Real.cos (2 * Real.pi * ξ) / 24) * y ^ 4 := by
  rcases hy0.eq_or_lt with hy | hy
  · subst hy
    exact ⟨0, by simp, by simp⟩
  obtain ⟨ξ, hξ, hTaylor⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv
      (f := fun u : ℝ => Real.cos (2 * Real.pi * u))
      (x := y) (x₀ := 0) (n := 3) hy.ne contDiff_cos_two_pi.contDiffOn
  rw [Set.uIoo_of_le hy0] at hξ
  refine ⟨ξ, Set.Ioo_subset_Icc_self hξ, ?_⟩
  rw [taylorWithinEval_cos_two_pi 3 hy, iteratedDeriv_cos_two_pi] at hTaylor
  simp [Finset.sum_range_succ, Nat.factorial] at hTaylor
  linarith

theorem cos_nearest_integer_reduction (y : ℝ) :
    Real.cos (2 * Real.pi * y) =
      Real.cos (2 * Real.pi * distToInt y) := by
  rw [distToInt_eq_abs_sub_round]
  have h1 : Real.cos (2 * Real.pi * y) = Real.cos (2 * Real.pi * (y - round y)) := by
    rw [← Real.cos_sub_int_mul_two_pi (2 * Real.pi * y) (round y)]
    congr 1
    ring
  rw [h1]
  rcases abs_cases (y - round y) with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]
  · rw [h, mul_neg, Real.cos_neg]

/-- Fact 2.2. The proof follows the two Taylor expansions in the paper. -/
theorem fact2_2 (y : ℝ) :
    1 - 20 * distToInt y ^ 2 ≤ Real.cos (2 * Real.pi * y) ∧
      Real.cos (2 * Real.pi * y) ≤ 1 - 2 * distToInt y ^ 2 := by
  rw [cos_nearest_integer_reduction]
  set d := distToInt y with hd
  have hd0 : 0 ≤ d := distToInt_nonneg y
  have hdh : d ≤ 1 / 2 := distToInt_le_half y
  have hpi3 : 3 < Real.pi := Real.pi_gt_three
  have hpi4 : Real.pi < 3.15 := Real.pi_lt_d2
  have hP9 : 9 < Real.pi ^ 2 := by nlinarith
  have hP10 : Real.pi ^ 2 < 10 := by nlinarith
  constructor
  · -- `cos (2πd) ≥ 1 - 2π² d² ≥ 1 - 20 d²`, since `sin (2πξ) ≥ 0` for `ξ ∈ [0, 1/2]`.
    obtain ⟨ξ, hξ, hT⟩ := cos_two_pi_taylor3 hd0
    have hsin : 0 ≤ Real.sin (2 * Real.pi * ξ) := by
      apply Real.sin_nonneg_of_nonneg_of_le_pi
      · have := hξ.1
        positivity
      · have := hξ.2
        nlinarith [Real.pi_pos]
    have hrem : 0 ≤ (2 * Real.pi) ^ 3 * Real.sin (2 * Real.pi * ξ) / 6 * d ^ 3 := by
      have := hξ.1
      positivity
    have hcoef : (2 * Real.pi) ^ 2 / 2 * d ^ 2 ≤ 20 * d ^ 2 := by
      have : (2 * Real.pi) ^ 2 / 2 = 2 * Real.pi ^ 2 := by ring
      rw [this]
      gcongr
      linarith
    rw [hT]
    linarith
  · -- `cos (2πd) ≤ 1 - (2π)²/2 d² + (2π)⁴/24 (1/2)² d² ≤ 1 - 2 d²`.
    obtain ⟨ξ, hξ, hT⟩ := cos_two_pi_taylor4 hd0
    have hcos : Real.cos (2 * Real.pi * ξ) ≤ 1 := Real.cos_le_one _
    have hd4 : d ^ 4 ≤ d ^ 2 / 4 := by
      have h1 : d ^ 2 ≤ 1 / 4 := by nlinarith
      have h2 : 0 ≤ d ^ 2 := sq_nonneg d
      nlinarith
    have h1 : (2 * Real.pi) ^ 4 * Real.cos (2 * Real.pi * ξ) / 24 * d ^ 4 ≤
        (2 * Real.pi) ^ 4 / 24 * (d ^ 2 / 4) := by
      calc (2 * Real.pi) ^ 4 * Real.cos (2 * Real.pi * ξ) / 24 * d ^ 4
          = (2 * Real.pi) ^ 4 / 24 * (Real.cos (2 * Real.pi * ξ) * d ^ 4) := by ring
        _ ≤ (2 * Real.pi) ^ 4 / 24 * (1 * (d ^ 2 / 4)) := by
            gcongr
        _ = (2 * Real.pi) ^ 4 / 24 * (d ^ 2 / 4) := by ring
    have hnum : 2 ≤ (2 * Real.pi) ^ 2 / 2 - (2 * Real.pi) ^ 4 / 24 / 4 := by
      have e : (2 * Real.pi) ^ 2 / 2 - (2 * Real.pi) ^ 4 / 24 / 4 =
          2 * Real.pi ^ 2 - (Real.pi ^ 2) ^ 2 / 6 := by ring
      rw [e]
      nlinarith
    rw [hT]
    have hfin : 1 - (2 * Real.pi) ^ 2 / 2 * d ^ 2 + (2 * Real.pi) ^ 4 / 24 * (d ^ 2 / 4) =
        1 - ((2 * Real.pi) ^ 2 / 2 - (2 * Real.pi) ^ 4 / 24 / 4) * d ^ 2 := by ring
    have h2 : 2 * d ^ 2 ≤ ((2 * Real.pi) ^ 2 / 2 - (2 * Real.pi) ^ 4 / 24 / 4) * d ^ 2 :=
      mul_le_mul_of_nonneg_right hnum (sq_nonneg d)
    linarith

/-- The paper's `‖x‖ₚ`, written using the canonical representative. -/
def zmodNorm {p : ℕ} [NeZero p] (x : ZMod p) : ℝ :=
  distToInt ((x.val : ℝ) / (p : ℝ))

theorem zmodNorm_nonneg {p : ℕ} [NeZero p] (x : ZMod p) :
    0 ≤ zmodNorm x := distToInt_nonneg _

theorem zmodNorm_le_half {p : ℕ} [NeZero p] (x : ZMod p) :
    zmodNorm x ≤ 1 / 2 := distToInt_le_half _

theorem zmodNorm_neg {p : ℕ} [NeZero p] (x : ZMod p) :
    zmodNorm (-x) = zmodNorm x := by
  unfold zmodNorm
  rw [ZMod.neg_val]
  split_ifs with hx
  · subst hx
    simp
  · have hle : x.val ≤ p := (ZMod.val_lt x).le
    have hp : (0 : ℝ) < p := by exact_mod_cast NeZero.pos p
    rw [Nat.cast_sub hle, sub_div, div_self hp.ne',
      show (1 : ℝ) - x.val / p = -(x.val / p) + ((1 : ℤ) : ℝ) by push_cast; ring,
      distToInt_add_int, distToInt_neg]

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
  rcases representative_sum_shift xs with ⟨q, hq⟩
  have hp : (0 : ℝ) < p := by exact_mod_cast (NeZero.pos p)
  have hcast : (xs.map fun x => (x.val : ℝ)).sum = ((xs.sum).val : ℝ) + (p : ℝ) * q := by
    have h := congrArg (fun n : ℤ => (n : ℝ)) hq
    simpa [Int.cast_list_sum, List.map_map, Function.comp_def] using h
  have hreal :
      (xs.map fun x => (x.val : ℝ) / (p : ℝ)).sum =
        ((xs.sum).val : ℝ) / p + q := by
    simp only [div_eq_mul_inv]
    rw [List.sum_map_mul_right, hcast]
    field_simp
  rw [hreal, distToInt_add_int]
  rfl

/-- Fact 2.3, following the representative argument in the paper. -/
theorem fact2_3_general {p : ℕ} [NeZero p] (xs : List (ZMod p)) :
    zmodNorm xs.sum ^ 2 ≤
      (xs.length : ℝ) * (xs.map fun x => zmodNorm x ^ 2).sum := by
  have h := fact2_1 (xs.map fun x => (x.val : ℝ) / (p : ℝ))
  rw [distToInt_rep_sum_eq_zmodNorm, List.length_map, List.map_map] at h
  exact h

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
  induction k generalizing x with
  | zero =>
      simp only [kfoldSumset_zero, Finset.mem_singleton, List.length_eq_zero_iff]
      constructor
      · rintro rfl
        exact ⟨[], rfl, by simp, rfl⟩
      · rintro ⟨xs, rfl, _, rfl⟩
        rfl
  | succ k ih =>
      constructor
      · intro hx
        rw [kfoldSumset_succ] at hx
        rcases Finset.mem_add.1 hx with ⟨u, hu, a, ha, rfl⟩
        rcases (ih u).1 hu with ⟨xs, hlen, hmem, hsum⟩
        refine ⟨xs ++ [a], by simp [hlen], ?_, by simp [hsum]⟩
        intro y hy
        rcases List.mem_append.1 hy with hy | hy
        · exact hmem y hy
        · rw [List.mem_singleton.1 hy]
          exact ha
      · rintro ⟨xs, hlen, hmem, rfl⟩
        obtain ⟨ys, a, rfl⟩ : ∃ ys a, xs = ys ++ [a] := by
          rcases List.eq_nil_or_concat xs with h | ⟨ys, a, h⟩
          · subst h; simp at hlen
          · exact ⟨ys, a, by rw [h, List.concat_eq_append]⟩
        rw [List.sum_append, List.sum_singleton, kfoldSumset_succ]
        refine Finset.mem_add.2 ⟨ys.sum, (ih ys.sum).2 ⟨ys, ?_, ?_, rfl⟩, a,
          hmem a (by simp), rfl⟩
        · simpa using hlen
        · intro y hy
          exact hmem y (List.mem_append_left _ hy)

theorem kfoldSumset_empty {p k : ℕ}
    (hk : 0 < k) :
    kfoldSumset (∅ : Finset (ZMod p)) k = ∅ := by
  cases k with
  | zero => omega
  | succ k => simp [kfoldSumset]

theorem univ_add_nonempty {p : ℕ} [NeZero p]
    {A : Finset (ZMod p)} (hA : A.Nonempty) :
    (Finset.univ : Finset (ZMod p)) + A = Finset.univ := by
  ext x
  simp only [Finset.mem_add, Finset.mem_univ, true_and, iff_true]
  rcases hA with ⟨a, ha⟩
  exact ⟨x - a, a, ha, by simp⟩

/-- A proper k-fold sumset has every positive prefix proper. -/
theorem kfoldSumset_prefix_proper {p k : ℕ} [NeZero p]
    {A : Finset (ZMod p)} (hA : A.Nonempty)
    (hproper : kfoldSumset A (k + 1) ≠ Finset.univ) :
    kfoldSumset A k ≠ Finset.univ := by
  intro hk
  apply hproper
  rw [kfoldSumset_succ, hk, univ_add_nonempty hA]

theorem kfoldSumset_nonempty {p : ℕ} {A : Finset (ZMod p)} (hA : A.Nonempty) (k : ℕ) :
    (kfoldSumset A k).Nonempty := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [kfoldSumset_succ]
      exact ih.add hA

/-- Fact 2.4, exactly as in the paper. The only external input is the ordinary
two-set Cauchy--Davenport theorem. -/
theorem fact2_4 {p k : ℕ} [NeZero p] (hp : p.Prime)
    (A : Finset (ZMod p)) (hk : 0 < k)
    (hproper : kfoldSumset A k ≠ Finset.univ) :
    (1 : ℤ) + (k : ℤ) * ((A.card : ℤ) - 1) ≤
      ((kfoldSumset A k).card : ℤ) := by
  rcases A.eq_empty_or_nonempty with hAe | hA
  · subst hAe
    rw [kfoldSumset_empty hk]
    simp only [Finset.card_empty, Nat.cast_zero, zero_sub, mul_neg, mul_one]
    have : (1 : ℤ) ≤ k := by exact_mod_cast hk
    linarith
  induction k with
  | zero => omega
  | succ k ih =>
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · subst hk0
        simp
      · -- Cauchy--Davenport for `(kA) + A ≠ ℤ_p`: `|kA + A| - 1 ≥ (|kA| - 1) + (|A| - 1)`.
        have hprev := kfoldSumset_prefix_proper hA hproper
        have hih := ih hk0 hprev
        have hcd := ZMod.cauchy_davenport hp (kfoldSumset_nonempty hA k) hA
        rw [kfoldSumset_succ] at hproper ⊢
        have hlt : (kfoldSumset A k + A).card < p := by
          have h := (Finset.card_lt_iff_ne_univ _).2 hproper
          rwa [ZMod.card] at h
        have hcd' : (kfoldSumset A k).card + A.card - 1 ≤ (kfoldSumset A k + A).card := by
          rcases min_le_iff.mp hcd with h | h
          · omega
          · exact h
        have hpos1 : 1 ≤ (kfoldSumset A k).card := (kfoldSumset_nonempty hA k).card_pos
        have hcd'' : ((kfoldSumset A k).card : ℤ) + (A.card : ℤ) - 1 ≤
            ((kfoldSumset A k + A).card : ℤ) := by
          omega
        push_cast
        have e : ((k : ℤ) + 1) * ((A.card : ℤ) - 1) =
            (k : ℤ) * ((A.card : ℤ) - 1) + ((A.card : ℤ) - 1) := by ring
        rw [e]
        linarith

/-- The paper's character `eₚ(x)=exp(2πix/p)`. -/
def ep (p : ℕ) [NeZero p] (x : ZMod p) : ℂ :=
  Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I *
    (((x.val : ℝ) / (p : ℝ) : ℝ) : ℂ))

theorem ep_eq_stdAddChar {p : ℕ} [NeZero p] (x : ZMod p) :
    ep p x = ZMod.stdAddChar x := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  unfold ep
  congr 1
  push_cast
  ring

theorem stdAddChar_re_eq_cos {p : ℕ} [NeZero p] (x : ZMod p) :
    (ZMod.stdAddChar x).re =
      Real.cos (2 * Real.pi * ((x.val : ℝ) / (p : ℝ))) := by
  rw [← ep_eq_stdAddChar]
  unfold ep
  rw [← Complex.exp_ofReal_mul_I_re]
  congr 2
  push_cast
  ring

/-- Fact 2.5. -/
theorem fact2_5 {p : ℕ} [NeZero p] (hp : p.Prime) (x : ZMod p) :
    (ep p x).re ≤ 1 - 2 * zmodNorm x ^ 2 := by
  rw [ep_eq_stdAddChar, stdAddChar_re_eq_cos]
  exact (fact2_2 _).2

/-- Finite-index form of Fact 2.3 used later. -/
theorem fact2_3_finset {p : ℕ} [NeZero p] {ι : Type*}
    [DecidableEq ι] (s : Finset ι) (f : ι → ZMod p) :
    zmodNorm (∑ i ∈ s, f i) ^ 2 ≤
      (s.card : ℝ) * ∑ i ∈ s, zmodNorm (f i) ^ 2 := by
  have h := fact2_3_general (s.toList.map f)
  rw [List.length_map, Finset.length_toList, List.map_map, Finset.sum_map_toList,
    Finset.sum_map_toList] at h
  exact h

end

end GrahamRearrangement
