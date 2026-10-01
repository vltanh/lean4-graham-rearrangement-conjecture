module

public import GrahamRearrangement.Probability
public import GrahamRearrangement.External.Hypergeometric
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Data.Nat.Log

@[expose] public section

open scoped BigOperators Pointwise

namespace GrahamRearrangement.External

/-!
# External inputs

This module now contains proved general-purpose lemmas used across the
formalization.  The bibliographic hypergeometric input cited by
Pham--Sauermann is formalized in `External/Hypergeometric/`; no project axiom
is used anywhere in this hierarchy.
-/

noncomputable section

-- ---------------------------------------------------------------------------
-- Standard real/complex analysis
-- ---------------------------------------------------------------------------

-- ---------------------------------------------------------------------------
-- Additive combinatorics
-- ---------------------------------------------------------------------------

-- ---------------------------------------------------------------------------
-- Finite Fourier analysis
-- ---------------------------------------------------------------------------

/-- Orthogonality of the additive characters of Z/pZ. -/
theorem zmod_character_orthogonality {p : ℕ} [NeZero p] (hp : p.Prime) (a : ZMod p) :
    (∑ χ : ZMod p, ZMod.stdAddChar (χ * a)) =
      if a = 0 then (p : ℂ) else 0 := by
  have h := AddChar.sum_mulShift (ψ := (ZMod.stdAddChar : AddChar (ZMod p) ℂ)) a
    (ZMod.isPrimitive_stdAddChar p)
  rw [h, ZMod.card]
  split_ifs <;> simp

/-- Character-average norm-square identity, obtained by expanding the square. -/
theorem zmod_character_average_norm_sq {p : ℕ} [NeZero p]
    (T : Finset (ZMod p)) (hT : T.Nonempty) (χ : ZMod p) :
    ‖((∑ x ∈ T, ZMod.stdAddChar (χ * x)) / (T.card : ℂ))‖ ^ 2 =
      (1 / (T.card : ℝ) ^ 2) *
        ∑ x ∈ T, ∑ x' ∈ T,
          (ZMod.stdAddChar (χ * x - χ * x')).re := by
  set A : ℂ := ∑ x ∈ T, ZMod.stdAddChar (χ * x) with hA
  have hnorm :
      ‖A / (T.card : ℂ)‖ ^ 2 =
        Complex.normSq A / (T.card : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_div, Complex.normSq_natCast]
    ring
  have hexpand :
      Complex.normSq A =
        ∑ x ∈ T, ∑ x' ∈ T,
          (ZMod.stdAddChar (χ * x - χ * x')).re := by
    have hmul :
        ((Complex.normSq A : ℝ) : ℂ) = A * (starRingEnd ℂ) A := (Complex.mul_conj A).symm
    have key : A * (starRingEnd ℂ) A =
        ∑ x ∈ T, ∑ x' ∈ T, ZMod.stdAddChar (χ * x - χ * x') := by
      rw [hA, map_sum, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro x' _
      rw [AddChar.map_sub_eq_div, div_eq_mul_inv]
      congr 1
      rw [ZMod.stdAddChar_apply, ← Circle.coe_inv_eq_conj, Circle.coe_inv]
    have hre := congrArg Complex.re (hmul.trans key)
    simpa [Complex.re_sum] using hre
  rw [hnorm, hexpand]
  ring

-- ---------------------------------------------------------------------------
-- Finite probability and sampling symmetry
-- ---------------------------------------------------------------------------

/-- Markov inequality on a finite uniform sample space. -/
theorem uniform_markov {Ω : Type*} [DecidableEq Ω]
    (space : Finset Ω) (X : Ω → ℝ) (a : ℝ)
    (hX : ∀ ω ∈ space, 0 ≤ X ω) (ha : 0 < a) :
    uniformMass space (fun ω => a ≤ X ω) ≤
      uniformExpectation space X / a := by
  unfold uniformMass uniformExpectation
  by_cases hs : space.card = 0
  · simp [hs]
  have hcardpos : (0 : ℝ) < space.card := by
    exact_mod_cast Nat.pos_of_ne_zero hs
  have hsum :
      a * ((space.filter fun ω => a ≤ X ω).card : ℝ) ≤
        ∑ ω ∈ space, X ω := by
    calc
      _ = ∑ _ω ∈ (space.filter fun ω => a ≤ X ω), a := by simp [mul_comm]
      _ ≤ ∑ ω ∈ (space.filter fun ω => a ≤ X ω), X ω := by
            apply Finset.sum_le_sum
            intro ω hω
            exact (Finset.mem_filter.mp hω).2
      _ ≤ ∑ ω ∈ space, X ω := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            intro ω hω _
            exact hX ω hω
  rw [div_div, le_div_iff₀ (by positivity), div_mul_eq_mul_div, div_le_iff₀ hcardpos]
  nlinarith

-- ---------------------------------------------------------------------------
-- Hypergeometric concentration
-- ---------------------------------------------------------------------------

/-!
The two lower-tail theorems used by Section 3 are proved in
`External/Hypergeometric/` and re-exported in namespace
`GrahamRearrangement.External`.  No project axiom is used.
-/

/-- A convenient monotonic consequence of exp for the numerical tail comparisons. -/
theorem exp_antitone {a b : ℝ} (h : a ≤ b) :
    Real.exp (-b) ≤ Real.exp (-a) :=
  Real.exp_le_exp.mpr (neg_le_neg h)

/-- exp(-c log n) = n^{-c}, in the positive range used throughout the paper. -/
theorem exp_neg_mul_log {n c : ℝ} (hn : 0 < n) :
    Real.exp (-c * Real.log n) = n ^ (-c) := by
  rw [Real.rpow_def_of_pos hn]
  congr 1
  ring

-- ---------------------------------------------------------------------------
-- Elementary asymptotic facts used to choose constants
-- ---------------------------------------------------------------------------

/-- Every real x in [1,m] lies in a dyadic interval [2^l,2^(l+1)). -/
theorem exists_dyadic_interval {x : ℝ} {m : ℕ}
    (hx : 1 ≤ x) (hm : x ≤ m) :
    ∃ l < Nat.log2 m + 1,
      (2 : ℝ) ^ l ≤ x ∧ x < 2 * (2 : ℝ) ^ l := by
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx
  have hfloor1 : 1 ≤ Nat.floor x := (Nat.one_le_floor_iff x).2 hx
  have hfloor0 : Nat.floor x ≠ 0 := by omega
  set l := Nat.log 2 (Nat.floor x) with hl
  have hlowN : 2 ^ l ≤ Nat.floor x :=
    Nat.pow_log_le_self 2 hfloor0
  have hlow : (2 : ℝ) ^ l ≤ x :=
    le_trans (by exact_mod_cast hlowN) (Nat.floor_le hx0)
  have huppN : Nat.floor x < 2 ^ (l + 1) :=
    Nat.lt_pow_succ_log_self Nat.one_lt_two (Nat.floor x)
  have hxFloor : x < (Nat.floor x : ℝ) + 1 :=
    Nat.lt_floor_add_one x
  have hupp : x < (2 : ℝ) ^ (l + 1) := by
    have : (Nat.floor x : ℝ) + 1 ≤ (2 : ℝ) ^ (l + 1) := by
      exact_mod_cast (Nat.succ_le_iff.mpr huppN)
    exact lt_of_lt_of_le hxFloor this
  have hfm : Nat.floor x ≤ m :=
    (Nat.floor_le_floor hm).trans (by simp)
  have hlog : l ≤ Nat.log 2 m := Nat.log_mono_right hfm
  refine ⟨l, ?_, hlow, ?_⟩
  · rw [Nat.log2_eq_log_two]
    omega
  · rw [pow_succ] at hupp
    linarith

/-- A convenient explicit lower bound for the natural logarithm of two. -/
theorem log_two_ge_half : (1 / 2 : ℝ) ≤ Real.log 2 := by
  exact le_of_lt (lt_trans (by norm_num) Real.log_two_gt_d9)

/-- `x² ≤ exp x` for `x ≥ 0`, from the cubic Taylor lower bound of `exp`. -/
theorem sq_le_real_exp {x : ℝ} (hx : 0 ≤ x) : x ^ 2 ≤ Real.exp x := by
  have h := Real.sum_le_exp_of_nonneg hx 4
  simp [Finset.sum_range_succ, Nat.factorial] at h
  nlinarith [mul_nonneg hx (sq_nonneg (x - 3 / 2))]

/-- Generic weighted dyadic split: small shells are controlled by a square-root
bound and the at most 22 remaining shells by the trivial bound. -/
theorem dyadic_weight_le_geometric (l : ℕ) :
    Real.sqrt ((2 : ℝ) ^ l) * Real.exp (-(2 : ℝ) ^ l) ≤
      (1 / 2 : ℝ) ^ l := by
  set x : ℝ := (2 : ℝ) ^ l with hxdef
  have hx1 : 1 ≤ x := one_le_pow₀ (by norm_num)
  have hx0 : 0 < x := by linarith
  have hexp : x ^ 2 ≤ Real.exp x := sq_le_real_exp hx0.le
  have hsqrt : Real.sqrt x ≤ x := Real.sqrt_le_self_iff.mpr (Or.inr hx1)
  have hhalf : (1 / 2 : ℝ) ^ l = 1 / x := by rw [hxdef, one_div_pow]
  rw [hhalf, Real.exp_neg, le_div_iff₀ hx0]
  calc Real.sqrt x * (Real.exp x)⁻¹ * x ≤ x * (Real.exp x)⁻¹ * x := by gcongr
     _ = x ^ 2 / Real.exp x := by ring
     _ ≤ 1 := by rw [div_le_one (Real.exp_pos x)]; exact hexp

theorem dyadic_weight_sum_le_two (N : ℕ) :
    (∑ l ∈ Finset.range N,
      Real.sqrt ((2 : ℝ) ^ l) * Real.exp (-(2 : ℝ) ^ l)) ≤ 2 := by
  calc
    _ ≤ ∑ l ∈ Finset.range N, (1 / 2 : ℝ) ^ l := by
          apply Finset.sum_le_sum
          intro l _
          exact dyadic_weight_le_geometric l
    _ ≤ 2 := by
          rw [geom_sum_eq (by norm_num)]
          have : (0 : ℝ) ≤ (1 / 2) ^ N := by positivity
          rw [div_le_iff_of_neg (by norm_num)]
          linarith

theorem terminal_dyadic_indices_card_le
    (m : ℕ) :
    ((Finset.range (Nat.log2 m + 1)).filter
      fun l => m / 2 ^ 22 < 2 ^ l).card ≤ 22 := by
  set L := Nat.log2 m with hL
  have hsub :
      (Finset.range (L + 1)).filter
          (fun l => m / 2 ^ 22 < 2 ^ l) ⊆
        Finset.Icc (L + 1 - 22) L := by
    intro l hl
    rcases Finset.mem_filter.mp hl with ⟨hlrange, htail⟩
    have hlL : l ≤ L := Nat.lt_succ_iff.mp (Finset.mem_range.mp hlrange)
    refine Finset.mem_Icc.mpr ⟨?_, hlL⟩
    by_contra hlow
    have hl22 : l + 22 ≤ L := by omega
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [hL, Nat.log2_eq_log_two] at hl22
      simp at hl22
    have hpw : 2 ^ (l + 22) ≤ m := by
      rw [hL, Nat.log2_eq_log_two] at hl22
      exact Nat.pow_le_of_le_log hm0 hl22
    have : 2 ^ l ≤ m / 2 ^ 22 := by
      apply (Nat.le_div_iff_mul_le (by positivity)).2
      simpa [pow_add] using hpw
    omega
  calc
    _ ≤ (Finset.Icc (L + 1 - 22) L).card := Finset.card_le_card hsub
    _ ≤ 22 := by
      rw [Nat.card_Icc]
      omega

/-- The final dyadic split in the proof of Theorem 1.3. -/
theorem weighted_dyadic_split (m : ℕ) (p K : ℝ) (E : ℕ → ℝ)
    (hp : 0 < p) (hK : 0 ≤ K)
    (hsmall : ∀ l, 2 ^ l ≤ m / 2 ^ 22 →
      E l ≤ p * K * Real.sqrt ((2 : ℝ) ^ l))
    (htriv : ∀ l, E l ≤ p) :
    (1 / p) *
        ∑ l ∈ Finset.range (Nat.log2 m + 1),
          E l * Real.exp (-(2 : ℝ) ^ l)
      ≤ 2 * K + 22 * Real.exp (-(m : ℝ) / 2 ^ 22) := by
  classical
  set S := Finset.range (Nat.log2 m + 1) with hS
  rw [← Finset.sum_filter_add_sum_filter_not S (fun l => 2 ^ l ≤ m / 2 ^ 22), mul_add]
  have hsm : (1 / p) * ∑ l ∈ S.filter (fun l => 2 ^ l ≤ m / 2 ^ 22),
      E l * Real.exp (-(2 : ℝ) ^ l) ≤ 2 * K := by
    rw [Finset.mul_sum]
    calc ∑ l ∈ S.filter (fun l => 2 ^ l ≤ m / 2 ^ 22),
          (1 / p) * (E l * Real.exp (-(2 : ℝ) ^ l))
        ≤ ∑ l ∈ S.filter (fun l => 2 ^ l ≤ m / 2 ^ 22),
            K * (Real.sqrt ((2 : ℝ) ^ l) * Real.exp (-(2 : ℝ) ^ l)) := by
          apply Finset.sum_le_sum
          intro l hl
          have hs := hsmall l (Finset.mem_filter.mp hl).2
          rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hp]
          calc E l * Real.exp (-(2 : ℝ) ^ l)
              ≤ (p * K * Real.sqrt ((2 : ℝ) ^ l)) * Real.exp (-(2 : ℝ) ^ l) := by
                gcongr
            _ = _ := by ring
      _ = K * ∑ l ∈ S.filter (fun l => 2 ^ l ≤ m / 2 ^ 22),
            Real.sqrt ((2 : ℝ) ^ l) * Real.exp (-(2 : ℝ) ^ l) := by
          rw [Finset.mul_sum]
      _ ≤ K * 2 := by
          gcongr
          calc _ ≤ ∑ l ∈ S, Real.sqrt ((2 : ℝ) ^ l) * Real.exp (-(2 : ℝ) ^ l) := by
                apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                intro l _ _
                positivity
             _ ≤ 2 := dyadic_weight_sum_le_two _
      _ = 2 * K := by ring
  have htl : (1 / p) * ∑ l ∈ S.filter (fun l => ¬ 2 ^ l ≤ m / 2 ^ 22),
      E l * Real.exp (-(2 : ℝ) ^ l) ≤ 22 * Real.exp (-(m : ℝ) / 2 ^ 22) := by
    have hcard : (S.filter (fun l => ¬ 2 ^ l ≤ m / 2 ^ 22)).card ≤ 22 := by
      have h := terminal_dyadic_indices_card_le m
      have heq : S.filter (fun l => ¬ 2 ^ l ≤ m / 2 ^ 22) =
          (Finset.range (Nat.log2 m + 1)).filter (fun l => m / 2 ^ 22 < 2 ^ l) := by
        rw [hS]
        apply Finset.filter_congr
        intro l _
        exact not_le
      rw [heq]
      exact h
    rw [Finset.mul_sum]
    calc ∑ l ∈ S.filter (fun l => ¬ 2 ^ l ≤ m / 2 ^ 22),
          (1 / p) * (E l * Real.exp (-(2 : ℝ) ^ l))
        ≤ ∑ l ∈ S.filter (fun l => ¬ 2 ^ l ≤ m / 2 ^ 22),
            Real.exp (-(m : ℝ) / 2 ^ 22) := by
          apply Finset.sum_le_sum
          intro l hl
          have hnot := (Finset.mem_filter.mp hl).2
          have hreal : (m : ℝ) / 2 ^ 22 ≤ (2 : ℝ) ^ l := by
            have h1 : m / 2 ^ 22 < 2 ^ l := lt_of_not_ge hnot
            have h2 : m < 2 ^ l * 2 ^ 22 := (Nat.div_lt_iff_lt_mul (by positivity)).1 h1
            rw [div_le_iff₀ (by positivity)]
            exact_mod_cast h2.le
          calc (1 / p) * (E l * Real.exp (-(2 : ℝ) ^ l))
              ≤ (1 / p) * (p * Real.exp (-(2 : ℝ) ^ l)) := by
                gcongr
                exact htriv l
            _ = Real.exp (-(2 : ℝ) ^ l) := by field_simp
            _ ≤ Real.exp (-(m : ℝ) / 2 ^ 22) := by
                apply Real.exp_le_exp.mpr
                rw [neg_div]
                linarith
      _ = (S.filter (fun l => ¬ 2 ^ l ≤ m / 2 ^ 22)).card *
            Real.exp (-(m : ℝ) / 2 ^ 22) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 22 * Real.exp (-(m : ℝ) / 2 ^ 22) := by
          gcongr
          exact_mod_cast hcard
  linarith

/-- Elementary floor estimate used with k=floor(sqrt x). -/
theorem natFloor_ge_half {x : ℝ} (hx : 1 ≤ x) :
    x / 2 ≤ (Nat.floor x : ℝ) := by
  have hfloor1 : (1 : ℝ) ≤ Nat.floor x := by
    exact_mod_cast (Nat.one_le_floor_iff x).2 hx
  have hlt : x < (Nat.floor x : ℝ) + 1 := Nat.lt_floor_add_one x
  linarith

/-- The standard reciprocal-square-root summation estimate. -/
theorem inv_sqrt_le_twice_sqrt_sub
    (n : ℕ) (hn : 1 ≤ n) :
    1 / Real.sqrt (n : ℝ) ≤
      2 * (Real.sqrt (n : ℝ) - Real.sqrt (n - 1 : ℝ)) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have ha : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
  have ha2 : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt hn0.le
  have hb2 : Real.sqrt ((n : ℝ) - 1) ^ 2 = (n : ℝ) - 1 := Real.sq_sqrt (by linarith)
  rw [div_le_iff₀ ha]
  nlinarith [sq_nonneg (Real.sqrt (n : ℝ) - Real.sqrt ((n : ℝ) - 1))]

theorem sum_inv_sqrt_le_two_sqrt (n : ℕ) :
    (∑ i ∈ Finset.Icc 1 n, (1 / Real.sqrt (i : ℝ))) ≤
      2 * Real.sqrt (n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hstep := inv_sqrt_le_twice_sqrt_sub (n + 1) (by omega)
      push_cast at hstep ⊢
      rw [add_sub_cancel_right] at hstep
      linarith

/-- Numerical consequence of D=ceil(3/α) when 0<α<1/2. -/
theorem ceil_three_div_ge_seven {α : ℝ}
    (hα0 : 0 < α) (hαh : α < 1 / 2) :
    7 ≤ Nat.ceil (3 / α) := by
  have h6 : (6 : ℝ) < 3 / α := by
    apply (lt_div_iff₀ hα0).2
    nlinarith
  exact Nat.add_one_le_ceil_iff.mpr h6

/-- Elementary power inequalities used for the Section 5 choice of C_α. -/
theorem section5_power_inequalities (D : ℕ) (hD : 7 ≤ D) :
    (100 : ℝ) * (5 * D : ℝ) ^ (2 * D) ≤
        (D + 1 : ℝ) * (2 : ℝ) ^ D *
          (D : ℝ) ^ (14 * D ^ 2) ∧
      (40 * D : ℝ) ^ D ≤
        (100 : ℝ) * (5 * D : ℝ) ^ (2 * D) := by
  have hD7 : (7 : ℝ) ≤ D := by exact_mod_cast hD
  have hD1 : (1 : ℝ) ≤ D := by linarith
  have h100 : (100 : ℝ) ≤ (2 : ℝ) ^ D := by
    calc (100 : ℝ) ≤ 2 ^ 7 := by norm_num
      _ ≤ 2 ^ D := pow_le_pow_right₀ (by norm_num) hD
  have h5D : (5 * D : ℝ) ≤ (D : ℝ) ^ 2 := by nlinarith
  have hpow5 : (5 * D : ℝ) ^ (2 * D) ≤ (D : ℝ) ^ (4 * D) := by
    calc (5 * D : ℝ) ^ (2 * D) ≤ ((D : ℝ) ^ 2) ^ (2 * D) :=
          pow_le_pow_left₀ (by positivity) h5D _
      _ = (D : ℝ) ^ (4 * D) := by rw [← pow_mul]; ring_nf
  have hpowD : (D : ℝ) ^ (4 * D) ≤ (D : ℝ) ^ (14 * D ^ 2) :=
    pow_le_pow_right₀ hD1 (by nlinarith)
  have hpos1 : (0 : ℝ) ≤ (5 * D : ℝ) ^ (2 * D) := by positivity
  have hpos3 : (0 : ℝ) ≤ (2 : ℝ) ^ D := by positivity
  constructor
  · calc (100 : ℝ) * (5 * D : ℝ) ^ (2 * D) ≤ (2 : ℝ) ^ D * (D : ℝ) ^ (14 * D ^ 2) :=
          mul_le_mul h100 (hpow5.trans hpowD) hpos1 hpos3
      _ = 1 * (2 : ℝ) ^ D * (D : ℝ) ^ (14 * D ^ 2) := by ring
      _ ≤ (D + 1 : ℝ) * (2 : ℝ) ^ D * (D : ℝ) ^ (14 * D ^ 2) := by
          gcongr
          linarith
  · have hbase : (40 * D : ℝ) ≤ (5 * D : ℝ) ^ 2 := by nlinarith
    calc (40 * D : ℝ) ^ D ≤ ((5 * D : ℝ) ^ 2) ^ D :=
          pow_le_pow_left₀ (by positivity) hbase _
      _ = (5 * D : ℝ) ^ (2 * D) := by rw [← pow_mul]
      _ ≤ (100 : ℝ) * (5 * D : ℝ) ^ (2 * D) := by nlinarith

/-- Raising the first Section 5 threshold to α recovers the required
10^4*2^(40D) lower bound. -/
theorem section5_rpow_threshold {α : ℝ} {D : ℕ}
    (hα0 : 0 < α) :
    (10 ^ 4 * (2 : ℝ) ^ (40 * D)) ≤
      (((10 ^ 4 : ℝ) * (2 : ℝ) ^ (40 * D)) ^ (1 / α)) ^ α := by
  have hA : (0 : ℝ) ≤ (10 ^ 4 : ℝ) * (2 : ℝ) ^ (40 * D) := by positivity
  rw [← Real.rpow_mul hA, one_div_mul_cancel hα0.ne', Real.rpow_one]

/-- Standard real-power consequence used in Section 5:
n ≤ p^(1-α) implies n/p ≤ n^(-α). -/
theorem card_div_prime_le_neg_rpow {α : ℝ} {n p : ℕ}
    (hα0 : 0 < α) (hα1 : α < 1)
    (hn : 1 ≤ n) (hp : 1 ≤ p)
    (hupper : (n : ℝ) ≤ (p : ℝ) ^ (1 - α)) :
    (n : ℝ) / p ≤ (n : ℝ) ^ (-α) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hn0 : 0 < (n : ℝ) := by linarith
  have hp0 : 0 < (p : ℝ) := by linarith
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hlogp0 : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg hp1
  have hlogupper :
      Real.log (n : ℝ) ≤ (1 - α) * Real.log (p : ℝ) := by
    have h := Real.log_le_log hn0 hupper
    rwa [Real.log_rpow hp0] at h
  -- `(1 + α) log n ≤ (1 + α)(1 - α) log p ≤ log p`.
  have hlogp :
      (1 + α) * Real.log (n : ℝ) ≤ Real.log (p : ℝ) := by
    have h1 : (1 + α) * Real.log (n : ℝ) ≤ (1 + α) * ((1 - α) * Real.log (p : ℝ)) :=
      mul_le_mul_of_nonneg_left hlogupper (by linarith)
    nlinarith [mul_nonneg (sq_nonneg α) hlogp0]
  have hleft : 0 < (n : ℝ) / p := div_pos hn0 hp0
  have hright : 0 < (n : ℝ) ^ (-α) := Real.rpow_pos_of_pos hn0 _
  rw [← Real.log_le_log_iff hleft hright, Real.log_div hn0.ne' hp0.ne', Real.log_rpow hn0]
  nlinarith [hlogp]

/-- Monotonicity of x↦x^{-α} for positive α on [1,∞). -/
theorem neg_rpow_antitone {α : ℝ} (hα : 0 < α)
    {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    y ^ (-α) ≤ x ^ (-α) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  exact Real.rpow_le_rpow_of_nonpos hx0 hxy (by linarith)

/-- Two-sided reciprocal-square-root kernel sum used for a fixed interval endpoint. -/
theorem reverse_Icc_inv_sqrt_sum (n : ℕ) :
    (∑ r ∈ Finset.Icc 1 (n - 1),
      1 / Real.sqrt ((n - r : ℕ) : ℝ)) =
    ∑ r ∈ Finset.Icc 1 (n - 1),
      1 / Real.sqrt (r : ℝ) := by
  apply Finset.sum_nbij' (fun r => n - r) (fun r => n - r)
  · intro r hr
    simp only [Finset.mem_Icc] at hr ⊢
    omega
  · intro r hr
    simp only [Finset.mem_Icc] at hr ⊢
    omega
  · intro r hr
    simp only [Finset.mem_Icc] at hr
    omega
  · intro r hr
    simp only [Finset.mem_Icc] at hr
    omega
  · intro r _
    rfl

theorem two_sided_interval_kernel_sum_le
    (n p : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    (∑ r ∈ Finset.Icc 1 (n - 1),
      ((1 / (p : ℝ) +
        C * Real.sqrt (Real.log (n : ℝ)) /
          ((n : ℝ) * Real.sqrt (r : ℝ))) +
       (1 / (p : ℝ) +
        C * Real.sqrt (Real.log (n : ℝ)) /
          ((n : ℝ) * Real.sqrt ((n - r : ℕ) : ℝ))))) ≤
      2 * (n : ℝ) / p +
        4 * C * Real.sqrt (Real.log (n : ℝ)) /
          Real.sqrt (n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  set c : ℝ := C * Real.sqrt (Real.log (n : ℝ)) / n with hc
  have hc0 : 0 ≤ c := by positivity
  have hterm : ∀ r : ℕ,
      C * Real.sqrt (Real.log (n : ℝ)) / ((n : ℝ) * Real.sqrt (r : ℝ)) =
        c * (1 / Real.sqrt (r : ℝ)) := by
    intro r
    rw [hc, div_mul_div_comm, mul_one]
  simp_rw [hterm]
  have hcount : ((Finset.Icc 1 (n - 1)).card : ℝ) ≤ n := by
    rw [Nat.card_Icc]
    exact_mod_cast (by omega : n - 1 + 1 - 1 ≤ n)
  have hs : (∑ r ∈ Finset.Icc 1 (n - 1), 1 / Real.sqrt (r : ℝ)) ≤
      2 * Real.sqrt (n : ℝ) :=
    (sum_inv_sqrt_le_two_sqrt (n - 1)).trans (by
      gcongr
      exact_mod_cast Nat.sub_le n 1)
  have hsplit : (∑ r ∈ Finset.Icc 1 (n - 1),
      ((1 / (p : ℝ) + c * (1 / Real.sqrt (r : ℝ))) +
       (1 / (p : ℝ) + c * (1 / Real.sqrt ((n - r : ℕ) : ℝ))))) =
      2 * ((Finset.Icc 1 (n - 1)).card : ℝ) / p +
        2 * c * ∑ r ∈ Finset.Icc 1 (n - 1), 1 / Real.sqrt (r : ℝ) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, reverse_Icc_inv_sqrt_sum, Finset.sum_const,
      nsmul_eq_mul]
    ring
  rw [hsplit]
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hsq : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt hnR.le
  have h1 : 2 * ((Finset.Icc 1 (n - 1)).card : ℝ) / p ≤ 2 * (n : ℝ) / p := by
    gcongr
  have h2 : 2 * c * ∑ r ∈ Finset.Icc 1 (n - 1), 1 / Real.sqrt (r : ℝ) ≤
      2 * c * (2 * Real.sqrt (n : ℝ)) := by
    gcongr
  have h3 : 2 * c * (2 * Real.sqrt (n : ℝ)) =
      4 * C * Real.sqrt (Real.log (n : ℝ)) / Real.sqrt (n : ℝ) := by
    rw [hc]
    field_simp
    rw [hsq]
    ring
  linarith

/-- Crude elementary growth used in Section 5 numerical union bounds. -/
theorem nat_le_two_pow_40 (D : ℕ) :
    (D : ℝ) ≤ (2 : ℝ) ^ (40 * D) := by
  have h1 : D < 2 ^ D := Nat.lt_two_pow_self
  have h2 : 2 ^ D ≤ 2 ^ (40 * D) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact_mod_cast (h1.le.trans h2)

/-- Elementary growth used in the Section 5 counting estimates. -/
theorem D_plus_one_le_fiveD_pow (D : ℕ) (hD : 7 ≤ D) :
    (D + 1 : ℝ) ≤ (5 * D : ℝ) ^ (2 * D) := by
  have hD7 : (7 : ℝ) ≤ D := by exact_mod_cast hD
  have hbase : (D + 1 : ℝ) ≤ (5 * D : ℝ) ^ 2 := by nlinarith
  exact hbase.trans (pow_le_pow_right₀ (by linarith) (by omega))

/-- Monotonicity of real powers in the exponent for a base at least one. -/
theorem rpow_exponent_mono_of_one_le {x a b : ℝ}
    (hx : 1 ≤ x) (hab : a ≤ b) :
    x ^ a ≤ x ^ b :=
  Real.monotone_rpow_of_base_ge_one hx hab

/-- Linear eventually dominates log-squared. -/
theorem exists_log_sq_threshold (A : ℝ) :
    ∃ N : ℕ, 2 ≤ N ∧
      ∀ n : ℕ, N ≤ n →
        A * (Real.log (n : ℝ)) ^ 2 ≤ (n : ℝ) := by
  by_cases hA : A ≤ 0
  · refine ⟨2, le_rfl, ?_⟩
    intro n _
    have h1 : A * (Real.log (n : ℝ)) ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hA (sq_nonneg _)
    have h2 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  · replace hA : 0 < A := lt_of_not_ge hA
    refine ⟨max 2 (Nat.ceil ((16 * A) ^ 2)), le_max_left _ _, ?_⟩
    intro n hn
    have hn2 : 2 ≤ n := le_trans (le_max_left _ _) hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hnB : (16 * A) ^ 2 ≤ (n : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hn)
    have hlog := Real.log_natCast_le_rpow_div n (show (0 : ℝ) < 1 / 4 by norm_num)
    have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
    set q : ℝ := (n : ℝ) ^ (1 / 4 : ℝ) with hq
    have hq0 : 0 ≤ q := by positivity
    have hq4 : q ^ 4 = n := by
      rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
      norm_num
    have hlog' : Real.log n ≤ 4 * q := by
      have : q / (1 / 4) = 4 * q := by ring
      linarith
    have h16 : 16 * A ≤ q ^ 2 := by
      have h : (16 * A) ^ 2 ≤ (q ^ 2) ^ 2 := by
        rw [← pow_mul]
        simpa [hq4] using hnB
      exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).1 h
    calc A * Real.log n ^ 2 ≤ A * (4 * q) ^ 2 := by gcongr
      _ = (16 * A) * q ^ 2 := by ring
      _ ≤ q ^ 2 * q ^ 2 := by gcongr
      _ = n := by rw [← hq4]; ring

/-- n^{-1/2} sqrt(log n) is eventually below n^{-α} for α < 1/2. -/
theorem exists_sqrt_log_power_threshold {α K : ℝ}
    (hα0 : 0 < α) (hαh : α < 1 / 2) (hK : 0 ≤ K) :
    ∃ N : ℕ, 2 ≤ N ∧
      ∀ n : ℕ, N ≤ n →
        K * Real.sqrt (Real.log (n : ℝ)) / Real.sqrt (n : ℝ) ≤
          (n : ℝ) ^ (-α) := by
  set β : ℝ := (1 / 2 - α) / 2 with hβdef
  have hβ : 0 < β := by rw [hβdef]; linarith
  set M : ℝ := K ^ 2 / (2 * β) with hMdef
  have hM : 0 ≤ M := by positivity
  refine ⟨max 2 (Nat.ceil (M ^ (1 / (2 * β)))), le_max_left _ _, ?_⟩
  intro n hn
  have hn2 : 2 ≤ n := le_trans (le_max_left _ _) hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hNpow : M ^ (1 / (2 * β)) ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hn)
  set t : ℝ := (n : ℝ) ^ (2 * β) with htdef
  have ht0 : 0 ≤ t := by positivity
  have hMt : M ≤ t := by
    have h := Real.rpow_le_rpow (by positivity) hNpow (by positivity : (0 : ℝ) ≤ 2 * β)
    rwa [← Real.rpow_mul hM, one_div_mul_cancel (by positivity), Real.rpow_one] at h
  have hlog : Real.log n ≤ t / (2 * β) := Real.log_natCast_le_rpow_div n (by positivity)
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  have hKlog : K ^ 2 * Real.log n ≤ t ^ 2 := by
    calc K ^ 2 * Real.log n ≤ K ^ 2 * (t / (2 * β)) := by gcongr
      _ = M * t := by rw [hMdef]; ring
      _ ≤ t * t := by gcongr
      _ = t ^ 2 := by ring
  have hKs : K * Real.sqrt (Real.log n) ≤ t := by
    rw [← Real.sqrt_sq hK, ← Real.sqrt_mul (sq_nonneg K)]
    calc Real.sqrt (K ^ 2 * Real.log n) ≤ Real.sqrt (t ^ 2) := Real.sqrt_le_sqrt hKlog
      _ = t := Real.sqrt_sq ht0
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
  have hrpow : (n : ℝ) ^ (-α) = t / Real.sqrt n := by
    rw [htdef, Real.sqrt_eq_rpow, ← Real.rpow_sub hn0]
    congr 1
    rw [hβdef]
    ring
  rw [hrpow]
  exact div_le_div_of_nonneg_right hKs hsqrt.le

end

end GrahamRearrangement.External
