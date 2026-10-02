# Audit of the paper and the formalization

Paper: H. T. Pham and L. Sauermann, *On Graham's rearrangement conjecture*,
arXiv:2602.15797v1. The audit below was made against the arXiv LaTeX source of that
version. Section, result and equation numbers are the paper's.

Status of the formalization:

- Every result that the paper proves is proved in Lean, following the paper's argument:
  Theorems 1.2 and 1.3, Corollaries 1.4 and 4.2, Facts 2.1–2.5, Lemmas 3.1–3.7, 4.1, 4.3
  and 5.1–5.6, and the numbered equations (3.1)–(3.4), (4.1) and (5.1).
- The proofs use one result from prior work, the Chernoff bound for hypergeometric
  distributions; the two tail bounds that they take from it are proved too, in [`GrahamRearrangement/External/`](GrahamRearrangement/External/README.md).
  Standard facts that the paper uses without citation come from Mathlib or are proved here
  (Section 2).
- `lake build` succeeds. The only `sorry`s are the three placeholders of the Palomar challenge
  in [`Challenge.lean`](Challenge.lean), and the repository declares no `axiom`. The script
  [`scripts/Audit.lean`](scripts/Audit.lean) checks that every result of the paper, the two results from prior work,
  the three theorems of [`Solution.lean`](Solution.lean), and every one of the 1896 declarations of the library
  depend only on Lean's standard axioms ([`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice), [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound)).
- Theorems 1.2, 1.3 and Corollary 1.4 are restated in [`Challenge.lean`](Challenge.lean) with Mathlib's vocabulary
  only, and `lake comparator` accepts [`Solution.lean`](Solution.lean) as their proof.
- No statement of a result of the paper had to be weakened. The places where the paper's
  proofs are wrong or incomplete are listed in Section 3; in each case the formalization
  proves the result as stated.

## 1. Summary

- **Errors.** No result of the paper is false, and none of its proofs has a gap that needs a
  new idea. The proofs contain several slips that a careful reader must repair: a
  displayed product in Corollary 4.2 that counts one factor twice, a constant that doubles
  in one step of Lemma 5.5 and would break the chain of inequalities, an arithmetic typo in
  Lemma 3.2 that makes the next inequality false, and wrong cross-references and index
  ranges (Section 3).
- **Gaps.** Three small ones: the proof of Fact 2.4 recalls Cauchy–Davenport for arbitrary
  sets, where it fails if one of them is empty, Section 3 asserts `m ≥ 2^24` without the step that justifies it, and the proof of
  Corollary 4.2 does not treat the extreme cases `j = 0` and `j = k`.
- **Missing hypotheses.** None in the statements of the paper's results. Several lemmas of
  Sections 3 and 5 rely on their section's standing assumptions; the formalization states
  them as hypotheses (Section 4).
- **Redundant hypotheses.** Several statements include hypotheses that their proofs do not
  use, among them primality in Facts 2.3 and 2.5; Lemma 4.3 holds for every constant
  `C > 0`. The Lean statements omit them (Section 5).
- **Use of cited results.** The single cited result is used correctly (Section 2).

## 2. Results from prior work and how the paper uses them

### Proved in `GrahamRearrangement/External/`

| Result | Where the paper uses it | Source | Theorem in `External/` |
| --- | --- | --- | --- |
| Lower tail of the hypergeometric distribution: if `\|G\| ≥ \|U\|/4`, a uniformly random `k`-subset of `U` meets `G` in at least `k/8` elements, except with probability `e^{-k/32}` | Lemma 3.1 | Janson–Łuczak–Ruciński, *Random Graphs*, Thm 2.10 and Eq. (2.6) | [`External.hypergeom_quarter_lower_tail`](GrahamRearrangement/External/Hypergeometric/Tails.lean#L222) |
| The same with `\|G\| ≥ 3\|U\|/4`: at least `k/2` elements, except with probability `e^{-k/24}` | Lemma 3.3 | same | [`External.hypergeom_three_quarters_lower_tail`](GrahamRearrangement/External/Hypergeometric/Tails.lean#L233) |

Both are deduced from Hoeffding's inequality for sampling without replacement,
[`uniformSubset_hoeffding_lower_tail`](GrahamRearrangement/External/Hypergeometric/Tails.lean#L66), which is proved from Mathlib's Hoeffding lemma
([`ProbabilityTheory.mgf_le_of_mem_Icc_of_integral_eq_zero`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Moments/SubGaussian.html#ProbabilityTheory.mgf_le_of_mem_Icc_of_integral_eq_zero)) through an exposure martingale. With
deviation `k/8` it gives exactly `e^{-k/32}`; with deviation `k/4` it gives `e^{-k/8} ≤ e^{-k/24}`.
The Chernoff bound `exp(-t²/(2μ))` that the paper cites gives the same two numbers: the
deviation is `t = μ − k/8` (resp. `μ − k/2`), `t²/(2μ)` increases with `μ`, and the worst
cases `μ = k/4, t = k/8` and `μ = 3k/4, t = k/4` give `e^{-k/32}` and `e^{-k/24}`.

### Standard facts used without citation

| Fact | Where | In the formalization |
| --- | --- | --- |
| Cauchy–Schwarz inequality | Fact 2.1 | Mathlib, [`Multiset.sq_sum_le_card_mul_sum_sq`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Order/Chebyshev.html#Multiset.sq_sum_le_card_mul_sum_sq) |
| Taylor's theorem with Lagrange remainder | Fact 2.2 | Mathlib, [`taylor_mean_remainder_lagrange_iteratedDeriv`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/Taylor.html#taylor_mean_remainder_lagrange_iteratedDeriv) |
| Cauchy–Davenport theorem | Fact 2.4 | Mathlib, [`ZMod.cauchy_davenport`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/Additive/CauchyDavenport.html#ZMod.cauchy_davenport) |
| Orthogonality of the additive characters of `ℤ_p` | (3.1); Lemma 3.6 | [`Auxiliary.zmod_character_orthogonality`](GrahamRearrangement/Auxiliary.lean#L41), from Mathlib's [`AddChar.sum_mulShift`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LegendreSymbol/AddCharacter.html#AddChar.sum_mulShift) |
| A random balanced partition followed by one uniform choice per part gives a uniformly random `m`-subset ("it is easy to see") | §3, start | [`Section3.sliceMass_eq_partition_average`](GrahamRearrangement/BooleanSlice/Auxiliary.lean#L275) |
| Markov's inequality | Lemma 3.5 | [`Auxiliary.uniform_markov`](GrahamRearrangement/Auxiliary.lean#L88) |
| Union bounds, conditioning, exposure of a uniformly random chain or bijection one block at a time | §3–§5 | [`GrahamRearrangement/Probability.lean`](GrahamRearrangement/Probability.lean) and the `Auxiliary.lean` files |

The paper's other citations (Graham; Erdős–Graham; Bedert–Kravitz; Kravitz; Sawin;
Müyesser–Pokrovskiy; Bucić–Frederickson–Müyesser–Pokrovskiy–Yepremyan;
Bedert–Bucić–Kravitz–Montgomery–Müyesser; Nguyen–Vu; Alspach–Liversidge; Costa–Pellegrini)
give context and are not used in the proofs.

### Does the paper use each cited result correctly?

| Cited result | Where | Verdict |
| --- | --- | --- |
| Janson–Łuczak–Ruciński, Thm 2.10 and Eq. (2.6) | Lemmas 3.1, 3.3 | Correct. The paper conditions on the part containing a fixed element, so that the rest of that part is a uniformly random subset of `S ∖ {x'}` of a known size `k ≥ \|S\|/(2m)`, and applies the lower tail with the densities `1/4` and `3/4`; both exponents check out. |
| Cauchy–Davenport (uncited) | Fact 2.4 | Correct for nonempty sets, but stated for arbitrary sets; see E2. |
| Bedert–Kravitz and Bedert–Bucić–Kravitz–Montgomery–Müyesser | §1 | Not used in any proof. After Theorem 1.2, and in the abstract, the paper states without further argument that Theorem 1.2 together with "the earlier results discussed above" settles the conjecture for all sufficiently large primes; the earlier results needed are these two, for `\|S\| ≤ exp((log p)^{1/4})` and `\|S\| ≥ p^{1−c}`. That consequence is not formalized (Section 8). |

## 3. Errors and gaps in the paper

**E1. Fact 2.3.** The proof says "it follows from Fact 2.3", the fact being proved; it means
Fact 2.1, which it applies to the representatives `y_i/p`.

**E2. Fact 2.4.** The proof recalls the Cauchy–Davenport theorem as "for any subsets
`A, B ⊆ ℤ_p` with `A + B ≠ ℤ_p`, we have `|A + B| ≥ |A| + |B| − 1`". This is false when one of
the sets is empty and the other has at least two elements; the theorem needs `A, B`
nonempty. Fact 2.4 is still true: if `A = ∅` then `|kA| = 0 ≥ 1 − k`, and if `A ≠ ∅` every
`jA` is nonempty and the induction goes through. [`fact2_4`](GrahamRearrangement/Preliminaries.lean#L393) is stated over the integers, so
that `1 + k(|A| − 1)` may be negative, and treats `A = ∅` separately.

**E3. The setup of Section 3.**

- "In this section, we prove Theorem 1.2, taking `C = 2^24`" should read Theorem 1.3, and so
  should "in the statement of Theorem 1.2 we consider a uniformly random subset `R ⊆ S` of
  size `m`", a few lines later.
- "Note that this in particular implies `|S| ≥ m ≥ 2^24 ≥ 10^7`": from `m ≥ 2^24 log |S|`,
  the bound `m ≥ 2^24` needs `log |S| ≥ 1`. It holds, because the two bounds on `m` give
  `2^24 (log |S|)² ≤ 10⁻³ |S|`, which forces `|S| > 10^{13}`; for `|S| = 2` there is no
  admissible `m` at all. The formalization never derives `m ≥ 2^24`: from
  `m ≥ 2^24 log |S| ≥ 2^24 log 2` it gets `m ≥ 10^7` and `|S| ≥ 10^7`
  ([`section3_basic_bounds`](GrahamRearrangement/BooleanSlice/Lemmas.lean#L93)), and `m ≥ 2^23` ([`theorem13_m_ge`](GrahamRearrangement/BooleanSlice/Theorem.lean#L57)).

**E4. The random partition (§3).** "`|S_1| ≥ |S_2| ≥ ⋯ ≥ |S_m| ≥ |S_m| − 1`" should end with
`|S_1| − 1`, and "exactly the first `|S| − m⌊|S|/m⌋` of the sets have size `⌈|S|/m⌉ + 1`"
should read `⌊|S|/m⌋ + 1`, as the same parenthesis says just before.
The random choices are written `X = (X_1, …, X_n)` twice; `n` should be `m`. In the
computation of `|𝔼_X[χ(X_i)]|`, the summand `χ(X_i)` should be `χ(x)`.

**E5. `B_{32t}` and `B_{2000t}` (§3).** Two transition passages (before Lemma 3.1 and before
the definition of `y_χ`) announce that every `χ ∈ D_t ∖ B_{32t}` lies in `A_t` with small
probability; the first also says that `|B_{32t}|` will be bounded. Lemmas 3.2 and 3.3 and
the final computation use `B_{2000t}`, and the formalization follows them.

**E6. Lemma 3.2.** The contribution of `S ∩ J_{χ,t}` is bounded by `|S ∩ J_{χ,t}| · 265t/m`,
and the next step bounds `(4|S ∩ J_{χ,t}|/|S|) · 265t/m` by `1024t/m`, which needs
`4 · 265 ≤ 1024`, false. The radius of `J_{χ,t}` is `16√(t/m)`, so the bound is `256t/m`, and
`4 · 256 = 1024`. The lemma would survive the typo,
since `(2000 − 1060)/4 ≥ 200`. [`lemma3_2`](GrahamRearrangement/BooleanSlice/Lemmas.lean#L314) is proved with 256. It holds for any choice of the
centre `y_χ`: the hypothesis `χ ∈ D_t`, which the paper needs to define `y_χ`, is not used in
the proof, and the Lean statement omits it.

**E7. Lemma 3.6.** In the first display of the proof, the second factor
`Σ_{χ' ∈ B_t} e_p(χx)` should be `Σ_{χ' ∈ B_t} e_p(χ'x)`.

**E8. Corollary 1.4.** The proof starts "let the constant `C > 0` be as in Theorem 1.2"; it
means Theorem 1.3, which the proof then applies.

**E9. Corollary 4.2.** After fixing `j` with `m_{j+1} − m_j ≥ |S|/(k+1)`, the proof exposes
`R_1, R_2 ∖ R_1, …, R_j ∖ R_{j−1}`, then the complements `R'_k, R'_{k−1} ∖ R'_k, …`.

- The final display multiplies the factor for `S ∖ R_k` (the term `m_{k+1} − m_k`) with
  `∏_{i=j+1}^{k}`, whose last factor is the same term. The product should run over
  `i = j+1, …, k−1`. The display's last line, `∏_{i ∈ {0,…,k} ∖ {j}}`, is the correct bound.
- The display is written for `1 ≤ j ≤ k − 1`. For `j = 0` there is no first factor, and for
  `j = k` there is no factor for `S ∖ R_k` (nothing is exposed after `R_k`). The proof does
  not mention these cases; the bound `∏_{i ≠ j}` holds in both.

The formalization exposes the blocks in an arbitrary order and counts directly
([`chainMass_fixed_gap_product_bound`](GrahamRearrangement/Combinatorial/Corollary42.lean#L1376)), which covers every `j` uniformly.

**E10. Lemma 5.4.** The proof of (5.1) recalls "`|S|/p ≤ |S|^{1−α}`"; Section 5's setup
established, and the computation uses, `|S|/p ≤ |S|^{−α}`.

**E11. Lemma 5.5.** In the final display, the change of variables `m_i = x_i − b'` is written
as an equality but replaces the constant `C_D` in every factor by `2C_D`. Two steps later,
Lemma 4.3 turns the constant `c` of the factors into `2c`, and the display writes `2C_D`,
which is correct only for `c = C_D`. With `c = 2C_D`, Lemma 4.3 gives `4C_D`, and the following step,
which uses `s ≥ |S|/2`, would need `4√2 C_D ≤ 4C_D`. The two middle lines should keep `C_D`,
as the display before them does; the conclusion is then correct.

**E12. Lemma 5.3.** In the proof that `t_1, …, t_D` are distinct (event `E_1`), the set
`π(π_{b,y_i}({b+5D+1, …, t_i}))` is rewritten as `π({b+5D, …, t_i})`; it should be
`π({b+5D+1, …, t_i})`, as in the line before. The same slip recurs twice right after the
display (for `t_i` and for `t_j`).
The argument is unaffected.

**E13. Typos.** "the a conjecture" (§1); "For any `0 < ε < 1` There exists" (Corollary 1.4);
"we give the proof of out main result" and "plan to return Alspach's conjecture" (§1); "let
`m` be a positive integers" (§3); "the uniformly random subset `R ⊆ S` of size `R`" (proof of
Lemma 4.1); "`R_1 ⊆ R_1 ⊆ ⋯ ⊆ R_k`", three times (§4); "the sum on the right-hand side of
(4.1) is has exactly one term" (proof of Lemma 4.3), where the sum is on the left-hand side.

## 4. Missing hypotheses

The statements of the paper's results need no further hypotheses. Several lemmas of
Sections 3 and 5 are stated without the standing assumptions of their section, which their
proofs use: in Section 3, `p` prime, `|S| ≥ 2` and `2^24 log |S| ≤ m ≤ 10⁻³ |S|/log |S|`; in
Section 5, `0 < α < 1/2`, the choice of `D` and `C_α`, and `S ⊆ ℤ_p ∖ {0}` with
`C_α ≤ |S| ≤ p^{1−α}`. The formalization states what each proof uses:

| Where | Standing assumption used | In the formalization |
| --- | --- | --- |
| Lemmas 3.1, 3.3 | the range of `m` (for the union bounds `\|S\| e^{−\|S\|/(64m)} ≤ \|S\|^{−9}` in Lemma 3.1 and `\|S\| e^{−\|S\|/(48m)} ≤ \|S\|^{−9}` in Lemma 3.3) | [`lemma3_1`](GrahamRearrangement/BooleanSlice/Lemmas.lean#L559) and [`lemma3_3`](GrahamRearrangement/BooleanSlice/Lemmas.lean#L613) assume it |
| Lemma 3.4 | `\|S\| ≥ 10^7`, for `1 + k(9\|S\|/10 − 1) ≥ 4k\|S\|/5` | [`lemma3_4`](GrahamRearrangement/BooleanSlice/Lemmas.lean#L1049) assumes `10^7 ≤ \|S\|` |
| Lemma 3.5 | `S` nonempty, `m ≥ 1` | [`lemma3_5`](GrahamRearrangement/BooleanSlice/Lemmas.lean#L700) assumes both |
| Lemmas 5.1–5.6 | `0 < α < 1/2`, `D = ⌈3/α⌉`, the conditions on `C_α` of §5, and `0 ∉ S`, `C_α ≤ \|S\| ≤ p^{1−α}` | `D` and the conditions on `C_α` are packaged as [`Section5Parameters`](GrahamRearrangement/Rearrangement/Parameters.lean#L40), and `0 ∉ S`, `C_α ≤ \|S\| ≤ p^{1−α}` as [`Section5Regime`](GrahamRearrangement/Rearrangement/Parameters.lean#L114); `0 < α < 1/2` are separate hypotheses of each lemma |

## 5. Redundant hypotheses

Hypotheses that the paper's statements include but its proofs do not use. The Lean
statements omit them, so each Lean statement implies the paper's; the statements of
Theorems 1.2, 1.3 and Corollary 1.4 in [`Challenge.lean`](Challenge.lean) are exactly the paper's.

| Result | Hypothesis that is not needed | Lean |
| --- | --- | --- |
| Fact 2.3 | `p` prime: the fact holds in `ℤ_n` for every `n ≥ 1` | [`fact2_3`](GrahamRearrangement/Preliminaries.lean#L304) |
| Fact 2.5 | `p` prime | [`fact2_5`](GrahamRearrangement/Preliminaries.lean#L456) |
| (3.4) | most of the range of `m`: only `1 ≤ m ≤ \|S\|/4` is assumed (which forces `\|S\| ≥ 4`) | [`equation_3_4`](GrahamRearrangement/BooleanSlice/Fourier.lean#L501) |
| Lemma 3.1 | `t ≥ 1`: for `t = 0` the event `ψ(χ) < 0` is empty | [`lemma3_1`](GrahamRearrangement/BooleanSlice/Lemmas.lean#L559) |
| Lemma 3.2 | `χ ∈ D_t`, which the paper needs only to define `y_χ` (E6) | [`lemma3_2`](GrahamRearrangement/BooleanSlice/Lemmas.lean#L314) |
| Lemma 3.6 | `t ≥ 1` | [`lemma3_6`](GrahamRearrangement/BooleanSlice/Lemmas.lean#L899) |
| Lemma 3.7 | `t ≥ 1` and `δ > 0` | [`lemma3_7`](GrahamRearrangement/BooleanSlice/Lemmas.lean#L1002) |
| Lemma 4.3 | that the constant is the `C_k` of Corollary 4.2: every `C > 0` works, and every `n ≥ 2` in place of `\|S\|` | [`lemma4_3`](GrahamRearrangement/Combinatorial/Lemma43.lean#L128) (keeps `p` prime, of which the proof uses only `p > 0`) |
| Lemma 5.5 | `b' ≤ \|S\| − 2`: `b ≥ 2` and `b' − b = 5D` suffice | [`lemma5_5`](GrahamRearrangement/Rearrangement/Lemma55.lean#L630) |

In Lemma 3.2, `y_χ` is defined (as [`centerAt`](GrahamRearrangement/BooleanSlice/Definitions.lean#L520)) for every `χ`, and the bound holds for that
centre whether or not `χ ∈ D_t`. Section 5 applies Lemma 4.3 to the ground set
`S ∖ {σ(b), …, σ(b')}` of size `s`, as the paper does.

## 6. How the formalization reads the paper

- **Probability.** Every probability space in the paper is finite and uniform. A
  probability is a proportion of a finite set ([`uniformMass`](GrahamRearrangement/Probability.lean#L22)); conditional
  probabilities and expectations are proportions and averages over finite sets.
- **Valid orderings.** An ordering of `S` is a list of its elements, each appearing once,
  and it is valid when its partial sums are pairwise distinct ([`HasValidOrdering`](GrahamRearrangement/Introduction.lean#L62)). Section 5
  works with bijections `σ : {1, …, |S|} → S`, as the paper does; positions are `Fin |S|`,
  and [`paperPos`](GrahamRearrangement/Rearrangement/Definitions.lean#L37) converts them to the paper's `1, …, |S|`. [`valid_iff_noZeroPaperSegments`](GrahamRearrangement/Rearrangement/IntervalLemmas.lean#L141)
  proves the paper's reformulation: for `0 ∉ S`, the ordering is valid if and only if
  `Σ(σ, [a, b]) ≠ 0` for all `2 ≤ a < b ≤ |S|`.
- **Theorem 1.3 and Corollary 1.4.** "`max_z ℙ[Σ(R) = z] ≤ …`" is read as "for every `z`";
  `ℙ[Σ(R) = z]` is [`sliceMass`](GrahamRearrangement/BooleanSlice/Definitions.lean#L22), the proportion of the `m`-subsets of `S` with sum `z`. In
  [`Challenge.lean`](Challenge.lean) this proportion is written out with Mathlib's [`Finset.powersetCard`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Powerset.html#Finset.powersetCard). The
  integer `m` of Theorem 1.3 is a natural number; the lower bound `C log |S| ≤ m` excludes
  `m ≤ 0` anyway.
- **The random partition of Section 3.** The partition `S = S_1 ∪ ⋯ ∪ S_m` is uniform among
  the partitions into `m` labelled parts with the prescribed sizes ([`balancedPartitions`](GrahamRearrangement/BooleanSlice/Definitions.lean#L229));
  the choices `X_i ∈ S_i` are then independent and uniform. That this produces a uniformly
  random `m`-subset is proved ([`Section3.sliceMass_eq_partition_average`](GrahamRearrangement/BooleanSlice/Auxiliary.lean#L275)).
- **Equations (3.1) and (3.2)** are proved together, as [`conditional_sum_mass_le_exp_psi`](GrahamRearrangement/BooleanSlice/Fourier.lean#L252).
- **Natural-number quotients.** Where the paper counts "at least `|S|/(16m)`" or "at least
  `k/8`" elements, the Lean statements use natural-number quotients (`⌊|S|/(16m)⌋`,
  `⌊k/8⌋`). These counts are slightly smaller than the paper's. The paper's computation in
  Lemma 3.1 gives exactly `ψ(χ) ≥ 2t`, with no room for the rounding, so the formal proof
  bounds the parts by `|S_i| ≤ ⌊|S|/m⌋ + 1` instead of `√2 |S|/m`, and uses `|S| ≥ 32m`,
  which follows from the range of `m`.
- **Theorem 1.3 with `C = 2^24`.** The paper's proof fixes `C = 2^24`, and [`theorem13_explicit`](GrahamRearrangement/BooleanSlice/Theorem.lean#L342)
  proves the theorem with that constant; [`theorem13`](GrahamRearrangement/BooleanSlice/Theorem.lean#L455) is the existential form.
- **Corollary 4.2.** A chain `R_1 ⊆ ⋯ ⊆ R_k` with prescribed sizes is a tuple of nested
  subsets ([`chainFamily`](GrahamRearrangement/Combinatorial/Definitions.lean#L23); [`chainMass`](GrahamRearrangement/Combinatorial/Definitions.lean#L31) is the probability on it); "integers `1 ≤ m_1 < ⋯ < m_k < |S|`" is [`IsChainSizeTuple`](GrahamRearrangement/Combinatorial/Definitions.lean#L61). The right-hand side is
  [`chainUpperBound`](GrahamRearrangement/Combinatorial/Definitions.lean#L54).
- **Section 5.** The reduction to `α < 1/2` is part of [`theorem12_of_section5_bounds`](GrahamRearrangement/Main.lean#L57). The
  bad events `B_0, …, B_3` are [`BadEvent0`](GrahamRearrangement/Rearrangement/Definitions.lean#L872)–[`BadEvent3`](GrahamRearrangement/Rearrangement/Definitions.lean#L864), `B(σ)` is [`badRightEndpoints`](GrahamRearrangement/Rearrangement/Definitions.lean#L237), and admissible
  permutations are [`IsAdmissiblePermutation`](GrahamRearrangement/Rearrangement/Definitions.lean#L493). As in the paper, the event of Lemma 5.5 involves only the right end
  `b'` of the window ([`Lemma55Event`](GrahamRearrangement/Rearrangement/Definitions.lean#L498)), and that of Lemma 5.6 only the left end `b` ([`Lemma56Event`](GrahamRearrangement/Rearrangement/Definitions.lean#L512)); the
  other end enters through the hypotheses. Lemma 5.6, which the paper obtains "by flipping the
  ordering", is deduced from Lemma 5.5 by an explicit reversal of positions
  ([`GrahamRearrangement/Rearrangement/Reversal.lean`](GrahamRearrangement/Rearrangement/Reversal.lean)). The greedy construction of `y_1, …, y_ℓ` in the
  proof of Theorem 1.2 is [`section5_local_repair`](GrahamRearrangement/Rearrangement/Repair.lean#L510).
- **Constants.** Where the paper proves the existence of a constant, the formal proof
  sometimes uses a different explicit one. For Corollary 1.4 it is
  `4N³ + 2√C + 2C + 50C/ε²`, where `C = 2^24` and `N` is a size threshold: one term for
  each case of the proof (small `|S|`, `m ≤ C log |S|`, the range of Theorem 1.3, and
  `m ≥ 10⁻³ |S|/log |S|`). In the last case the paper gets `50Cε^{−3/2}` and the formal proof
  `50C/ε²`. Only existence is claimed.

## 7. What each result depends on

Computed by [`scripts/Audit.lean`](scripts/Audit.lean). Every result depends only on the standard axioms. The last
column lists the results from prior work that the proof uses; "–" means none. "Both" means
[`External.hypergeom_quarter_lower_tail`](GrahamRearrangement/External/Hypergeometric/Tails.lean#L222) and [`External.hypergeom_three_quarters_lower_tail`](GrahamRearrangement/External/Hypergeometric/Tails.lean#L233). Section 3 needs them
through Lemmas 3.1 and 3.3, and every later result that uses Theorem 1.3 (Corollaries 1.4 and
4.2, Lemmas 5.1–5.6, Theorem 1.2) needs them through it.

| Result | Lean | Results from prior work used |
| --- | --- | --- |
| Thm 1.2 | [`theorem12`](GrahamRearrangement/Main.lean#L87) | both |
| Thm 1.3 | [`theorem13`](GrahamRearrangement/BooleanSlice/Theorem.lean#L455), [`theorem13_explicit`](GrahamRearrangement/BooleanSlice/Theorem.lean#L342) | both |
| Cor 1.4 | [`corollary14`](GrahamRearrangement/Combinatorial/Corollary14.lean#L376) | both |
| Fact 2.1 | [`fact2_1`](GrahamRearrangement/Preliminaries.lean#L95) | – |
| Fact 2.2 | [`fact2_2`](GrahamRearrangement/Preliminaries.lean#L183) | – |
| Fact 2.3 | [`fact2_3`](GrahamRearrangement/Preliminaries.lean#L304) | – |
| Fact 2.4 | [`fact2_4`](GrahamRearrangement/Preliminaries.lean#L393) | – |
| Fact 2.5 | [`fact2_5`](GrahamRearrangement/Preliminaries.lean#L456) | – |
| (3.1), (3.2) | [`conditional_sum_mass_le_exp_psi`](GrahamRearrangement/BooleanSlice/Fourier.lean#L252) | – |
| (3.3) | [`psi_lower_bound`](GrahamRearrangement/BooleanSlice/Fourier.lean#L287) | – |
| (3.4) | [`equation_3_4`](GrahamRearrangement/BooleanSlice/Fourier.lean#L501) | – |
| Lemma 3.1 | [`lemma3_1`](GrahamRearrangement/BooleanSlice/Lemmas.lean#L559) | [`External.hypergeom_quarter_lower_tail`](GrahamRearrangement/External/Hypergeometric/Tails.lean#L222) |
| Lemma 3.2 | [`lemma3_2`](GrahamRearrangement/BooleanSlice/Lemmas.lean#L314) | – |
| Lemma 3.3 | [`lemma3_3`](GrahamRearrangement/BooleanSlice/Lemmas.lean#L613) | [`External.hypergeom_three_quarters_lower_tail`](GrahamRearrangement/External/Hypergeometric/Tails.lean#L233) |
| Lemma 3.4 | [`lemma3_4`](GrahamRearrangement/BooleanSlice/Lemmas.lean#L1049) | – |
| Lemma 3.5 | [`lemma3_5`](GrahamRearrangement/BooleanSlice/Lemmas.lean#L700) | – |
| Lemma 3.6 | [`lemma3_6`](GrahamRearrangement/BooleanSlice/Lemmas.lean#L899) | – |
| Lemma 3.7 | [`lemma3_7`](GrahamRearrangement/BooleanSlice/Lemmas.lean#L1002) | – |
| Lemma 4.1 | [`lemma4_1`](GrahamRearrangement/Combinatorial/Lemma41.lean#L43) | – |
| Cor 4.2 | [`corollary42`](GrahamRearrangement/Combinatorial/Corollary42.lean#L1424), [`corollary42_one_bound`](GrahamRearrangement/Combinatorial/Corollary42.lean#L1531) (`k = 1`) | both |
| Lemma 4.3 | [`lemma4_3`](GrahamRearrangement/Combinatorial/Lemma43.lean#L128) | – |
| (4.1) | [`equation_4_1`](GrahamRearrangement/Combinatorial/Lemma43.lean#L78) | – |
| Lemma 5.1 | [`lemma5_1`](GrahamRearrangement/Rearrangement/Lemma51.lean#L185) | both |
| Lemma 5.2 | [`lemma5_2`](GrahamRearrangement/Rearrangement/Lemma52.lean#L496) | both |
| Lemma 5.3 | [`lemma5_3`](GrahamRearrangement/Rearrangement/Lemma53.lean#L621) | both |
| Lemma 5.4 | [`lemma5_4`](GrahamRearrangement/Rearrangement/Lemma54.lean#L354) | both |
| (5.1) | [`equation_5_1`](GrahamRearrangement/Rearrangement/Lemma54.lean#L221) | both |
| Lemma 5.5 | [`lemma5_5`](GrahamRearrangement/Rearrangement/Lemma55.lean#L630) | both |
| Lemma 5.6 | [`lemma5_6`](GrahamRearrangement/Rearrangement/Lemma56.lean#L20) | both |
| Lemmas 5.1–5.3 together | [`section5_bad_event_bounds`](GrahamRearrangement/Rearrangement/BadEvents.lean#L34) | both |
| Repair step in the proof of Thm 1.2 | [`section5_local_repair`](GrahamRearrangement/Rearrangement/Repair.lean#L510) | – |

## 8. Not formalized

- Conjecture 1.1 itself, and the paper's statement (in the abstract and after Theorem 1.2,
  without further argument) that Theorem 1.2 together with earlier results settles it for
  all sufficiently large primes; the results needed are those of Bedert–Kravitz (small
  sets, `|S| ≤ exp((log p)^{1/4})`) and Bedert–Bucić–Kravitz–Montgomery–Müyesser (large sets,
  `|S| ≥ p^{1−c}`). Those results are not formalized;
  [`Conjecture11Statement`](GrahamRearrangement/Introduction.lean#L82) only records the conjecture.
- The survey of earlier work and the proof overview in §1, and the remark on Alspach's
  conjecture.
