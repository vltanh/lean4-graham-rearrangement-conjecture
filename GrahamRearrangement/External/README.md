# Results from prior work

The paper's proofs use one result from prior work: the Chernoff bound for hypergeometric
distributions, cited from S. Janson, T. Łuczak and A. Ruciński, *Random Graphs* (Wiley,
2011), Theorem 2.10 and Eq. (2.6). The proofs of Lemmas 3.1 and 3.3 apply it in two forms.
Both are proved in this directory.

| Paper's use | Lean |
| --- | --- |
| Lemma 3.1: if at least a quarter of `U` lies in `G`, a uniformly random `k`-subset of `U` has at least `k/8` elements in `G`, except with probability `e^{-k/32}` | [`GrahamRearrangement.External.hypergeom_quarter_lower_tail`](Hypergeometric/Tails.lean#L222) |
| Lemma 3.3: if at least three quarters of `U` lies in `G`, it has at least `k/2` elements in `G`, except with probability `e^{-k/24}` | [`GrahamRearrangement.External.hypergeom_three_quarters_lower_tail`](Hypergeometric/Tails.lean#L233) |

Both are deduced from Hoeffding's bound for sampling without replacement,
[`GrahamRearrangement.External.Hypergeometric.uniformSubset_hoeffding_lower_tail`](Hypergeometric/Tails.lean#L66): the number
of elements of `G` in a uniformly random `k`-subset falls at least `d` below its mean with
probability at most `exp(-2d²/k)`. With `d = k/8` this is exactly `e^{-k/32}`; with `d = k/4`
it is `e^{-k/8}`, which is at most `e^{-k/24}`. The Chernoff bound that the paper cites gives
the same two estimates.

The proof is in three files:

- [`Hypergeometric/Sampling.lean`](Hypergeometric/Sampling.lean): sampling without replacement, one draw at a time, and its
  equivalence with a uniformly random subset of fixed size;
- [`Hypergeometric/Hoeffding.lean`](Hypergeometric/Hoeffding.lean): the exposure martingale, its bounded increments, and the
  exponential-moment bound, from Mathlib's Hoeffding lemma
  [`ProbabilityTheory.mgf_le_of_mem_Icc_of_integral_eq_zero`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Moments/SubGaussian.html#ProbabilityTheory.mgf_le_of_mem_Icc_of_integral_eq_zero);
- [`Hypergeometric/Tails.lean`](Hypergeometric/Tails.lean): the lower tail for uniformly random subsets and the two
  forms above.

In the Lean statements, the thresholds `k/8` and `k/2` are natural-number quotients
(`⌊k/8⌋` and `⌊k/2⌋`), so the bad events are slightly smaller than the paper's. The proofs of
Lemmas 3.1 and 3.3 only need these.
