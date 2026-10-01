# Graham's rearrangement conjecture for small sets — Lean formalization

[![Lean Action CI](https://github.com/vltanh/lean4-graham-rearrangement-conjecture/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/vltanh/lean4-graham-rearrangement-conjecture/actions/workflows/lean_action_ci.yml)

A Lean 4 / Mathlib formalization of H. T. Pham and L. Sauermann, *On Graham's
rearrangement conjecture* (arXiv:2602.15797v1).

Graham conjectured in 1971 that for every prime `p`, every subset `S ⊆ ℤ_p ∖ {0}` has a
*valid ordering*: an ordering `s₁, …, s_{|S|}` of its elements whose partial sums
`s₁, s₁ + s₂, …, s₁ + ⋯ + s_{|S|}` are pairwise distinct. The paper proves it for all `S`
with `C_α ≤ |S| ≤ p^{1-α}`, for any fixed `0 < α < 1` (Theorem 1.2). The main tool is an
anticoncentration bound for the sum of a uniformly random `m`-element subset of `S`
(Theorem 1.3 and Corollary 1.4).

Every result that the paper proves is proved here, following the paper's argument. The one
result from prior work that the proofs use, the Chernoff bound for hypergeometric
distributions, is proved as well, in [`GrahamRearrangement/External/`](GrahamRearrangement/External/README.md).

`lake build` succeeds with no `sorry`, and the repository declares no `axiom`: every theorem
depends only on Lean's standard axioms [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound). The script
[`scripts/Audit.lean`](scripts/Audit.lean) checks this for all 1902 declarations of the library, and lists which
results from prior work each result of the paper uses; run it with
`lake env lean scripts/Audit.lean`.

[REPORT.md](REPORT.md) is a full audit of the paper and of this formalization, made against
the arXiv source: errors and gaps, missing and redundant hypotheses, how the paper uses
each cited result, how the formalization reads each statement, and which results from prior
work each result depends on. The main findings are summarized below.

## The main results

The paper's three main results are stated in [`Challenge.lean`](Challenge.lean) with Mathlib's vocabulary only,
and proved in [`Solution.lean`](Solution.lean) from the formalization:

- [`PhamSauermann.theorem_1_2`](Challenge.lean#L45) (Theorem 1.2): for every `0 < α < 1` there is `C > 0` such that,
  for every prime `p`, every `S ⊆ ℤ_p ∖ {0}` with `C ≤ |S| ≤ p^{1-α}` has a list `l` of its
  elements, each appearing once, whose partial sums `(l.take (k + 1)).sum` are pairwise
  distinct.
- [`PhamSauermann.theorem_1_3`](Challenge.lean#L58) (Theorem 1.3): there is `C > 0` such that for every prime `p`,
  every `S ⊆ ℤ_p` with `|S| ≥ 2`, every integer `m` with `C log |S| ≤ m ≤ 10⁻³ |S| / log |S|`
  and every `z ∈ ℤ_p`, the proportion of the `m`-element subsets of `S` with sum `z` is at
  most `1/p + C / (|S| √m)`.
- [`PhamSauermann.corollary_1_4`](Challenge.lean#L72) (Corollary 1.4): for every `0 < ε < 1` there is `C > 0` such
  that the same proportion is at most `1/p + C √(log |S|) / (|S| √m)` for every positive
  integer `m ≤ (1 - ε) |S|`.

They match the paper's statements exactly; the paper's probability `ℙ[Σ(R) = z]` for a uniformly
random `m`-subset `R` is written as the number of `m`-subsets with sum `z` divided by
`(|S| choose m)`. Combined with earlier results (Bedert–Kravitz for small sets,
Bedert–Bucić–Kravitz–Montgomery–Müyesser for large sets), the paper deduces Graham's
conjecture for all sufficiently large primes; those earlier results are not formalized.

## Palomar

The repository is set up for submission to the [Palomar](https://github.com/PalomarRegistry/PalomarPolicy)
registry: [`comparator.json`](comparator.json) names the challenge and solution modules and the three theorems
above, and [`formalization.yaml`](formalization.yaml) carries the metadata. Every `.lean` file uses the module system.
To check the solution against the challenge, with [bubblewrap](https://github.com/containers/bubblewrap)
installed:

```sh
lake build
lake comparator
```

[`comparator.json`](comparator.json) asks for the NanoDa kernel, which Palomar's verifier provides. To run
Comparator without it, copy the file with `"enable_nanoda": false` and pass the copy with
`--config`; Lean's kernel then accepts the solution.

## Audit summary

References are to the paper's numbering; E-numbers refer to [`REPORT.md`](REPORT.md), §3.

**Errors in the paper.** None affects a result: every numbered result is true as stated, and
proved here. The slips, in decreasing order of substance:

- Corollary 4.2: the displayed product in the proof counts the factor `i = k` twice, and is
  only right for `1 ≤ j ≤ k − 1`; its final line is correct (E9).
- Lemma 5.5: one step of the final display replaces the constant `C_D` by `2C_D`, after
  which the next steps fail (they would need `4√2 C_D ≤ 4C_D`); with `C_D`, as in the
  previous display, they hold (E11).
- Lemma 3.2: `265t/m` should be `256t/m`; with 265 the next step (`4 · 265 ≤ 1024`) is false
  (E6).
- Section 3 twice writes `B_{32t}` where Lemma 3.3 and the proof use `B_{2000t}` (E5), and
  describes the random partition with two wrong size formulas (E4). It opens with "we
  prove Theorem 1.2", and the proof of Corollary 1.4 takes "C as in Theorem 1.2"; both mean
  Theorem 1.3 (E3, E8).
- Lemma 5.4 uses `|S|/p ≤ |S|^{1−α}` where `|S|^{−α}` is meant (E10), Lemma 5.3 writes
  `{b+5D, …, t_i}` for `{b+5D+1, …, t_i}` (E12), and Lemma 3.6 writes `χ` for `χ'` (E7).
- Fact 2.3's proof cites itself instead of Fact 2.1 (E1).

**Gaps.** Each is closed here.

- Fact 2.4's proof applies the Cauchy–Davenport theorem to sets that may be empty, where it
  is false; Fact 2.4 itself holds (E2).
- Section 3 claims `m ≥ 2^24` from `m ≥ 2^24 log |S|`, which needs `log |S| ≥ 1`; it holds
  because the two bounds on `m` force `|S|` to be huge (E3).
- Corollary 4.2's exposure argument does not treat the cases `j = 0` and `j = k` (E9).

**Missing hypotheses.** None in the statements of the paper's results. The formalization
makes the standing assumptions of each section explicit (§4 of the report).

**Redundant hypotheses.** Primality is not used in Facts 2.3 and 2.5, nor in Lemma 4.3,
which also holds for every constant `C > 0`, not only the constant `C_k` of Corollary 4.2.
The Lean statements of Facts 2.3 and 2.5 keep `p` prime, to match the paper; Lemma 4.3 is
stated for every `C > 0` ([`REPORT.md`](REPORT.md), §5).

**Use of cited results.** The proofs cite one result, the Chernoff bound for hypergeometric
distributions (Janson–Łuczak–Ruciński, *Random Graphs*, Theorem 2.10 and Eq. (2.6)), in
Lemmas 3.1 and 3.3. It is used correctly, and both of the paper's tail estimates follow; the
formalization derives them from Hoeffding's inequality for sampling without replacement.
Standard facts used without citation (Cauchy–Schwarz, Taylor's theorem, Cauchy–Davenport,
orthogonality of characters, Markov's inequality) come from Mathlib or are proved here.

## Credits

- **Formalization:** first written by ChatGPT (OpenAI, "Extra High" setting) in
  [vltanh/lean4-examples#2](https://github.com/vltanh/lean4-examples/pull/2), branch
  `formalize-graham-rearrangement`, up to commit
  [`59c67ba4912d26586d3aa77c61bffb5e081f7a0b`](https://github.com/vltanh/lean4-examples/commit/59c67ba4912d26586d3aa77c61bffb5e081f7a0b). The draft was complete at the source
  level but had never been compiled. The first commit of this repository imports it
  verbatim.
- **Compilation and fidelity:** Claude (Anthropic) set up this Lean project on current
  Mathlib, moved it to the module system, repaired the draft until it builds (proving the
  332 steps that did not compile, and correcting the 15 helper lemmas of the draft that were
  false as stated; see [`REPORT.md`](REPORT.md), §6), checked the statements against the paper, and
  wrote the Palomar challenge, the audit and this documentation.

## Building

Install [elan](https://github.com/leanprover/elan), then:

```sh
lake exe cache get   # download prebuilt Mathlib
lake build
lake env lean scripts/Audit.lean   # optional: axiom and dependency audit
```

Toolchain `leanprover/lean4:v4.35.0-rc3`; Mathlib tracks `master`, with the exact revision
pinned in [`lake-manifest.json`](lake-manifest.json).

The Markdown files link each Lean name they mention to its declaration. After editing the
Lean code, run `lake build` and then `python3 scripts/linkify_docs.py` to update the line numbers of those
links and to link new mentions; with `--check`, it only lists the files that are out of
date. It reads the declaration locations from the `.ilean` files that `lake build` writes.

## Layout

The paper, in [`GrahamRearrangement/`](GrahamRearrangement), in dependency order:

| Module | Paper content |
| --- | --- |
| [`GrahamRearrangement/Introduction.lean`](GrahamRearrangement/Introduction.lean) | §1: valid orderings; Conjecture 1.1 (stated, not proved) |
| [`GrahamRearrangement/Probability.lean`](GrahamRearrangement/Probability.lean) | Uniform probability on finite sets: conditioning, union bounds, averaging |
| [`GrahamRearrangement/Auxiliary.lean`](GrahamRearrangement/Auxiliary.lean) | Auxiliary lemmas used throughout: characters of `ℤ_p`, dyadic decompositions, numerical inequalities |
| [`GrahamRearrangement/Preliminaries.lean`](GrahamRearrangement/Preliminaries.lean) | §2: Facts 2.1–2.5 |
| [`GrahamRearrangement/BooleanSlice/Definitions.lean`](GrahamRearrangement/BooleanSlice/Definitions.lean) | §3: the slice probability, the random partition, `ψ`, `Ψ`, `A_t`, `B_t`, `D_t`, `Q_{t,δ}` |
| [`GrahamRearrangement/BooleanSlice/Auxiliary.lean`](GrahamRearrangement/BooleanSlice/Auxiliary.lean) | §3: the random partition gives a uniformly random subset; concentration for the parts |
| [`GrahamRearrangement/BooleanSlice/Fourier.lean`](GrahamRearrangement/BooleanSlice/Fourier.lean) | §3: (3.1)–(3.4) |
| [`GrahamRearrangement/BooleanSlice/Lemmas.lean`](GrahamRearrangement/BooleanSlice/Lemmas.lean) | §3: Lemmas 3.1–3.7 |
| [`GrahamRearrangement/BooleanSlice/Theorem.lean`](GrahamRearrangement/BooleanSlice/Theorem.lean) | Theorem 1.3 |
| [`GrahamRearrangement/Combinatorial/Definitions.lean`](GrahamRearrangement/Combinatorial/Definitions.lean) | §4: random chains of subsets and the bounds of Corollary 4.2 and Lemma 4.3 |
| [`GrahamRearrangement/Combinatorial/Auxiliary.lean`](GrahamRearrangement/Combinatorial/Auxiliary.lean) | §4: counting lemmas |
| [`GrahamRearrangement/Combinatorial/Lemma41.lean`](GrahamRearrangement/Combinatorial/Lemma41.lean) | Lemma 4.1 |
| [`GrahamRearrangement/Combinatorial/Corollary14.lean`](GrahamRearrangement/Combinatorial/Corollary14.lean) | Corollary 1.4 |
| [`GrahamRearrangement/Combinatorial/Corollary42.lean`](GrahamRearrangement/Combinatorial/Corollary42.lean) | Corollary 4.2 |
| [`GrahamRearrangement/Combinatorial/Lemma43.lean`](GrahamRearrangement/Combinatorial/Lemma43.lean) | Lemma 4.3 and (4.1) |
| [`GrahamRearrangement/Rearrangement/Definitions.lean`](GrahamRearrangement/Rearrangement/Definitions.lean) | §5: orderings as bijections, `B(σ)`, admissible permutations, the bad events |
| [`GrahamRearrangement/Rearrangement/IntervalLemmas.lean`](GrahamRearrangement/Rearrangement/IntervalLemmas.lean) | §5: interval sums; a valid ordering is one with no zero interval sum |
| [`GrahamRearrangement/Rearrangement/Parameters.lean`](GrahamRearrangement/Rearrangement/Parameters.lean) | §5: the parameters `D` and `C_α` |
| [`GrahamRearrangement/Rearrangement/Auxiliary.lean`](GrahamRearrangement/Rearrangement/Auxiliary.lean) | §5: permutations, conditioning on part of a random bijection, counting |
| [`GrahamRearrangement/Rearrangement/Lemma51.lean`](GrahamRearrangement/Rearrangement/Lemma51.lean) | Lemma 5.1 |
| [`GrahamRearrangement/Rearrangement/Lemma54.lean`](GrahamRearrangement/Rearrangement/Lemma54.lean) | Lemma 5.4 and (5.1) |
| [`GrahamRearrangement/Rearrangement/Lemma52.lean`](GrahamRearrangement/Rearrangement/Lemma52.lean) | Lemma 5.2 |
| [`GrahamRearrangement/Rearrangement/Lemma55.lean`](GrahamRearrangement/Rearrangement/Lemma55.lean) | Lemma 5.5 |
| [`GrahamRearrangement/Rearrangement/Reversal.lean`](GrahamRearrangement/Rearrangement/Reversal.lean) | §5: reversing the order of positions |
| [`GrahamRearrangement/Rearrangement/Lemma56.lean`](GrahamRearrangement/Rearrangement/Lemma56.lean) | Lemma 5.6 |
| [`GrahamRearrangement/Rearrangement/Lemma53.lean`](GrahamRearrangement/Rearrangement/Lemma53.lean) | Lemma 5.3 |
| [`GrahamRearrangement/Rearrangement/Repair.lean`](GrahamRearrangement/Rearrangement/Repair.lean) | §5: the greedy repair in the proof of Theorem 1.2 |
| [`GrahamRearrangement/Rearrangement/BadEvents.lean`](GrahamRearrangement/Rearrangement/BadEvents.lean) | Lemmas 5.1–5.3 together |
| [`GrahamRearrangement/Main.lean`](GrahamRearrangement/Main.lean) | Theorem 1.2 |

The hypergeometric tail bounds cited from Janson–Łuczak–Ruciński are proved in
[`GrahamRearrangement/External/Hypergeometric/`](GrahamRearrangement/External/README.md): sampling without replacement (`Sampling.lean`),
Hoeffding's inequality (`Hoeffding.lean`) and the two tail bounds (`Tails.lean`).

[`Challenge.lean`](Challenge.lean) and [`Solution.lean`](Solution.lean) state and prove Theorems 1.2, 1.3 and Corollary 1.4 in
Mathlib's vocabulary, for Palomar; [`scripts/`](scripts) holds the audit and the link checker.

## GitHub configuration

The CI workflows come from the Lake `math` template. [`lean_action_ci.yml`](.github/workflows/lean_action_ci.yml) builds
the project on every push and pull request, runs the axiom audit, and checks that the
documentation's links to the code are current; the badge above shows its status. To use the
other workflows:

- Under the repository's **Settings → Actions → General**, check **Allow GitHub
  Actions to create and approve pull requests** (used by [`update.yml`](.github/workflows/update.yml)).
- Under **Settings → Pages**, set **Source** to "GitHub Actions" (used by
  [`docs.yml`](.github/workflows/docs.yml), which publishes the API documentation).

## License

Apache-2.0; see [LICENSE](LICENSE).
