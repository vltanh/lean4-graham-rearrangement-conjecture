module

public import GrahamRearrangement.External.Hypergeometric.Sampling
public import GrahamRearrangement.External.Hypergeometric.Hoeffding
public import GrahamRearrangement.External.Hypergeometric.Tails

@[expose] public section

/-!
# Hypergeometric concentration

The Chernoff bound for hypergeometric distributions that Pham--Sauermann cite from
Janson, Łuczak and Ruciński, *Random Graphs*, Theorem 2.10 and Eq. (2.6), in the two forms the
proofs of Lemmas 3.1 and 3.3 use. The proof goes through finite sampling without replacement
and Hoeffding's exponential-moment estimate.
-/
