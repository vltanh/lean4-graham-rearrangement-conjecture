module

public import GrahamRearrangement.External.Hypergeometric.Sampling
public import GrahamRearrangement.External.Hypergeometric.Hoeffding
public import GrahamRearrangement.External.Hypergeometric.Tails

@[expose] public section

/-!
# Hypergeometric concentration

Umbrella module for the self-contained external proof used in Lemmas 3.1 and
3.3.  The implementation proves finite sampling without replacement, the
Hoeffding exponential-moment estimate, and the two numerical tail
specializations used by Pham--Sauermann.
-/
