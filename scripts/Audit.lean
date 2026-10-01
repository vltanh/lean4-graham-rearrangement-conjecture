module

public meta import Lean.Elab.Command
import all GrahamRearrangement.Auxiliary
import all GrahamRearrangement.BooleanSlice
import all GrahamRearrangement.BooleanSlice.Auxiliary
import all GrahamRearrangement.BooleanSlice.Definitions
import all GrahamRearrangement.BooleanSlice.Fourier
import all GrahamRearrangement.BooleanSlice.Lemmas
import all GrahamRearrangement.BooleanSlice.Theorem
import all GrahamRearrangement.Combinatorial
import all GrahamRearrangement.Combinatorial.Auxiliary
import all GrahamRearrangement.Combinatorial.Corollary14
import all GrahamRearrangement.Combinatorial.Corollary42
import all GrahamRearrangement.Combinatorial.Definitions
import all GrahamRearrangement.Combinatorial.Lemma41
import all GrahamRearrangement.Combinatorial.Lemma43
import all GrahamRearrangement.External.Hypergeometric
import all GrahamRearrangement.External.Hypergeometric.Hoeffding
import all GrahamRearrangement.External.Hypergeometric.Sampling
import all GrahamRearrangement.External.Hypergeometric.Tails
import all GrahamRearrangement.Introduction
import all GrahamRearrangement.Main
import all GrahamRearrangement.Preliminaries
import all GrahamRearrangement.Probability
import all GrahamRearrangement.Rearrangement
import all GrahamRearrangement.Rearrangement.Auxiliary
import all GrahamRearrangement.Rearrangement.BadEvents
import all GrahamRearrangement.Rearrangement.Definitions
import all GrahamRearrangement.Rearrangement.IntervalLemmas
import all GrahamRearrangement.Rearrangement.Lemma51
import all GrahamRearrangement.Rearrangement.Lemma52
import all GrahamRearrangement.Rearrangement.Lemma53
import all GrahamRearrangement.Rearrangement.Lemma54
import all GrahamRearrangement.Rearrangement.Lemma55
import all GrahamRearrangement.Rearrangement.Lemma56
import all GrahamRearrangement.Rearrangement.Parameters
import all GrahamRearrangement.Rearrangement.Repair
import all GrahamRearrangement.Rearrangement.Reversal
import all Solution

/-!
# Axiom and dependency audit

Run with `lake env lean scripts/Audit.lean` after `lake build`.

For every numbered result of the paper, this prints the axioms it depends on and the results from
prior work (`GrahamRearrangement/External/`) that its proof uses. It then checks every declaration
of the library and the three theorems of `Solution.lean`. The run fails if any of them depends on
an axiom other than Lean's standard `propext`, `Classical.choice` and `Quot.sound` (a `sorry`
shows up as the axiom `sorryAx`).

The library's modules are imported with `import all`, which makes the proofs of their theorems
available: the module system does not export them otherwise.
-/

open Lean Elab Command

namespace Audit

/-- The results from prior work, proved in `GrahamRearrangement/External/`, with a short label. -/
meta def externalResults : List (String × Name) :=
  [("hypergeometric tail, density 1/4", ``GrahamRearrangement.External.hypergeom_quarter_lower_tail),
   ("hypergeometric tail, density 3/4",
     ``GrahamRearrangement.External.hypergeom_three_quarters_lower_tail)]

/-- The numbered results of the paper, in the order of the paper. -/
meta def paperResults : List (String × Name) :=
  [("Thm 1.2", ``GrahamRearrangement.theorem12),
   ("Thm 1.3", ``GrahamRearrangement.theorem13),
   ("Thm 1.3 (C = 2^24)", ``GrahamRearrangement.theorem13_explicit),
   ("Cor 1.4", ``GrahamRearrangement.corollary14),
   ("Fact 2.1", ``GrahamRearrangement.fact2_1),
   ("Fact 2.2", ``GrahamRearrangement.fact2_2),
   ("Fact 2.3", ``GrahamRearrangement.fact2_3),
   ("Fact 2.4", ``GrahamRearrangement.fact2_4),
   ("Fact 2.5", ``GrahamRearrangement.fact2_5),
   ("(3.1), (3.2)", ``GrahamRearrangement.conditional_sum_mass_le_exp_psi),
   ("(3.3)", ``GrahamRearrangement.psi_lower_bound),
   ("(3.4)", ``GrahamRearrangement.equation_3_4),
   ("Lemma 3.1", ``GrahamRearrangement.lemma3_1),
   ("Lemma 3.2", ``GrahamRearrangement.lemma3_2),
   ("Lemma 3.3", ``GrahamRearrangement.lemma3_3),
   ("Lemma 3.4", ``GrahamRearrangement.lemma3_4),
   ("Lemma 3.5", ``GrahamRearrangement.lemma3_5),
   ("Lemma 3.6", ``GrahamRearrangement.lemma3_6),
   ("Lemma 3.7", ``GrahamRearrangement.lemma3_7),
   ("Lemma 4.1", ``GrahamRearrangement.lemma4_1),
   ("Cor 4.2", ``GrahamRearrangement.corollary42),
   ("Cor 4.2 (k = 1)", ``GrahamRearrangement.corollary42_one_bound),
   ("Lemma 4.3", ``GrahamRearrangement.lemma4_3),
   ("(4.1)", ``GrahamRearrangement.equation_4_1),
   ("Lemma 5.1", ``GrahamRearrangement.lemma5_1),
   ("Lemma 5.2", ``GrahamRearrangement.lemma5_2),
   ("Lemma 5.3", ``GrahamRearrangement.lemma5_3),
   ("Lemma 5.4", ``GrahamRearrangement.lemma5_4),
   ("(5.1)", ``GrahamRearrangement.equation_5_1),
   ("Lemma 5.5", ``GrahamRearrangement.lemma5_5),
   ("Lemma 5.6", ``GrahamRearrangement.lemma5_6),
   ("Lemmas 5.1–5.3 combined", ``GrahamRearrangement.section5_bad_event_bounds),
   ("Repair step of §5", ``GrahamRearrangement.section5_local_repair)]

/-- The theorems that Palomar's comparator checks. -/
meta def solutionResults : List Name :=
  [``PhamSauermann.theorem_1_2, ``PhamSauermann.theorem_1_3, ``PhamSauermann.corollary_1_4]

/-- Lean's standard axioms. -/
meta def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Whether `m` is a module of the library. -/
meta def isLibraryModule (m : Name) : Bool := (`GrahamRearrangement).isPrefixOf m

/-- The constants declared in the library. -/
meta def libraryConstants (env : Environment) : NameSet := Id.run do
  let mut s : NameSet := {}
  for m in env.header.moduleNames, d in env.header.moduleData do
    if isLibraryModule m then
      for c in d.constNames do
        s := s.insert c
  return s

/-- The constants used by the type and the value of `c`. -/
meta def usedConstants (env : Environment) (c : Name) : Array Name :=
  match env.find? c with
  | some (.thmInfo t) => t.type.getUsedConstants ++ t.value.getUsedConstants
  | some (.defnInfo d) => d.type.getUsedConstants ++ d.value.getUsedConstants
  | some (.opaqueInfo o) => o.type.getUsedConstants ++ o.value.getUsedConstants
  | some (.inductInfo i) => i.type.getUsedConstants ++ i.ctors.toArray
  | some ci => ci.type.getUsedConstants
  | none => #[]

/-- The external results reached from `root` through constants of the library, without looking
inside the proofs of the external results themselves. `deps` caches the constants of the library
that each constant uses, across calls. -/
meta def externalUses (env : Environment) (library : NameSet) (deps : NameMap (Array Name))
    (root : Name) :
    List Name × NameMap (Array Name) := Id.run do
  let externals := externalResults.map (·.2)
  let mut deps := deps
  let mut visited : NameSet := {}
  let mut stack : List Name := [root]
  let mut found : NameSet := {}
  while true do
    match stack with
    | [] => break
    | c :: rest =>
      stack := rest
      if visited.contains c then continue
      visited := visited.insert c
      if c != root && externals.contains c then
        found := found.insert c
        continue
      let ds := match deps.find? c with
        | some ds => ds
        | none => (usedConstants env c).filter library.contains
      deps := deps.insert c ds
      for d in ds do
        if !visited.contains d then stack := d :: stack
  return (externalResults.filterMap fun (_, n) => if found.contains n then some n else none, deps)

elab "#audit" : command => do
  let env ← getEnv
  let mut bad : Array Name := #[]
  let library := libraryConstants env
  let mut deps : NameMap (Array Name) := {}
  let mut rows : Array String := #["| Result | Lean | Results from prior work used | Axioms |",
    "| --- | --- | --- | --- |"]
  for (label, n) in paperResults do
    let axs ← liftCoreM <| collectAxioms n
    if axs.any (!standardAxioms.contains ·) then bad := bad.push n
    let (uses, deps') := externalUses env library deps n
    deps := deps'
    let usesStr := if uses.isEmpty then "–" else ", ".intercalate (uses.map fun u => s!"`{u}`")
    let axStr := ", ".intercalate (axs.toList.map toString)
    rows := rows.push s!"| {label} | `{n}` | {usesStr} | {axStr} |"
  for n in solutionResults ++ externalResults.map (·.2) do
    let axs ← liftCoreM <| collectAxioms n
    if axs.any (!standardAxioms.contains ·) then bad := bad.push n
  -- Every declaration of the library, including private and auxiliary ones.
  for c in library do
    let axs ← liftCoreM <| collectAxioms c
    if axs.any (!standardAxioms.contains ·) then bad := bad.push c
  logInfo ("\n".intercalate rows.toList ++
    s!"\n\nChecked {library.size} declarations of the library: " ++
    (if bad.isEmpty then "all use only the standard axioms." else "see the error."))
  unless bad.isEmpty do
    throwError m!"non-standard axioms used by: {bad}"

end Audit

#audit
