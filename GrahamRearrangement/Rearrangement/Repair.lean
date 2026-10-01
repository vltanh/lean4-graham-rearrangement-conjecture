module

public import GrahamRearrangement.Rearrangement.Lemma53

@[expose] public section

open scoped BigOperators Pointwise

namespace GrahamRearrangement

/-!
# Deterministic Section 5 repair

The descending greedy construction from the proof of Theorem 1.2.
-/

noncomputable section

theorem applyPositionPerm_isIndexedOrdering
    {p : ℕ} {S : Finset (ZMod p)}
    {σ : Fin S.card → ZMod p}
    (hσ : IsIndexedOrdering S σ)
    (π : Equiv.Perm (Fin S.card)) :
    IsIndexedOrdering S (applyPositionPerm σ π) := by
  constructor
  · intro i j hij
    apply π.injective
    apply hσ.1
    exact hij
  · intro x
    rw [hσ.2]
    constructor
    · rintro ⟨j, hj⟩
      refine ⟨π.symm j, ?_⟩
      simpa [applyPositionPerm] using hj
    · rintro ⟨i, hi⟩
      refine ⟨π i, ?_⟩
      simpa [applyPositionPerm] using hi

theorem not_badEvent1_far
    {n p D : ℕ} {σ : Fin n → ZMod p}
    (h1 : ¬ BadEvent1 D σ) :
    ∀ b ∈ badRightEndpoints σ,
      paperPos b + 5 * D ≤ n := by
  intro b hb
  by_contra h
  have hlate : n ≤ paperPos b + 30 * D := by omega
  exact h1 ⟨b, hb, hlate⟩

theorem not_badEvent2_local
    {n p D : ℕ} {σ : Fin n → ZMod p}
    (h2 : ¬ BadEvent2 D σ) :
    ∀ z : Fin n,
      ((badRightEndpoints σ) ∩
        symmetricWindow z (10 * D)).card ≤ D := by
  intro z
  by_contra h
  have hgt :
      D < ((badRightEndpoints σ) ∩
        symmetricWindow z (10 * D)).card := by omega
  exact h2 ⟨z, hgt⟩

theorem not_badEvent3_blocked
    {n p D : ℕ} {σ : Fin n → ZMod p}
    (h3 : ¬ BadEvent3 D σ) :
    ∀ b ∈ badRightEndpoints σ,
      ∀ π : Equiv.Perm (Fin n),
        IsAdmissiblePermutation D π →
        FixedBelow b π →
        (blockedCandidates D σ b π).card < 2 * D := by
  intro b hb π hπ hfix
  by_contra h
  have hge :
      2 * D ≤ (blockedCandidates D σ b π).card := by omega
  exact h3 ⟨b, hb, π, hπ, hfix, hge⟩

/-- The 5D possible choices {b+1,...,b+5D}. -/
def repairWindow {n : ℕ} (b : Fin n) (D : ℕ) :
    Finset (Fin n) :=
  (forwardWindow b (5 * D)).erase b

theorem mem_repairWindow {n D : ℕ} {b y : Fin n} :
    y ∈ repairWindow b D ↔
      paperPos b < paperPos y ∧
        paperPos y ≤ paperPos b + 5 * D := by
  simp [repairWindow, forwardWindow, paperPos]
  omega

theorem card_repairWindow {n D : ℕ} (b : Fin n)
    (hfit : paperPos b + 5 * D ≤ n) :
    (repairWindow b D).card = 5 * D := by
  have hfit' : b.val + 5 * D < n := by
    simp [paperPos] at hfit
    omega
  have hcard :=
    card_forwardWindow_eq b (5 * D) hfit'
  have hb : b ∈ forwardWindow b (5 * D) := by
    simp [forwardWindow]
  unfold repairWindow
  rw [Finset.card_erase_of_mem hb, hcard]
  omega

def usedSeconds {n : ℕ}
    (P : Finset (Fin n × Fin n)) : Finset (Fin n) :=
  P.image Prod.snd

def ZeroRightInvariant {n p : ℕ}
    (σ : Fin n → ZMod p)
    (P : Finset (Fin n × Fin n))
    (R : Finset (Fin n)) : Prop :=
  ∀ a t : Fin n,
    2 ≤ paperPos a → paperPos a < paperPos t →
    indexedIntervalSum
        (applyPositionPerm σ (collectionPerm P)) a t = 0 →
      t ∈ R

/-- State invariant for the descending repair. -/
structure RepairState {n p : ℕ} (D : ℕ)
    (σ : Fin n → ZMod p)
    (B R : Finset (Fin n))
    (P : Finset (Fin n × Fin n)) : Prop where
  admissible : IsAdmissibleCollection D P
  remaining_subset : R ⊆ B
  pair_data :
    ∀ q ∈ P,
      q.1 ∈ B ∧ q.1 ∉ R ∧ q.2 ∉ B
  processed_above :
    ∀ q ∈ P, ∀ r ∈ R,
      paperPos r < paperPos q.1
  zero_right : ZeroRightInvariant σ P R

theorem empty_repair_state {n p D : ℕ}
    (σ : Fin n → ZMod p)
    (B : Finset (Fin n)) :
    RepairState D σ B B ∅ := by
  sorry

theorem collectionPerm_fixes_of_support_above
    {n D : ℕ} {P : Finset (Fin n × Fin n)}
    (hP : IsAdmissibleCollection D P)
    {b : Fin n}
    (habove : ∀ q ∈ P, paperPos b < paperPos q.1) :
    FixedThrough b (collectionPerm P) := by
  intro i hi
  unfold collectionPerm
  apply Section5External.disjoint_swaps_fix_outside_support
    P hP.1 i
  intro q hq
  have hqb := habove q hq
  have hq12 := (hP.2 q hq).1
  constructor
  · intro h
    subst i
    omega
  · intro h
    subst i
    omega

theorem usedSeconds_near_card_le
    {n p D : ℕ}
    {σ : Fin n → ZMod p}
    {B R : Finset (Fin n)}
    {P : Finset (Fin n × Fin n)}
    (hstate : RepairState D σ B R P)
    (hlocal : ∀ z : Fin n,
      (B ∩ symmetricWindow z (10 * D)).card ≤ D)
    {b : Fin n} (hbR : b ∈ R) :
    ((repairWindow b D) ∩ usedSeconds P).card ≤ D := by
  sorry

theorem badEndpoints_in_repairWindow_le
    {n p D : ℕ} {σ : Fin n → ZMod p}
    (B : Finset (Fin n))
    (hB : B = badRightEndpoints σ)
    (hlocal : ∀ z : Fin n,
      (B ∩ symmetricWindow z (10 * D)).card ≤ D)
    (b : Fin n) :
    ((repairWindow b D) ∩ B).card ≤ D := by
  sorry

theorem blocked_in_repairWindow_le
    {n p D : ℕ}
    (σ : Fin n → ZMod p) (b : Fin n)
    (π : Equiv.Perm (Fin n))
    (hblocked :
      (blockedCandidates D σ b π).card < 2 * D) :
    ((repairWindow b D) ∩
      blockedCandidates D σ b π).card ≤ 2 * D := by
  sorry

theorem swap_preserves_interval_of_membership_iff
    {n p : ℕ} (τ : Fin n → ZMod p)
    (b y a t : Fin n)
    (hbt :
      (b ∈ indexInterval a t ↔ y ∈ indexInterval a t)) :
    indexedIntervalSum
        (applyPositionPerm τ (Equiv.swap b y)) a t =
      indexedIntervalSum τ a t := by
  sorry

theorem not_blocked_zero_preserves
    {n p D : ℕ}
    (σ : Fin n → ZMod p)
    (π : Equiv.Perm (Fin n))
    (b y a t : Fin n)
    (hy : y ∈ repairWindow b D)
    (ha2 : 2 ≤ paperPos a)
    (hat : paperPos a < paperPos t)
    (hnot : ¬ IsBlockedAt D σ b π y)
    (hz :
      indexedIntervalSum
        (applyPositionPerm
          (applyPositionPerm σ π) (Equiv.swap b y))
        a t = 0) :
    indexedIntervalSum (applyPositionPerm σ π) a t = 0 ∧ t ≠ b := by
  sorry

theorem extend_admissible_collection
    {n D : ℕ}
    {P : Finset (Fin n × Fin n)}
    (hP : IsAdmissibleCollection D P)
    {b y : Fin n}
    (hby : paperPos b < paperPos y)
    (hlen : paperPos y - paperPos b ≤ 5 * D)
    (hbfirst : ∀ q ∈ P, q.1 ≠ b)
    (hbsecond : ∀ q ∈ P, q.2 ≠ b)
    (hyfirst : ∀ q ∈ P, q.1 ≠ y)
    (hysecond : ∀ q ∈ P, q.2 ≠ y) :
    IsAdmissibleCollection D (insert (b, y) P) := by
  sorry

theorem collectionPerm_insert
    {n D : ℕ}
    {P : Finset (Fin n × Fin n)}
    (hP : IsAdmissibleCollection D P)
    {b y : Fin n}
    (hnew : IsAdmissibleCollection D (insert (b,y) P))
    (hnotmem : (b,y) ∉ P) :
    collectionPerm (insert (b,y) P) =
      (Equiv.swap b y).trans (collectionPerm P) := by
  sorry

theorem repair_state_step
    {n p D : ℕ} (hD : 0 < D)
    (σ : Fin n → ZMod p)
    (B R : Finset (Fin n))
    (P : Finset (Fin n × Fin n))
    (hB : B = badRightEndpoints σ)
    (hstate : RepairState D σ B R P)
    (hfar : ∀ b ∈ B, paperPos b + 5 * D ≤ n)
    (hlocal : ∀ z : Fin n,
      (B ∩ symmetricWindow z (10 * D)).card ≤ D)
    (hblocked :
      ∀ b ∈ B, ∀ π : Equiv.Perm (Fin n),
        IsAdmissiblePermutation D π →
        FixedBelow b π →
        (blockedCandidates D σ b π).card < 2 * D)
    (hR : R.Nonempty) :
    ∃ b ∈ R, ∃ y ∈ repairWindow b D,
      y ∉ badRightEndpoints σ ∧
      y ∉ usedSeconds P ∧
      ¬ IsBlockedAt D σ b (collectionPerm P) y ∧
      RepairState D σ B (R.erase b) (insert (b,y) P) := by
  sorry

/-- The complete induction on the number of unprocessed bad endpoints. -/
theorem repair_all_bad_endpoints
    {n p D : ℕ} (hD : 0 < D)
    (σ : Fin n → ZMod p)
    (B R : Finset (Fin n))
    (P : Finset (Fin n × Fin n))
    (hB : B = badRightEndpoints σ)
    (hstate : RepairState D σ B R P)
    (hfar : ∀ b ∈ B, paperPos b + 5 * D ≤ n)
    (hlocal : ∀ z : Fin n,
      (B ∩ symmetricWindow z (10 * D)).card ≤ D)
    (hblocked :
      ∀ b ∈ B, ∀ π : Equiv.Perm (Fin n),
        IsAdmissiblePermutation D π →
        FixedBelow b π →
        (blockedCandidates D σ b π).card < 2 * D) :
    ∃ P' : Finset (Fin n × Fin n),
      IsAdmissibleCollection D P' ∧
      ZeroRightInvariant σ P' ∅ := by
  sorry

/-- The deterministic local-repair step from the proof of Theorem 1.2. -/
theorem section5_local_repair
    {n p D : ℕ} (hD : 0 < D)
    (σ : Fin n → ZMod p)
    (hgood : Section5Good D σ) :
    ∃ π : Equiv.Perm (Fin n),
      IsAdmissiblePermutation D π ∧
      HasNoZeroPaperSegments
        (applyPositionPerm σ π) := by
  sorry

end

end GrahamRearrangement
