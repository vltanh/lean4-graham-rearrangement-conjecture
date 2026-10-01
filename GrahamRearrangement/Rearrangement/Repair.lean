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

theorem repair_collectionPerm_empty {n : ℕ} :
    collectionPerm (∅ : Finset (Fin n × Fin n)) = Equiv.refl _ := by
  unfold collectionPerm
  rw [Finset.toList_empty]
  rfl

/-- The initial state of the repair.  (The hypothesis `hB` is needed: the
`zero_right` field forces every bad right endpoint of `σ` into `B`.) -/
theorem empty_repair_state {n p D : ℕ}
    (σ : Fin n → ZMod p)
    (B : Finset (Fin n))
    (hB : B = badRightEndpoints σ) :
    RepairState D σ B B ∅ := by
  refine ⟨⟨by simp, by simp⟩, subset_refl B, by simp, by simp, ?_⟩
  intro a t ha hat hz
  rw [repair_collectionPerm_empty] at hz
  rw [hB]
  exact (mem_badRightEndpoints_iff σ t).2 ⟨a, ha, hat, hz⟩

theorem collectionPerm_fixes_of_support_above
    {n D : ℕ} {P : Finset (Fin n × Fin n)}
    (hP : IsAdmissibleCollection D P)
    {b : Fin n}
    (habove : ∀ q ∈ P, paperPos b < paperPos q.1) :
    FixedThrough b (collectionPerm P) := by
  intro i hi
  apply collectionPerm_apply_of_forall_ne P i
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
  classical
  let Q := P.filter fun q => q.2 ∈ repairWindow b D
  have hsub : (repairWindow b D) ∩ usedSeconds P ⊆ Q.image Prod.snd := by
    intro y hy
    rcases Finset.mem_inter.1 hy with ⟨hyW, hyU⟩
    rcases Finset.mem_image.1 hyU with ⟨q, hq, rfl⟩
    exact Finset.mem_image.2 ⟨q, Finset.mem_filter.2 ⟨hq, hyW⟩, rfl⟩
  have hinj : Set.InjOn Prod.fst (Q : Set (Fin n × Fin n)) := by
    intro q hq r hr hqr
    have hqP := (Finset.mem_filter.1 hq).1
    have hrP := (Finset.mem_filter.1 hr).1
    by_contra hne
    exact (hstate.admissible.1 hqP hrP hne).1 hqr
  have himg : Q.image Prod.fst ⊆ B ∩ symmetricWindow b (10 * D) := by
    intro z hz
    rcases Finset.mem_image.1 hz with ⟨q, hq, rfl⟩
    have hqP := (Finset.mem_filter.1 hq).1
    have hqW := mem_repairWindow.1 (Finset.mem_filter.1 hq).2
    have hqB := (hstate.pair_data q hqP).1
    have hqb := hstate.processed_above q hqP b hbR
    have hlen := (hstate.admissible.2 q hqP).1
    refine Finset.mem_inter.2 ⟨hqB, ?_⟩
    simp only [symmetricWindow, Finset.mem_filter, Finset.mem_univ, true_and]
    unfold Nat.dist
    simp only [paperPos] at hqW hqb hlen
    omega
  calc
    ((repairWindow b D) ∩ usedSeconds P).card ≤ (Q.image Prod.snd).card :=
      Finset.card_le_card hsub
    _ ≤ Q.card := Finset.card_image_le
    _ = (Q.image Prod.fst).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (B ∩ symmetricWindow b (10 * D)).card := Finset.card_le_card himg
    _ ≤ D := hlocal b

theorem badEndpoints_in_repairWindow_le
    {n D : ℕ}
    (B : Finset (Fin n))
    (hlocal : ∀ z : Fin n,
      (B ∩ symmetricWindow z (10 * D)).card ≤ D)
    (b : Fin n) :
    ((repairWindow b D) ∩ B).card ≤ D := by
  refine le_trans (Finset.card_le_card ?_) (hlocal b)
  intro y hy
  rcases Finset.mem_inter.1 hy with ⟨hyC, hyB⟩
  refine Finset.mem_inter.2 ⟨hyB, ?_⟩
  have hyw := mem_repairWindow.mp hyC
  simp only [symmetricWindow, Finset.mem_filter, Finset.mem_univ, true_and]
  unfold Nat.dist
  simp only [paperPos] at hyw
  omega

theorem blocked_in_repairWindow_le
    {n p D : ℕ}
    (σ : Fin n → ZMod p) (b : Fin n)
    (π : Equiv.Perm (Fin n))
    (hblocked :
      (blockedCandidates D σ b π).card < 2 * D) :
    ((repairWindow b D) ∩
      blockedCandidates D σ b π).card ≤ 2 * D := by
  exact le_trans (Finset.card_le_card Finset.inter_subset_right) hblocked.le

theorem swap_preserves_interval_of_membership_iff
    {n p : ℕ} (τ : Fin n → ZMod p)
    (b y a t : Fin n)
    (hbt :
      (b ∈ indexInterval a t ↔ y ∈ indexInterval a t)) :
    indexedIntervalSum
        (applyPositionPerm τ (Equiv.swap b y)) a t =
      indexedIntervalSum τ a t := by
  rw [← indexSetSum_indexInterval, indexSetSum_applyPositionPerm_image]
  have key : ∀ z, z ∈ (indexInterval a t).image (Equiv.swap b y) ↔
      Equiv.swap b y z ∈ indexInterval a t := by
    intro z
    constructor
    · intro hz
      rcases Finset.mem_image.1 hz with ⟨w, hw, rfl⟩
      rwa [Equiv.swap_apply_self]
    · intro hz
      exact Finset.mem_image.2 ⟨_, hz, Equiv.swap_apply_self _ _ _⟩
  have himage : (indexInterval a t).image (Equiv.swap b y) = indexInterval a t := by
    ext z
    rw [key]
    rcases eq_or_ne z b with rfl | hzb
    · rw [Equiv.swap_apply_left]
      exact hbt.symm
    · rcases eq_or_ne z y with rfl | hzy
      · rw [Equiv.swap_apply_right]
        exact hbt
      · rw [Equiv.swap_apply_of_ne_of_ne hzb hzy]
  rw [himage, indexSetSum_indexInterval]

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
  have hyw := mem_repairWindow.mp hy
  have hnot' :
      ¬ ((paperPos b < paperPos a ∧ paperPos a ≤ paperPos y) ∨
        (paperPos b ≤ paperPos t ∧ paperPos t < paperPos y)) := by
    intro hcross
    exact hnot ⟨hyw.1, hyw.2, a, t, ha2, hat, hz, hcross⟩
  have hsame : (b ∈ indexInterval a t ↔ y ∈ indexInterval a t) := by
    simp only [indexInterval, Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [paperPos] at hnot' hyw
    omega
  refine ⟨?_, ?_⟩
  · rw [← swap_preserves_interval_of_membership_iff
      (applyPositionPerm σ π) b y a t hsame]
    exact hz
  · intro htb
    subst htb
    exact hnot' (Or.inr ⟨le_rfl, hyw.1⟩)

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
  constructor
  · rw [Finset.coe_insert, Set.pairwise_insert]
    refine ⟨hP.1, ?_⟩
    intro q hq _
    have hq' : q ∈ P := hq
    exact ⟨⟨(hbfirst q hq').symm, (hbsecond q hq').symm,
        (hyfirst q hq').symm, (hysecond q hq').symm⟩,
      ⟨hbfirst q hq', hyfirst q hq', hbsecond q hq', hysecond q hq'⟩⟩
  · intro q hq
    rcases Finset.mem_insert.1 hq with rfl | hq
    · exact ⟨hby, hlen⟩
    · exact hP.2 q hq

theorem collectionPerm_insert
    {n D : ℕ}
    {P : Finset (Fin n × Fin n)}
    {b y : Fin n}
    (hnew : IsAdmissibleCollection D (insert (b,y) P))
    (hnotmem : (b,y) ∉ P) :
    collectionPerm (insert (b,y) P) =
      (Equiv.swap b y).trans (collectionPerm P) := by
  have hl : ((b,y) :: P.toList).toFinset = insert (b,y) P := by
    rw [List.toFinset_cons, Finset.toList_toFinset]
  have hln : ((b,y) :: P.toList).Nodup :=
    List.nodup_cons.2 ⟨fun h => hnotmem (Finset.mem_toList.1 h),
      Finset.nodup_toList P⟩
  rw [← collectionPerm_order_independent hnew _ hl hln]
  rfl

theorem repair_state_step
    {n p D : ℕ}
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
  classical
  -- Process the largest unprocessed bad endpoint.
  obtain ⟨b, hbR, hbmax⟩ : ∃ b ∈ R, ∀ r ∈ R, r ≤ b :=
    ⟨R.max' hR, R.max'_mem hR, fun r hr => R.le_max' r hr⟩
  have hbB : b ∈ B := hstate.remaining_subset hbR
  have hbfar := hfar b hbB
  have hfixThrough : FixedThrough b (collectionPerm P) :=
    collectionPerm_fixes_of_support_above hstate.admissible
      (fun q hq => hstate.processed_above q hq b hbR)
  have hfix : FixedBelow b (collectionPerm P) :=
    fun i hi => hfixThrough i hi.le
  have hπadm : IsAdmissiblePermutation D (collectionPerm P) :=
    ⟨P, hstate.admissible, rfl⟩
  have hblockedCard := hblocked b hbB (collectionPerm P) hπadm hfix
  have hCcard : (repairWindow b D).card = 5 * D := card_repairWindow b hbfar
  have h₁ := blocked_in_repairWindow_le σ b (collectionPerm P) hblockedCard
  have h₂ := badEndpoints_in_repairWindow_le B hlocal b
  have h₃ := usedSeconds_near_card_le hstate hlocal hbR
  -- At most 2D + D + D < 5D choices are forbidden.
  obtain ⟨y, hyC, hyBl, hyB, hyU⟩ :
      ∃ y ∈ repairWindow b D,
        y ∉ blockedCandidates D σ b (collectionPerm P) ∧
        y ∉ B ∧ y ∉ usedSeconds P := by
    by_contra hcon
    push Not at hcon
    have hsub :
        repairWindow b D ⊆
          ((repairWindow b D ∩ blockedCandidates D σ b (collectionPerm P)) ∪
            (repairWindow b D ∩ B)) ∪
            (repairWindow b D ∩ usedSeconds P) := by
      intro z hz
      by_cases h1 : z ∈ blockedCandidates D σ b (collectionPerm P)
      · exact Finset.mem_union_left _
          (Finset.mem_union_left _ (Finset.mem_inter.2 ⟨hz, h1⟩))
      · by_cases h2 : z ∈ B
        · exact Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_inter.2 ⟨hz, h2⟩))
        · exact Finset.mem_union_right _
            (Finset.mem_inter.2 ⟨hz, hcon z hz h1 h2⟩)
    have h4 := Finset.card_le_card hsub
    have h5 := Finset.card_union_le
      ((repairWindow b D ∩ blockedCandidates D σ b (collectionPerm P)) ∪
        (repairWindow b D ∩ B))
      (repairWindow b D ∩ usedSeconds P)
    have h6 := Finset.card_union_le
      (repairWindow b D ∩ blockedCandidates D σ b (collectionPerm P))
      (repairWindow b D ∩ B)
    omega
  have hyw := mem_repairWindow.mp hyC
  have hyNotBad : y ∉ badRightEndpoints σ := by
    rw [← hB]
    exact hyB
  have hnotBlocked : ¬ IsBlockedAt D σ b (collectionPerm P) y := by
    intro h
    exact hyBl (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
  have hbfirst : ∀ q ∈ P, q.1 ≠ b := by
    intro q hq h
    have := hstate.processed_above q hq b hbR
    rw [h] at this
    exact lt_irrefl _ this
  have hbsecond : ∀ q ∈ P, q.2 ≠ b := by
    intro q hq h
    exact (hstate.pair_data q hq).2.2 (h ▸ hbB)
  have hyfirst : ∀ q ∈ P, q.1 ≠ y := by
    intro q hq h
    exact hyB (h ▸ (hstate.pair_data q hq).1)
  have hysecond : ∀ q ∈ P, q.2 ≠ y := by
    intro q hq h
    exact hyU (Finset.mem_image.2 ⟨q, hq, h⟩)
  have hnewAdm : IsAdmissibleCollection D (insert (b,y) P) :=
    extend_admissible_collection hstate.admissible hyw.1 (by omega)
      hbfirst hbsecond hyfirst hysecond
  have hnotmem : (b,y) ∉ P := fun h => hbfirst (b,y) h rfl
  have hperm := collectionPerm_insert hnewAdm hnotmem
  refine ⟨b, hbR, y, hyC, hyNotBad, hyU, hnotBlocked, ?_⟩
  refine ⟨hnewAdm, ?_, ?_, ?_, ?_⟩
  · exact fun r hr => hstate.remaining_subset (Finset.mem_of_mem_erase hr)
  · intro q hq
    rcases Finset.mem_insert.1 hq with rfl | hq
    · exact ⟨hbB, Finset.notMem_erase b R, hyB⟩
    · obtain ⟨hqB, hqR, hq2⟩ := hstate.pair_data q hq
      exact ⟨hqB, fun h => hqR (Finset.mem_of_mem_erase h), hq2⟩
  · intro q hq r hr
    rcases Finset.mem_insert.1 hq with rfl | hq
    · have hrR := Finset.mem_of_mem_erase hr
      have hrne := Finset.ne_of_mem_erase hr
      have hlt : r < b := lt_of_le_of_ne (hbmax r hrR) hrne
      have hlt' := Fin.lt_def.1 hlt
      simp only [paperPos]
      omega
    · exact hstate.processed_above q hq r (Finset.mem_of_mem_erase hr)
  · intro a t ha hat hz
    rw [hperm] at hz
    have hz' :
        indexedIntervalSum
          (applyPositionPerm
            (applyPositionPerm σ (collectionPerm P)) (Equiv.swap b y))
          a t = 0 := hz
    obtain ⟨hbefore, htne⟩ :=
      not_blocked_zero_preserves σ (collectionPerm P) b y a t hyC ha hat
        hnotBlocked hz'
    exact Finset.mem_erase.2 ⟨htne, hstate.zero_right a t ha hat hbefore⟩

/-- The complete induction on the number of unprocessed bad endpoints. -/
theorem repair_all_bad_endpoints
    {n p D : ℕ}
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
  suffices h : ∀ k (R : Finset (Fin n)) (P : Finset (Fin n × Fin n)),
      R.card = k → RepairState D σ B R P →
        ∃ P' : Finset (Fin n × Fin n),
          IsAdmissibleCollection D P' ∧ ZeroRightInvariant σ P' ∅ from
    h _ R P rfl hstate
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro R P hcard hstate
    by_cases hR : R.Nonempty
    · obtain ⟨b, hbR, y, _, _, _, _, hstep⟩ :=
        repair_state_step σ B R P hB hstate hfar hlocal hblocked hR
      have hlt : (R.erase b).card < k := by
        rw [Finset.card_erase_of_mem hbR, ← hcard]
        have := Finset.card_pos.2 hR
        omega
      exact ih _ hlt (R.erase b) (insert (b,y) P) rfl hstep
    · have hRempty : R = ∅ := Finset.not_nonempty_iff_eq_empty.mp hR
      subst hRempty
      exact ⟨P, hstate.admissible, hstate.zero_right⟩

/-- The deterministic local-repair step from the proof of Theorem 1.2. -/
theorem section5_local_repair
    {n p D : ℕ}
    (σ : Fin n → ZMod p)
    (hgood : Section5Good D σ) :
    ∃ π : Equiv.Perm (Fin n),
      IsAdmissiblePermutation D π ∧
      HasNoZeroPaperSegments
        (applyPositionPerm σ π) := by
  obtain ⟨h1, h2, h3⟩ := hgood
  have hinit : RepairState D σ (badRightEndpoints σ) (badRightEndpoints σ) ∅ :=
    empty_repair_state σ _ rfl
  obtain ⟨P, hPadm, hzero⟩ :=
    repair_all_bad_endpoints σ (badRightEndpoints σ) (badRightEndpoints σ)
      ∅ rfl hinit (not_badEvent1_far h1) (not_badEvent2_local h2)
      (not_badEvent3_blocked h3)
  refine ⟨collectionPerm P, ⟨P, hPadm, rfl⟩, ?_⟩
  intro a t ha hat hz
  exact Finset.notMem_empty t (hzero a t ha hat hz)

end

end GrahamRearrangement
