module

public import Certificates.Kernel.RouteP.Text.PlanesX
public import Certificates.Kernel.RouteP.Text.Layout
public import Mathlib.Tactic.ReduceModChar

public section

namespace CertificateChecks.KernelRouteP

open CFSG.KC.RouteP CFSG.KD.RouteP CFSG.KS.RouteP
  CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native CFSG.Sporadic.Th.Native

theorem planeGen_lt {s : Nat} (hs : s < 16) : ∀ i < 891, ((planeGenData ())[s]!)[i]! = PGE s i ∧
    ((planeGenData ())[s]!).size = 891 := by
  obtain ⟨-, h⟩ := planeGenData_get
  obtain ⟨h1, h2⟩ := h s (by omega)
  rw [pgLens_eq, if_pos hs] at h1 h2
  exact fun i hi => ⟨h2 i hi, h1⟩

theorem planeTabs_get : (planeTabs ()).size = 14 ∧ ∀ s < 14, ((planeTabs ())[s]!).size = 891 ∧
    ∀ i < 891, ((planeTabs ())[s]!)[i]! = PGE s i := by
  obtain ⟨h0, -⟩ := planeGenData_get
  unfold planeTabs
  refine ⟨by simp [h0], fun s hs => ?_⟩
  have e : ((planeGenData ()).extract 0 14)[s]! = (planeGenData ())[s]! := by
    rw [getElem!_pos _ _ (by simp [h0]; omega), getElem!_pos _ _ (by omega), Array.getElem_extract]
    simp
  rw [e]
  exact ⟨(planeGen_lt (by omega) 0 (by decide)).2, fun i hi => (planeGen_lt (by omega) i hi).1⟩

theorem planePar_get : (planePar ()).size = 891 ∧ ∀ k < 891, (planePar ())[k]! = PGE 14 k :=
  ⟨(planeGen_lt (by decide) 0 (by decide)).2, fun k hk => (planeGen_lt (by decide) k hk).1⟩

theorem planeLab_get : (planeLab ()).size = 891 ∧ ∀ k < 891, (planeLab ())[k]! = PGE 15 k :=
  ⟨(planeGen_lt (by decide) 0 (by decide)).2, fun k hk => (planeGen_lt (by decide) k hk).1⟩

theorem planeSep_get : (planeSep ()).size = 21 ∧ ∀ t < 21, (planeSep ())[t]! = PGE 16 t := by
  obtain ⟨-, h⟩ := planeGenData_get
  obtain ⟨h1, h2⟩ := h 16 (by decide)
  rw [pgLens_eq, if_neg (by decide)] at h1 h2
  exact ⟨h1, h2⟩

theorem allIn_iff' {lo hi : Nat} {p : Nat → Bool} :
    allIn lo hi p = true ↔ ∀ i, lo ≤ i → i < hi → p i = true :=
  CFSG.Sporadic.Th.allIn_eq_true

theorem anyIn_iff {lo hi : Nat} {p : Nat → Bool} :
    anyIn lo hi p = true ↔ ∃ i, lo ≤ i ∧ i < hi ∧ p i = true := by
  unfold anyIn
  rw [Bool.not_eq_true', Bool.eq_false_iff, Ne, allIn_iff']
  constructor
  · intro h
    by_contra hc
    exact h fun i h1 h2 => by simpa using fun hp => hc ⟨i, h1, h2, hp⟩
  · rintro ⟨i, h1, h2, hp⟩ h
    have := h i h1 h2
    simp [hp] at this

theorem ball_range {n : Nat} {p : Nat → Bool} (h : (List.range n).all p = true) :
    ∀ i < n, p i = true := fun i hi => List.all_eq_true.1 h i (List.mem_range.2 hi)

theorem memRow_iff {r : Array Nat} {p : Nat} : memRow r p = true ↔ ∃ b < 24, r[b]! = p := by
  unfold memRow
  rw [anyIn_iff]
  constructor
  · rintro ⟨b, -, hb, h⟩
    exact ⟨b, hb, by simpa using h⟩
  · rintro ⟨b, hb, h⟩
    exact ⟨b, Nat.zero_le _, hb, by simp [h]⟩

@[expose] noncomputable def pxRowsK : Bool :=
  (List.range 891).all fun i => (List.range 24).all (fun j => decide (PXE i j < 920808)) &&
    (List.range 23).all fun j => decide (PXE i j < PXE i (j + 1))

@[expose] noncomputable def pxBaseK : Bool :=
  (List.range 24).all fun j => (List.range 24).any fun i => planeArr[i]! == PXE 0 j

@[expose] noncomputable def pxRow (i : Nat) : List Nat := (List.range 24).map (PXE i)

@[expose] noncomputable def pxDistinctK : Bool :=
  (List.range 891).all fun i => (List.range i).all fun j => pxRow i != pxRow j

@[expose] noncomputable def pxSepK : Bool :=
  (List.range 21).all fun t => decide (PGE 16 t < 891) && (List.range 24).all fun i =>
    ((List.range 24).any fun b => PXE (PGE 16 t) b == planeArr[i]!) ==
      (decide (i < 3) || i == t + 3)

@[expose] noncomputable def pgTreeK : Bool :=
  ((List.range 891).all fun k => k == 0 ||
    (decide (PGE 14 k < k) && decide (PGE 15 k < 14) && PGE (PGE 15 k) (PGE 14 k) == k)) &&
  (List.range 14).all fun s => (List.range 891).all fun i => decide (PGE s i < 891)

set_option maxHeartbeats 0 in
theorem pxRowsK_true : pxRowsK = true := by decide +kernel

theorem pxBaseK_true : pxBaseK = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem pxDistinctK_true : pxDistinctK = true := by decide +kernel

theorem pxSepK_true : pxSepK = true := by decide +kernel

theorem pgTreeK_true : pgTreeK = true := by decide +kernel

theorem px_rows (i : Nat) (hi : i < 891) :
    (∀ j < 24, PXE i j < 920808) ∧ ∀ j < 23, PXE i j < PXE i (j + 1) := by
  have h := ball_range pxRowsK_true i hi
  rw [Bool.and_eq_true] at h
  exact ⟨fun j hj => by simpa using ball_range h.1 j hj, fun j hj => by simpa using ball_range h.2 j hj⟩

theorem px_get {i j : Nat} (hi : i < 891) (hj : j < 24) : ((planeXData ())[i]!)[j]! = PXE i j :=
  (planeXData_get.2 i hi).2 j hj

theorem rowsOK_true : rowsOK (planeXData ()) = true := by
  unfold rowsOK
  rw [Bool.and_eq_true, beq_iff_eq, allIn_iff']
  refine ⟨planeXData_get.1, fun i _ hi => ?_⟩
  obtain ⟨hlt, hmono⟩ := px_rows i hi
  unfold rowOK
  simp only [Bool.and_eq_true, beq_iff_eq, allIn_iff', decide_eq_true_eq]
  refine ⟨⟨(planeXData_get.2 i hi).1, fun j _ hj => ?_⟩, fun j _ hj => ?_⟩
  · rw [px_get hi hj]
    exact hlt j hj
  · rw [px_get hi (by omega), px_get hi (by omega)]
    exact hmono j hj

theorem baseOK_true : baseOK (planeXData ()) = true := by
  unfold baseOK
  rw [allIn_iff']
  intro j _ hj
  rw [anyIn_iff]
  obtain ⟨i, hi, h⟩ := List.any_eq_true.1 (ball_range pxBaseK_true j hj)
  refine ⟨i, Nat.zero_le _, List.mem_range.1 hi, ?_⟩
  rw [px_get (by decide) hj]
  exact h

theorem pxRow_pairwise (i : Nat) (hi : i < 891) : (pxRow i).Pairwise (· < ·) := by
  obtain ⟨-, hmono⟩ := px_rows i hi
  have key : ∀ a b, a < b → b < 24 → PXE i a < PXE i b := by
    intro a b hab hb
    induction b with
    | zero => omega
    | succ b ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h | h
      · exact lt_trans (ih h (by omega)) (hmono b (by omega))
      · subst h
        exact hmono a (by omega)
  unfold pxRow
  rw [List.pairwise_map]
  rw [List.pairwise_iff_getElem]
  intro a b ha hb hab
  simp only [List.getElem_range]
  exact key a b hab (by simpa using hb)

theorem row_eq_of_mem {L M : List Nat} (hL : L.Pairwise (· < ·)) (hM : M.Pairwise (· < ·))
    (hlen : L.length = M.length) (hsub : ∀ a ∈ L, a ∈ M) : L = M := by
  have hnd : L.Nodup := hL.imp (fun h => Nat.ne_of_lt h)
  have hsp : L.Subperm M := hnd.subperm hsub
  have hp : L.Perm M := hsp.perm_of_length_le (by omega)
  exact hp.eq_of_pairwise (fun a b _ _ h1 h2 => absurd (Nat.lt_trans h1 h2) (Nat.lt_irrefl a)) hL hM

theorem distinctOK_true : distinctOK (planeXData ()) = true := by
  unfold distinctOK
  simp only [planeCount]
  rw [allIn_iff']
  intro i _ hi
  rw [allIn_iff']
  intro j _ hj
  rw [anyIn_iff]
  by_contra hc
  have hne := ball_range (ball_range pxDistinctK_true i hi) j hj
  simp only [bne_iff_ne, ne_eq, decide_eq_true_eq] at hne
  apply hne
  apply row_eq_of_mem (pxRow_pairwise i hi) (pxRow_pairwise j (by omega)) (by simp [pxRow])
  intro a ha
  obtain ⟨a', ha', rfl⟩ := List.mem_map.1 ha
  have ha'' := List.mem_range.1 ha'
  have hm : memRow (planeXData ())[j]! ((planeXData ())[i]!)[a']! = true := by
    by_contra hm
    exact hc ⟨a', Nat.zero_le _, ha'', by simpa using hm⟩
  obtain ⟨b, hb, he⟩ := memRow_iff.1 hm
  rw [px_get (by omega) hb, px_get hi ha''] at he
  exact List.mem_map.2 ⟨b, List.mem_range.2 hb, he⟩

theorem sepOK_true : sepOK (planeXData ()) (planeSep ()) = true := by
  obtain ⟨hs, hg⟩ := planeSep_get
  unfold sepOK
  rw [Bool.and_eq_true, beq_iff_eq, allIn_iff']
  refine ⟨hs, fun t _ ht => ?_⟩
  have h := ball_range pxSepK_true t ht
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  rw [hg t ht, Bool.and_eq_true, allIn_iff']
  refine ⟨h1, fun i _ hi => ?_⟩
  have h3 := ball_range h2 i hi
  have hlt : PGE 16 t < 891 := by simpa using h1
  have e : memRow (planeXData ())[PGE 16 t]! planeArr[i]! =
      (List.range 24).any fun b => PXE (PGE 16 t) b == planeArr[i]! := by
    apply Bool.eq_iff_iff.mpr
    rw [memRow_iff, List.any_eq_true]
    constructor
    · rintro ⟨b, hb, he⟩
      exact ⟨b, List.mem_range.2 hb, by rw [← px_get hlt hb, he]; simp⟩
    · rintro ⟨b, hb, he⟩
      exact ⟨b, List.mem_range.1 hb, by rw [px_get hlt (List.mem_range.1 hb)]; simpa using he⟩
  rw [e]
  exact h3

theorem planeTreeOK_true : planeTreeOK (planeTabs ()) (planePar ()) (planeLab ()) = true := by
  obtain ⟨hps, hpg⟩ := planePar_get
  obtain ⟨hls, hlg⟩ := planeLab_get
  obtain ⟨-, htg⟩ := planeTabs_get
  have ht := pgTreeK_true
  unfold pgTreeK at ht
  rw [Bool.and_eq_true] at ht
  unfold planeTreeOK
  simp only [planeCount, planeGenCount, Bool.and_eq_true, beq_iff_eq, allIn_iff', decide_eq_true_eq]
  refine ⟨⟨hps, hls⟩, fun k hk1 hk => ?_⟩
  have h := ball_range ht.1 k hk
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with h | ⟨⟨h1, h2⟩, h3⟩
  · omega
  · rw [hpg k hk, hlg k hk]
    refine ⟨⟨h1, h2⟩, ?_⟩
    rw [(htg _ h2).2 _ (by omega)]
    exact h3

@[expose] noncomputable def maskActK : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, i => i
  | k + 1, s, m, i =>
    if m % 2 = 1 then PGE (2 + s) (maskActK k (s + 1) (m / 2) i) else maskActK k (s + 1) (m / 2) i

theorem pg_lt {s i : Nat} (hs : s < 14) (hi : i < 891) : PGE s i < 891 := by
  have ht := pgTreeK_true
  unfold pgTreeK at ht
  rw [Bool.and_eq_true] at ht
  simpa using ball_range (ball_range ht.2 s hs) i hi

theorem maskActK_lt : ∀ (k s m i : Nat), s + k ≤ 11 → i < 891 → maskActK k s m i < 891
  | 0, _, _, _, _, hi => hi
  | k + 1, s, m, i, hk, hi => by
    unfold maskActK
    split
    · exact pg_lt (by omega) (maskActK_lt k (s + 1) (m / 2) i (by omega) hi)
    · exact maskActK_lt k (s + 1) (m / 2) i (by omega) hi

theorem maskAct_eq : ∀ (k s m i : Nat), s + k ≤ 11 → i < 891 →
    maskAct (epsTabsFrom (planeTabs ()) k s) m i = maskActK k s m i
  | 0, _, _, _, _, _ => rfl
  | k + 1, s, m, i, hk, hi => by
    unfold epsTabsFrom maskAct maskActK
    rw [maskAct_eq k (s + 1) (m / 2) i (by omega) hi]
    split
    · rw [(planeTabs_get.2 (2 + s) (by omega)).2 _ (maskActK_lt k (s + 1) (m / 2) i (by omega) hi)]
    · rfl

@[expose] noncomputable def fixMasksK : List Nat :=
  (List.range 2048).filter fun m => (List.range 891).all fun i => maskActK 11 0 m i == i

set_option maxHeartbeats 0 in
theorem fixMasksK_eq : fixMasksK = fixMasksExpected := by decide +kernel

theorem fixMasks_eq : fixMasks (planeTabs ()) = fixMasksExpected := by
  rw [← fixMasksK_eq]
  unfold fixMasks fixMasksK
  apply List.filter_congr
  intro m _
  apply Bool.eq_iff_iff.mpr
  rw [allIn_iff', List.all_eq_true]
  constructor
  · intro h i hi
    have hi' := List.mem_range.1 hi
    rw [← maskAct_eq 11 0 m i (by decide) hi']
    exact h i (Nat.zero_le _) hi'
  · intro h i _ hi
    rw [maskAct_eq 11 0 m i (by decide) hi]
    exact h i (List.mem_range.2 hi)

theorem dwordsOK_true : dwordsOK (planeDWords ()) = true := by
  rw [planeDWords_eq]
  unfold dwordsOK
  simp only [allIn_zero_eq]
  decide +kernel

end CertificateChecks.KernelRouteP
