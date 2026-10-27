
module

public import Certificates.Kernel.SporSch.Co2M.ThirdBoundBase

public import Certificates.Kernel.SporSch.Co2M.ThirdGlue
public import CFSG.Certificates.Kernel.SporSch.ThirdChainH
public import CFSG.Certificates.Kernel.SporSch.OrbitBound
public import Certificates.Kernel.SporSch.Ru.SmallFacts
public import CFSG.Certificates.Kernel.SporSch.ThirdChainHPrelude
public import CFSG.Certificates.Kernel.SporSch.ThirdDfsPrelude
public import CFSG.Sporadic.Co2Schreier.Centralizers

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.Co2M CFSG.KS.Co2Third
  CFSG.KS.OrbitBound
open CFSG.Sporadic.Co2Schreier CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.Certificates CFSG.Sporadic.Co2Cert CFSG.Monster.B.Mathieu

local notation "cJ " j:max => rcnt (Co2T3.LR j)
local notation "rptJ " j:max k:max => rpt 12 (mask 12) (Co2T3.LR j) k
local notation "rposJ " j:max z:max => rpos 12 (mask 12) (2300 * 12) (Co2T3.LR j) z
local notation "tau " j:max k:max => treeF (stp 2300 S3 thB j)
  (rpar 12 (mask 12) (2300 * 12) (Co2T3.LR j)) (rlab 2300 (2300 * 12) (Co2T3.LR j)) k k
local notation "walkJ " j:max k:max z:max =>
  walkIK 2300 12 (mask 12) (2300 * 12) Co2T3.S Co2T3.SI 30 (t3St j) (Co2T3.LR j) k k z
local notation "mJ " j:max inO:max k:max =>
  mIK 2300 12 (mask 12) (2300 * 12) Co2T3.S Co2T3.SI 30 (t3St j) (Co2T3.LR j) inO fxP 52 k

theorem hRj {j : ℕ} (hj : j < 13) : ∀ k < cJ j, 0 < k →
    rpar 12 (mask 12) (2300 * 12) (Co2T3.LR j) k < k ∧
      rlab 2300 (2300 * 12) (Co2T3.LR j) k < (rawSteps 2300 S3 thB j).size := by
  intro k hk hk0
  obtain ⟨e1, e2, -⟩ := (recF hj).edge k hk hk0
  rw [(stepsK hj.le).1] at e2
  exact ⟨e1, e2⟩

theorem kstepsJ {j : ℕ} (hj : j < 13) :
    (∀ l < (rawSteps 2300 S3 thB j).size, ∀ x : Fin 2300,
      pg 12 (mask 12) (letterK Co2T3.S Co2T3.SI 30 (stAt (t3St j) l)) x =
        (stp 2300 S3 thB j l x : ℕ)) ∧
      ∀ l < (rawSteps 2300 S3 thB j).size,
        PRep 2300 12 (invLetterK Co2T3.S Co2T3.SI 30 (stAt (t3St j) l)) (stp 2300 S3 thB j l)⁻¹ :=
  have h := kernel_steps binds perm_ok (by norm_num) (fun t ht => thB_lt' ht) (i := j) hj.le
  ⟨h.2.1, h.2.2.2⟩

theorem stp_mem {j l : ℕ} (hj : j < 13) (hl : l < (rawSteps 2300 S3 thB j).size) :
    stp 2300 S3 thB j l ∈ stabB j := by
  obtain ⟨g, hg, hr⟩ := step_rep hj.le (rawStep_mem hl)
  rw [Rep.unique (rep_stp binds perm_ok hl) hr]
  exact hg

theorem tau_mem {j : ℕ} (hj : j < 13) : ∀ k < cJ j, tau j k ∈ stabB j := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [treeF_zero]
      exact (stabB j).one_mem
    · obtain ⟨hp, hl⟩ := hRj hj k hk hk0
      rw [treeF_step (fun k hk hk0 => (hRj hj k hk hk0).1) hk hk0]
      exact (stabB j).mul_mem (stp_mem hj hl) (ih _ hp (by omega))

theorem tau_apply {j : ℕ} (hj : j < 13) : ∀ k < cJ j, ((tau j k) (bpt j) : ℕ) = rptJ j k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [treeF_zero, Equiv.Perm.one_apply, bpt_val' hj, (recF hj).root, base_get hj]
    · obtain ⟨hp, hl⟩ := hRj hj k hk hk0
      rw [treeF_step (fun k hk hk0 => (hRj hj k hk hk0).1) hk hk0, Equiv.Perm.mul_apply,
        ← (kstepsJ hj).1 _ hl, ih _ hp (by omega)]
      exact ((recF hj).edge k hk hk0).2.2

theorem walk_eq {j : ℕ} (hj : j < 13) {k : ℕ} (hk : k < cJ j) (z : Fin 2300) :
    walkJ j k z = ((tau j k)⁻¹ z : ℕ) :=
  walkIK_eq (r := (rawSteps 2300 S3 thB j).size) (c := cJ j)
    (fun l hl x => (kstepsJ hj).2 l hl x) (hRj hj) k k hk z

theorem pts_sub {j : ℕ} (hj : j < 13) :
    ∀ k < thL[j]!.pts.size, ∃ k' < cJ j, rptJ j k' = thL[j]!.pts[k]! := by
  have F := lvFacts hj
  have R := recF hj
  obtain ⟨hcnt, hstep⟩ := stepsK hj.le
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact ⟨0, R.c_pos, by rw [R.root, F.root, base_get hj]⟩
    · obtain ⟨h, hh, s, hs, e⟩ := F.edge k hk hk0
      obtain ⟨k1, hk1, e1⟩ := ih h hh (by omega)
      have hm : s ∈ rawSteps 2300 S3 thB j := mem_rawSteps_iff.2 hs
      obtain ⟨l, hl, rfl⟩ := OrbTr.mem_steps hm
      have hpn := (R.pt k1 hk1).1
      have hc := R.closed k1 hk1 l (by rw [hcnt]; exact hl)
      rw [hstep l hl _ hpn, e1, e] at hc
      have hz : thL[j]!.pts[k]! < 2300 := F.pt_lt k hk
      exact ⟨_, hc, R.pos _ hz hc⟩

theorem orbit_sub {j : ℕ} (hj : j < 13) {g : Equiv.Perm (Fin 2300)} (hg : g ∈ stabB j) :
    ∃ k < cJ j, rptJ j k = (g (bpt j) : ℕ) := by
  have F := lvFacts hj
  obtain ⟨k0, hk0, hs⟩ := exists_thT_inv_mul_memH thirdFactsK hj hg
  have e : g (bpt j) = thT j k0 (bpt j) := by
    have := hs.2 j (Nat.lt_succ_self j)
    rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq] at this
    exact this
  have hk0' : k0 < thL[j]!.pts.size := by rw [← F.tr_size]; exact hk0
  rw [e, rep_apply_bptH thirdFactsK (rep_thTH thirdFactsK hj hk0) hj, (F.tr_rep k0 hk0').2]
  exact pts_sub hj k0 hk0'

theorem thT_mem_Gj {i k : ℕ} (hi : i < 13) (hk : k < tsz i) : thT i k ∈ Gj i := by
  obtain ⟨⟨g, hg, hr⟩, -⟩ := (lvFacts hi).tr_rep k (by rw [← (lvFacts hi).tr_size]; exact hk)
  rw [Rep.unique (rep_thTH thirdFactsK hi hk) hr]
  exact hg

theorem prodFrom_mem_Gj {k : ℕ → ℕ} : ∀ (f j : ℕ), j + f = 13 →
    (∀ i, j ≤ i → i < 13 → k i < tsz i) → ∀ j₀ ≤ j, prodFrom k f j ∈ Gj j₀
  | 0, _, _, _, j₀, _ => by
    rw [prodFrom]
    exact (Gj j₀).one_mem
  | f + 1, j, hj, hk, j₀, hj₀ => by
    rw [prodFrom]
    exact (Gj j₀).mul_mem (Gj_mono hj₀ (thT_mem_Gj (by omega) (hk j le_rfl (by omega))))
      (prodFrom_mem_Gj f (j + 1) (by omega) (fun i hi hi' => hk i (by omega) hi') j₀ (by omega))

theorem stabB_le_Gj {j : ℕ} (hj : j ≤ 13) : stabB j ≤ Gj j := fun s hs => by
  obtain ⟨k, hk, rfl⟩ := exists_prodFromH thirdFactsK (13 - j) j (by omega) s hs
  exact prodFrom_mem_Gj _ _ (by omega) hk j le_rfl

theorem O1_inv {s : Equiv.Perm (Fin 2300)} (hs : s ∈ stabB 1) (y : Fin 2300) :
    s y ∈ O1 ↔ y ∈ O1 := by
  refine iff_of_closed O1 {g | ∃ t ∈ thirdSteps S3 thB 1, Rep 2300 t g} ?_ s
    (stabB_le_Gj (by norm_num) hs) y
  rintro g ⟨t, ht, hg⟩ z hz
  have R := recF (j := 1) (by norm_num)
  obtain ⟨hcnt, hstep⟩ := stepsK (j := 1) (by norm_num)
  have hz' : inO1 z = true := (Finset.mem_filter.1 hz).2
  refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
  change Nat.blt (rposJ 1 (g z)) (cJ 1) = true
  rw [Nat.blt_eq]
  have hz : rposJ 1 z < cJ 1 := by
    have h1 : Nat.blt (rposJ 1 z) (cJ 1) = true := hz'
    rwa [Nat.blt_eq] at h1
  have hm : t ∈ rawSteps 2300 S3 thB 1 := mem_rawSteps_iff.2 ht
  obtain ⟨l, hl, rfl⟩ := OrbTr.mem_steps hm
  have ez := R.pos z z.2 hz
  have hc := R.closed _ hz l (by rw [hcnt]; exact hl)
  rw [ez, hstep l hl _ z.2, hg z] at hc
  exact hc

theorem O42_inv {s : Equiv.Perm (Fin 2300)} (hs : s ∈ stabB 2) (y : Fin 2300) :
    s y ∈ O42 ↔ y ∈ O42 := by
  refine iff_of_closed O42 {g | ∃ t ∈ thirdSteps S3 thB 2, Rep 2300 t g} ?_ s
    (stabB_le_Gj (by norm_num) hs) y
  rintro g ⟨t, ht, hg⟩ z hz
  obtain ⟨hcnt, hstep⟩ := stepsK (j := 2) (by norm_num)
  have hz' : inK oP 42 z = true := (Finset.mem_filter.1 hz).2
  refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
  change inK oP 42 (g z) = true
  obtain ⟨i, hi, ei⟩ := inK_iff.1 hz'
  have hm : t ∈ rawSteps 2300 S3 thB 2 := mem_rawSteps_iff.2 ht
  obtain ⟨l, hl, rfl⟩ := OrbTr.mem_steps hm
  have hc0 := clos_ok
  unfold closK at hc0
  have hc := allN_spec (allN_spec hc0 i hi) l (by rw [hcnt]; exact hl)
  rw [ei, hstep l hl _ z.2, hg z] at hc
  exact hc

theorem locU_val (y : Fin 2300) : (locU y : ℕ) = pg 12 (mask 12) (UP 0) y := by
  rw [← rep_u.apply y.2, u_get y.2]

theorem locU_iff (y : Fin 2300) : locU y = y ↔ pg 12 (mask 12) (UP 0) y = y := by
  rw [← locU_val, Fin.val_inj]

theorem FixS_eq : FixS = (Finset.range 52).image fxF := by
  have hsub : (Finset.range 52).image fxF ⊆ FixS := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hy
    have hi' := Finset.mem_range.1 hi
    simp only [FixS, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [locU_iff, fxF_val hi']
    exact (fxs.1 i hi').2
  have hcard : FixS.card = 52 := by
    have e : FixS.map Fin.valEmbedding =
        (Finset.range 2300).filter fun z => pg 12 (mask 12) (UP 0) z = z := by
      ext z
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Fin.valEmbedding_apply, Finset.mem_range]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.2, (locU_iff y).1 hy⟩
      · rintro ⟨hz, hp⟩
        exact ⟨⟨z, hz⟩, (locU_iff _).2 hp, rfl⟩
    rw [← Finset.card_map Fin.valEmbedding, e, fxs.2.2]
  refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
  rw [hcard, Finset.card_image_of_injOn fxF_injOn, Finset.card_range]

theorem count_fix (Q : Fin 2300 → Bool) :
    ((Finset.range 52).filter fun i => Q (fxF i) = true).card =
      (FixS.filter fun y => Q y = true).card := by
  rw [FixS_eq, Finset.filter_image, Finset.card_image_of_injOn
    (fxF_injOn.mono fun x hx => Finset.mem_coe.2 (Finset.mem_filter.1 (Finset.mem_coe.1 hx)).1)]

theorem mJ_eq {j : ℕ} (hj : j < 13) (inO : ℕ → Bool) {k : ℕ} (hk : k < cJ j) :
    mJ j inO k = (FixS.filter fun y => inO ((tau j k)⁻¹ y) = true).card := by
  rw [mIK, cntN_card, ← count_fix (fun y => inO ((tau j k)⁻¹ y))]
  refine congrArg Finset.card (Finset.filter_congr fun i hi => ?_)
  have hi' := Finset.mem_range.1 hi
  have e := walk_eq hj hk (fxF i)
  rw [fxF_val hi'] at e
  change inO (walkJ j k (fxP i)) = true ↔ _
  rw [e]

theorem mJ_orbit {j : ℕ} (hj : j < 12) (inO : ℕ → Bool)
    (hO : ∀ s ∈ stabB (j + 1), ∀ y, inO (s y) = true ↔ inO y = true)
    {g : Equiv.Perm (Fin 2300)} (hg : g ∈ locH3 ⊓ stabB j) {k : ℕ} (hk : k < cJ j)
    (hx : rptJ j k = (g (bpt j) : ℕ)) : mJ j inO k = mJ j inO 0 := by
  have hj13 : j < 13 := by omega
  have hg' := Subgroup.mem_inf.1 hg
  have hc := (mem_locH3.1 hg'.1).2
  rw [mJ_eq hj13 inO hk, mJ_eq hj13 inO (recF hj13).c_pos, treeF_zero, inv_one]
  simp only [Equiv.Perm.one_apply]
  have hτ := tau_mem hj13 k hk
  have hs : (tau j k)⁻¹ * g ∈ stabB (j + 1) := by
    refine ⟨co2P.mul_mem (co2P.inv_mem hτ.1) hg'.2.1, fun i hi => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · rw [Equiv.Perm.mul_apply, hg'.2.2 i hi, Equiv.Perm.inv_eq_iff_eq, hτ.2 i hi]
    · rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
      apply Fin.ext
      rw [tau_apply hj13 k hk, hx]
  have key := card_filter_conj FixS (Finset.univ.filter fun y => inO y = true) (h := g)
    (s := (tau j k)⁻¹ * g) (fun y => ?_) (fun y => ?_)
  · rw [mul_inv_inv_mul] at key
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at key
    exact key
  · simp only [FixS, Finset.mem_filter, Finset.mem_univ, true_and]
    exact fix_iff_of_comm locU g hc y
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hO _ hs y

theorem fix_of_Hj {j : ℕ} (hj : j < 12) {g : Equiv.Perm (Fin 2300)} (hg : g ∈ Hj j) :
    locU (g (bpt j)) = g (bpt j) :=
  fix_of_comm' locU g (bpt j) (mem_locH3.1 (Subgroup.mem_inf.1 hg).1).2
    (locU_fixH thirdFactsK hj)

theorem card_Hj_cand {j : ℕ} (hj : j < 12) (inO : ℕ → Bool)
    (hO : ∀ s ∈ stabB (j + 1), ∀ y, inO (s y) = true ↔ inO y = true) :
    Nat.card (Hj j) ≤ candK 2300 12 (mask 12) (2300 * 12) Co2T3.S Co2T3.SI 30 (t3St j)
      (Co2T3.LR j) inO fxP 52 (mJ j inO 0) * Nat.card (Hj (j + 1)) := by
  have hj13 : j < 13 := by omega
  set A := ((Finset.range 52).filter fun i =>
    (bAnd(Nat.blt (rposJ j (fxP i)) (cJ j), Nat.beq (mJ j inO (rposJ j (fxP i))) (mJ j inO 0))) =
      true).image fxF
  have hA : A.card ≤ candK 2300 12 (mask 12) (2300 * 12) Co2T3.S Co2T3.SI 30 (t3St j)
      (Co2T3.LR j) inO fxP 52 (mJ j inO 0) := by
    refine Finset.card_image_le.trans (le_of_eq ?_)
    rw [candK, cntN_card]
    refine congrArg Finset.card (Finset.filter_congr fun i _ => ?_)
    rw [CFSG.KS.Raw.Orb.strictB_eq]
  refine (card_le_orbit (Hj j) (Hj (j + 1)) (bpt j) A mem_Hj_succ fun g hg => ?_).trans
    (Nat.mul_le_mul_right _ hA)
  have hfix := fix_of_Hj hj hg
  have hmem : g (bpt j) ∈ FixS := by simpa using hfix
  rw [FixS_eq] at hmem
  obtain ⟨i, hi, ei⟩ := Finset.mem_image.1 hmem
  have hi' := Finset.mem_range.1 hi
  obtain ⟨k, hk, ek⟩ := orbit_sub hj13 (Subgroup.mem_inf.1 hg).2
  have hpos : rposJ j (fxP i) = k := by
    rw [← fxF_val hi', ei, ← ek]
    exact ((recF hj13).pt k hk).2
  refine Finset.mem_image.2 ⟨i, Finset.mem_filter.2 ⟨hi, ?_⟩, ei⟩
  rw [hpos, CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq]
  exact ⟨hk, mJ_orbit hj inO hO hg hk ek⟩

theorem card_Hj_fix {j : ℕ} (hj : j < 12) :
    Nat.card (Hj j) ≤ fixCntK 12 (mask 12) (Co2T3.LR j) (UP 0) * Nat.card (Hj (j + 1)) := by
  have hj13 : j < 13 := by omega
  set A := ((Finset.range (cJ j)).filter fun k =>
    pg 12 (mask 12) (UP 0) (rptJ j k) = rptJ j k).image fun k => toF (rptJ j k)
  have hA : A.card ≤ fixCntK 12 (mask 12) (Co2T3.LR j) (UP 0) := by
    refine Finset.card_image_le.trans (le_of_eq ?_)
    rw [fixCntK, cntN_card]
    refine congrArg Finset.card (Finset.filter_congr fun k _ => ?_)
    rw [CFSG.KS.Raw.Orb.strictB_eq, Nat.beq_eq]
  refine (card_le_orbit (Hj j) (Hj (j + 1)) (bpt j) A mem_Hj_succ fun g hg => ?_).trans
    (Nat.mul_le_mul_right _ hA)
  obtain ⟨k, hk, ek⟩ := orbit_sub hj13 (Subgroup.mem_inf.1 hg).2
  have hfix := (locU_iff _).1 (fix_of_Hj hj hg)
  refine Finset.mem_image.2 ⟨k, Finset.mem_filter.2 ⟨Finset.mem_range.2 hk, ?_⟩, ?_⟩
  · rw [ek]
    exact hfix
  · apply Fin.ext
    rw [ek, toF_val (g (bpt j)).2]

theorem card_Hj_last : Nat.card (Hj 12) ≤ cJ 12 * Nat.card (Hj 13) := by
  set A := (Finset.range (cJ 12)).image fun k => toF (rptJ 12 k)
  have hA : A.card ≤ cJ 12 := Finset.card_image_le.trans (by rw [Finset.card_range])
  refine (card_le_orbit (Hj 12) (Hj 13) (bpt 12) A mem_Hj_succ fun g hg => ?_).trans
    (Nat.mul_le_mul_right _ hA)
  obtain ⟨k, hk, ek⟩ := orbit_sub (by norm_num) (Subgroup.mem_inf.1 hg).2
  refine Finset.mem_image.2 ⟨k, Finset.mem_range.2 hk, ?_⟩
  apply Fin.ext
  rw [ek, toF_val (g (bpt 12)).2]

theorem card_Hj_le {j : ℕ} (hj : j < 13) :
    Nat.card (Hj j) ≤ cB.getD j 0 * Nat.card (Hj (j + 1)) := by
  rcases (by omega : j = 0 ∨ j = 1 ∨ (2 ≤ j ∧ j < 12) ∨ j = 12) with rfl | rfl | ⟨h2, h12⟩ | rfl
  · have h := card_Hj_cand (j := 0) (by norm_num) inO1 fun s hs y => by
      have := O1_inv hs y
      simpa using this
    rwa [Nat.eq_of_beq_eq_true cand0_ok] at h
  · have h := card_Hj_cand (j := 1) (by norm_num) inO42 fun s hs y => by
      have := O42_inv hs y
      simpa using this
    rwa [Nat.eq_of_beq_eq_true cand1_ok] at h
  · have h := card_Hj_fix h12
    have e := Nat.eq_of_beq_eq_true (allN_spec cnt_ok (j - 2) (by omega))
    rw [show Nat.add (j - 2) 2 = j from by rw [Nat.add_eq]; omega] at e
    rw [e] at h
    refine h.trans (le_of_eq ?_)
    congr 1
    interval_cases j <;> rfl
  · have h := card_Hj_last
    rwa [show cJ 12 = 2 from Nat.eq_of_beq_eq_true (allN_spec sizes_ok 12 (by norm_num))] at h

theorem card_locH3_leK : Nat.card locH3 ≤ 1474560 := by
  have h := card_le_chain (a := fun j => Nat.card (Hj j)) (c := fun j => cB.getD j 0) (n := 13)
    fun j hj => card_Hj_le hj
  have h0 : Hj 0 = locH3 := by
    rw [Hj, stabB_zero]
    exact inf_eq_left.2 fun g hg => (mem_locH3.1 hg).1
  have h13 : Nat.card (Hj 13) ≤ 1 := by
    have : Hj 13 ≤ ⊥ := by
      rw [← stabB_thirteenH thirdFactsK]
      exact inf_le_right
    exact (Subgroup.card_le_of_le this).trans (le_of_eq Subgroup.card_bot)
  simp only [h0] at h
  refine h.trans ?_
  have hp : ∏ j ∈ Finset.range 13, cB.getD j 0 = 1474560 := by
    simp [Finset.prod_range_succ, cB]
  rw [hp]
  calc 1474560 * Nat.card (Hj 13) ≤ 1474560 * 1 := Nat.mul_le_mul_left _ h13
    _ = 1474560 := by norm_num

end CertificateChecks.KernelSporSch.Co2M
