module

public import Certificates.Kernel.Sporadic.OddCore.McLC
public import Certificates.Kernel.Sporadic.OddCore.McLSub
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue3
public import CFSG.Certificates.Kernel.Misc.PairCountSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.KernelSpor.McL2287

open CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SuzOddCore CFSG.KC.Enum CFSG.KS
open CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.BfsPin CFSG.Monster.B.Co2.Native
open CFSG.KS.Mathieu CFSG.KC.Misc.HexAt CFSG.Sporadic.SmallOddCore.Native

theorem idc : canonK 35 6 (mask 6) (35 * 6) (pidn 35 6) = true ∧ idK 35 6 (mask 6) = true ∧
    szOK 35 6 = true := by
  simpa only [bAnd_iff] using id_ok

theorem idTab_eq : idTab 35 = unpack 35 6 (pidn 35 6) := (idK_sound idc.2.1).symm

theorem rec_get35 {cnt i : Nat} {T PL : Nat → Nat} (hi : i < cnt) :
    (penumRec 35 6 cnt T PL).tabs[i]! = unpack 35 6 (T i) := by
  rw [getElem!_pos _ i (by simp only [penumRec, Array.size_ofFn]; exact hi)]
  simp only [penumRec, Array.getElem_ofFn]

theorem comp35 {p q : Nat} (hp : canonK 35 6 (mask 6) (35 * 6) p = true)
    (hq : canonK 35 6 (mask 6) (35 * 6) q = true) :
    comp 35 (unpack 35 6 p) (unpack 35 6 q) = unpack 35 6 (pcomp 35 6 (mask 6) p q) :=
  compA_unpack hp hq

theorem cent_eq {k : Nat} (hk : k < 30) : natArr (mclCentTbl k) = unpack 275 9 (McLCT.F k) := by
  have h := CFSG.KC.Misc.HexFlat.hexT_sound McLCT.all (by norm_num) k hk
  rw [← McLCT.eq] at h
  exact h

theorem cent_perm {k j : Nat} (hk : k < 30)
    (h : invEqK 275 9 (mask 9) (275 * 9) (McLCT.F k) (McLCI j) = true) :
    CFSG.Sporadic.SmallOddCore.permOK 275 (mclCentTbl k) = true := by
  obtain ⟨h1, h2⟩ := invEqK_sound h
  unfold CFSG.Sporadic.SmallOddCore.permOK
  rw [cent_eq hk, h1]
  exact h2

theorem fix_eq : mclFix = fixL := by
  rw [← sel_spec fix_sel]
  unfold mclFix fixedList mclT0Arr
  apply List.filter_congr
  intro x hx
  have hx' : x < 275 := List.mem_range.1 hx
  rw [cent_eq (by norm_num), CFSG.KC.Misc.PairCount.unpack_get hx']
  cases h : Nat.beq (pg 9 (mask 9) (McLCT.F 4) x) x
  · have : pg 9 (mask 9) (McLCT.F 4) x ≠ x := fun e => by simp [e] at h
    simp [this]
  · simp [Nat.eq_of_beq_eq_true h]

theorem fixL_nodup : fixL.Nodup := by
  rw [← sel_spec fix_sel]
  exact List.nodup_range.filter _

theorem fixL_len : fixL.length = 35 := rfl

theorem fixL_mem_lt {x : Nat} (hx : x ∈ fixL) : x < 275 := by
  rw [← sel_spec fix_sel] at hx
  exact List.mem_range.1 (List.mem_filter.1 hx).1

theorem fixL_lt {a : Nat} (ha : a < 35) : fixL[a]'(by rw [fixL_len]; exact ha) < 275 :=
  fixL_mem_lt (List.getElem_mem _)

theorem xg_facts {k : Nat} (hk : k < 2) : canonK 35 6 (mask 6) (35 * 6) (MXE.G k) = true ∧
    ∀ a < 35, pg 9 (mask 9) (McLCT.F (Nat.add k 5)) (nget fixL a) =
      nget fixL (pg 6 (mask 6) (MXE.G k) a) := by
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec xg_ok k hk)
  exact ⟨h1, fun a ha => Nat.eq_of_beq_eq_true (allN_spec h2 a ha)⟩

theorem canon_lt {p a : Nat} (hp : canonK 35 6 (mask 6) (35 * 6) p = true) (ha : a < 35) :
    pg 6 (mask 6) p a < 35 := by
  have h' : bAnd(szOK 35 6, bAnd(Nat.beq (Nat.shiftRight p (35 * 6)) (nat_lit 0),
      allN 35 (fun i => Nat.blt (pg 6 (mask 6) p i) 35))) = true := hp
  simp only [bAnd_iff] at h'
  exact Eq.mp Nat.blt_eq (allN_spec h'.2.2 a ha)

theorem xgens_get {k : Nat} (hk : k < 2) : mclXGens[k]! = unpack 35 6 (MXE.G k) := by
  obtain ⟨hc, hr⟩ := xg_facts hk
  rw [getElem!_pos mclXGens k (by simp [mclXGens]; omega)]
  simp only [mclXGens, Array.getElem_ofFn]
  rw [fix_eq, cent_eq (by omega)]
  apply Array.ext
  · simp [restrictArr, unpack, fixL_len]
  · intro a h1 _
    have ha : a < 35 := by simpa [restrictArr, fixL_len] using h1
    simp only [restrictArr, List.getElem_toArray, List.getElem_map]
    rw [CFSG.KC.Misc.PairCount.unpack_get (fixL_lt ha)]
    simp only [unpack, Array.getElem_ofFn]
    have e1 := hr a ha
    rw [nget_get fixL (by rw [fixL_len]; exact ha)] at e1
    have hb := canon_lt hc ha
    rw [nget_get fixL (by rw [fixL_len]; exact hb)] at e1
    have e2 : Nat.add k 5 = k + 5 := rfl
    rw [e2] at e1
    rw [e1, fixL_nodup.idxOf_getElem]

theorem xi_facts {k : Nat} (hk : k < 2) :
    invEqK 35 6 (mask 6) (35 * 6) (MXE.G k) (MXI k) = true ∧
      canonK 35 6 (mask 6) (35 * 6) (MXI k) = true ∧
      Nat.beq (pcomp 35 6 (mask 6) (MXI k) (MXE.G k)) (pidn 35 6) = true := by
  simpa only [bAnd_iff] using allN_spec xi_ok k hk

theorem xinvs_get {k : Nat} (hk : k < 2) : mclXInvs[k]! = unpack 35 6 (MXI k) := by
  rw [mclXInvs, getElem!_pos _ k (by simp [mclXGens]; omega), Array.getElem_map,
    ← getElem!_pos mclXGens k (by simp [mclXGens]; omega), xgens_get hk]
  exact (invEqK_sound (xi_facts hk).1).1

theorem g_ok : GensOK 35 6 MXE.k MXE.G mclXGens :=
  ⟨rfl, fun _ hj => ⟨xgens_get hj, (xg_facts hj).1⟩⟩

theorem fg_ok : GensOK 35 6 MOF.k MOF.G mclXGens :=
  ⟨rfl, fun j hj => by
    have e := Nat.eq_of_beq_eq_true ((bAnd_iff _ _).1 (allN_spec fam_g j hj)).1
    rw [e]
    exact ⟨xgens_get hj, (xg_facts hj).1⟩⟩

theorem fgi_ok : GensOK 35 6 MOF.k MOF.GI mclXInvs :=
  ⟨by simp [mclXInvs, mclXGens]; rfl, fun j hj => by
    have e := Nat.eq_of_beq_eq_true ((bAnd_iff _ _).1 (allN_spec fam_g j hj)).2
    rw [e]
    exact ⟨xinvs_get hj, (xi_facts hj).2.1⟩⟩

theorem invs : invsOK 35 mclXGens mclXInvs = true := by
  unfold invsOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨by simp [mclXInvs], ?_⟩
  unfold allBelow
  rw [all_range_iff]
  intro k hk
  have hk2 : k < 2 := by simpa [mclXGens] using hk
  obtain ⟨-, hci, hpi⟩ := xi_facts hk2
  simp only [Bool.and_eq_true, beq_iff_eq]
  rw [xinvs_get hk2, xgens_get hk2]
  refine ⟨unpack_size _ _ _, ?_⟩
  rw [comp35 hci (xg_facts hk2).1, idTab_eq, Nat.eq_of_beq_eq_true hpi]

theorem x_pt {i : Nat} (hi : i < MXE.cnt) : penumPtK 35 6 (mask 6) (35 * 6) false MXE.G MXE.GI
    MXE.k MXE.cnt MXE.T MXE.PL MXE.POS MXE.SRT MXE.SRI i = true := by
  have e : MXE.cnt = 20160 := rfl
  rcases Nat.lt_or_ge i 5040 with h0 | h0
  · exact penumSl_spec x_sl0 i (Nat.zero_le _) (by omega) hi
  rcases Nat.lt_or_ge i 10080 with h1 | h1
  · exact penumSl_spec x_sl1 i h0 (by omega) hi
  rcases Nat.lt_or_ge i 15120 with h2 | h2
  · exact penumSl_spec x_sl2 i h1 (by omega) hi
  · exact penumSl_spec x_sl3 i h2 (by omega) hi

theorem x_enum : mclXEnum = penumRec 35 6 MXE.cnt MXE.T MXE.PL ∧
    enumOK 35 mclXGens (penumRec 35 6 MXE.cnt MXE.T MXE.PL) = true :=
  penumK_left_sound (cap := 20160) idc.2.2 g_ok x_hd (fun _ hi => x_pt hi)

@[expose] noncomputable def orbRec (l : Nat) : Enum :=
  penumRec 35 6 (MOF.C l) (offF MOF.T (MOF.TO l)) (offF MOF.PL (MOF.PLO l))

theorem orb_k {l : Nat} (hl : l < 14) : orbK l = true := by
  interval_cases l
  exacts [o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13]

theorem cover_all {k : Nat} (hk : k < 20160) : coverK k = true := by
  rcases Nat.lt_or_ge k 5040 with h0 | h0
  · simpa using allBlk_spec cover0 k h0
  rcases Nat.lt_or_ge k 10080 with h1 | h1
  · simpa [Nat.add_sub_cancel' h0] using allBlk_spec cover1 (k - 5040) (by omega)
  rcases Nat.lt_or_ge k 15120 with h2 | h2
  · simpa [Nat.add_sub_cancel' h1] using allBlk_spec cover2 (k - 10080) (by omega)
  · simpa [Nat.add_sub_cancel' h2] using allBlk_spec cover3 (k - 15120) (by omega)

theorem orb_hd {l : Nat} (hl : l < 14) :
    penumHdK (MOF.R l) (MOF.C l) 5000 (offF MOF.T (MOF.TO l)) (offF MOF.PL (MOF.PLO l)) = true :=
  ((bAnd_iff _ _).1 (orb_k hl)).1

theorem orb_pt {l i : Nat} (hl : l < 14) (hi : i < MOF.C l) :
    penumPtK 35 6 (mask 6) (35 * 6) true MOF.G MOF.GI MOF.k (MOF.C l) (offF MOF.T (MOF.TO l))
      (offF MOF.PL (MOF.PLO l)) (offF MOF.POS (MOF.POSO l)) (offF MOF.SRT (MOF.SRTO l))
      (offF MOF.SRI (MOF.SRIO l)) i = true :=
  penumSl_spec ((bAnd_iff _ _).1 (orb_k hl)).2 i (Nat.zero_le _) (by omega) hi

theorem words_lt : ∀ l < 14, ∀ j ∈ mclXWords.getD l [], j < mclXGens.size := by
  decide

theorem rep_eq {l : Nat} (hl : l < 14) :
    wordTabS 35 mclXGens (mclXWords.getD l []) = unpack 35 6 (MOF.R l) := by
  obtain ⟨hr, -⟩ := (bAnd_iff _ _).1 (allN_spec reps_ok l hl)
  rw [Nat.eq_of_beq_eq_true hr, lget2_eq]
  exact (wordTabK_eq idTab_eq idc.1 _ (fun j hj => by
    have hj2 : j < 2 := words_lt l hl j hj
    exact ⟨xgens_get hj2, (xg_facts hj2).1⟩)).1

theorem orbits_get {l : Nat} (hl : l < 14) : mclXOrbits[l]! = orbitBFS 35 mclXGens mclXInvs
    (wordTabS 35 mclXGens (mclXWords.getD l [])) 5000 := by
  rw [getElem!_pos mclXOrbits l (by simp [mclXOrbits]; omega)]
  simp [mclXOrbits]

theorem orb_enum {l : Nat} (hl : l < 14) : mclXOrbits[l]! = orbRec l ∧
    treeOK (conjStep 35 mclXGens mclXInvs) mclXGens.size
      (wordTabS 35 mclXGens (mclXWords.getD l [])) (orbRec l) = true := by
  rw [orbits_get hl]
  exact penumK_conj_sound idc.2.2 fg_ok fgi_ok (rep_eq hl) (orb_hd hl) (fun _ hi => orb_pt hl hi)

theorem nget_getD (L : List Nat) (i : Nat) : nget L i = L.getD i 0 := by
  induction L generalizing i with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem orb_size {l : Nat} (hl : l < 14) : (orbRec l).tabs.size = mclXSizes.getD l 0 := by
  obtain ⟨-, hc⟩ := (bAnd_iff _ _).1 (allN_spec reps_ok l hl)
  simp only [orbRec, penumRec, Array.size_ofFn]
  rw [Nat.eq_of_beq_eq_true hc, nget_getD]

theorem orb_get {l q : Nat} (hl : l < 14) (hq : q < MOF.C l) :
    (orbRec l).tabs[q]! = unpack 35 6 (offF MOF.T (MOF.TO l) q) ∧
      canonK 35 6 (mask 6) (35 * 6) (offF MOF.T (MOF.TO l) q) = true := by
  refine ⟨?_, penumPt_canon (orb_pt hl hq)⟩
  rw [getElem!_pos _ q (by simp [orbRec, penumRec, hq])]
  simp [orbRec, penumRec]

theorem root_canon {l : Nat} (hl : l < 14) : canonK 35 6 (mask 6) (35 * 6) (MOF.R l) = true := by
  have hh := orb_hd hl
  unfold penumHdK at hh
  obtain ⟨h0, -, hr, -⟩ := (by simpa only [bAnd_iff] using hh :
    Nat.blt 0 (MOF.C l) = true ∧ Nat.ble (MOF.C l) 5000 = true ∧
      Nat.beq (offF MOF.T (MOF.TO l) 0) (MOF.R l) = true ∧
      Nat.beq (CFSG.KS.PEnum.r32 (offF MOF.PL (MOF.PLO l)) 0) 0 = true)
  rw [← Nat.eq_of_beq_eq_true hr]
  exact (orb_get hl (Eq.mp Nat.blt_eq h0)).2

theorem facts2287 :
    (mclFix.length = 35 ∧ mclXGens.size = 2 ∧ invsOK 35 mclXGens mclXInvs = true ∧
      mclXOrbits.size = 14 ∧ CFSG.Sporadic.SmallOddCore.permOK 275 (mclCentTbl 4) = true ∧
      ∀ k < 2, CFSG.Sporadic.SmallOddCore.permOK 275 (mclCentTbl (k + 5)) = true) ∧
    (enumOK 35 mclXGens mclXEnum = true ∧ mclXEnum.tabs.size = 20160) ∧
    ((∀ l < 14, orbitOK 35 mclXGens mclXInvs (wordTabS 35 mclXGens (mclXWords.getD l []))
        mclXOrbits[l]! = true ∧ mclXOrbits[l]!.tabs.size = mclXSizes.getD l 0) ∧
      (∀ l < 14, ∀ l' < 14, l ≠ l' →
        notInOK mclXOrbits[l]!.tabs (wordTabS 35 mclXGens (mclXWords.getD l' [])) = true) ∧
      (∀ l < 14, ∀ j ∈ mclXWords.getD l [], j < mclXGens.size) ∧
      wordTabS 35 mclXGens (mclXWords.getD 0 []) = idTab 35) ∧
    (coverAllOK mclXEnum.tabs mclXOrbits = true) ∧
    (∀ U : Finset (Fin 14), 0 ∈ U → (∑ l ∈ U, mclXSizes.getD l 0) ∣ 20160 →
      U = {0} ∨ U = Finset.univ) := by
  obtain ⟨p4, p5, p6⟩ := (by simpa only [bAnd_iff] using c_perm :
    invEqK 275 9 (mask 9) (275 * 9) (McLCT.F 4) (McLCI 0) = true ∧
    invEqK 275 9 (mask 9) (275 * 9) (McLCT.F 5) (McLCI 1) = true ∧
    invEqK 275 9 (mask 9) (275 * 9) (McLCT.F 6) (McLCI 2) = true)
  refine ⟨⟨by rw [fix_eq]; rfl, rfl, invs, by simp [mclXOrbits], cent_perm (by norm_num) p4,
    fun k hk => ?_⟩, ⟨?_, ?_⟩, ⟨fun l hl => ?_, fun l hl l' hl' hne => ?_, words_lt, rfl⟩, ?_,
    sizes_sums⟩
  · interval_cases k
    · exact cent_perm (by norm_num) p5
    · exact cent_perm (by norm_num) p6
  · rw [x_enum.1]
    exact x_enum.2
  · rw [x_enum.1]
    simp [penumRec]
    rfl
  · obtain ⟨e, ht⟩ := orb_enum hl
    rw [e]
    refine ⟨?_, orb_size hl⟩
    unfold orbitOK
    rw [invs, ht]
    rfl
  · rw [(orb_enum hl).1, rep_eq hl']
    unfold notInOK allBelow
    rw [all_range_iff]
    intro q hq
    have hq' : q < MOF.C l := by simpa [orbRec, penumRec] using hq
    obtain ⟨hg, hc⟩ := orb_get hl hq'
    rw [hg, beq_unpack hc (root_canon hl')]
    have hn := allN_spec (allN_spec notin l hl) l' hl'
    have hb : Nat.beq l l' = false := by
      cases h : Nat.beq l l'
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) hne
    rw [hb] at hn
    have hz := allN_spec hn q hq'
    cases h : Nat.beq (offF MOF.T (MOF.TO l) q) (MOF.R l')
    · rfl
    · rw [h] at hz
      exact absurd hz (by decide)
  · rw [x_enum.1]
    unfold coverAllOK allBelow
    rw [all_range_iff]
    intro k hk
    have hk' : k < MXE.cnt := by simpa [penumRec] using hk
    have hc := cover_all (k := k) hk'
    unfold coverK at hc
    simp only [strictB_app'] at hc
    obtain ⟨hl, hq, he⟩ := (by simpa only [bAnd_iff] using hc :
      Nat.blt (Nat.shiftRight (MCOV k) 16) 14 = true ∧
      Nat.blt (Nat.land (MCOV k) 65535) (MOF.C (Nat.shiftRight (MCOV k) 16)) = true ∧
      Nat.beq (offF MOF.T (MOF.TO (Nat.shiftRight (MCOV k) 16)) (Nat.land (MCOV k) 65535))
        (MXE.T k) = true)
    have hl' := Eq.mp Nat.blt_eq hl
    unfold anyBelow
    rw [List.any_eq_true]
    have hsz : Nat.shiftRight (MCOV k) 16 < mclXOrbits.size := by simpa [mclXOrbits] using hl'
    refine ⟨Nat.shiftRight (MCOV k) 16, List.mem_range.2 hsz, ?_⟩
    rw [getElem!_map_eq _ _ hsz, (orb_enum hl').1, rec_get35 hk']
    exact penum_found_sound (fun _ hx => orb_pt hl' hx) (Eq.mp Nat.blt_eq hq)
      (Nat.eq_of_beq_eq_true he)

end CertificateChecks.KernelSpor.McL2287

end
