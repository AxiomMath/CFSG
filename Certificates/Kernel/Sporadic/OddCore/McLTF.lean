module

public import Certificates.Kernel.Sporadic.OddCore.McLTK
public import Certificates.Kernel.Sporadic.OddCore.McLTwoF
public import Certificates.Kernel.Sporadic.OddCore.CentGlue
public import CFSG.Certificates.Kernel.Spor.MulHAbsSound
import Mathlib.Tactic.IntervalCases
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheckBase
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue3

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.McLTK

open CFSG.Sporadic.Recognition.McLAS CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.BfsPin CertificateChecks.KernelCensus
open CertificateChecks.KernelSpor CFSG.Monster.B.Co2.Native

local notation "⟪" p "⟫" => tabT (unpack 275 9 p)

theorem base : szOK 275 9 = true ∧ cK idP = true ∧ CFSG.KS.Prim.idK 275 9 (mask 9) = true ∧
    allN 11 (fun k => cK (McLTh.F k) && cK (McLThI k) && iE (McLTh.F k) (McLThI k)) = true ∧
    allN 15 (fun k => cK (McLTl.F k) && cK (McLTlI k) && iE (McLTl.F k) (McLTlI k)) = true ∧
    cK (McLCT.F 0) = true ∧ cK (McLTO 0) = true ∧ iE (McLCT.F 0) (McLTO 0) = true ∧
    allN 2 (fun j => Nat.beq (McLTC.G j) (McLC.S j) && cK (McLTC.G j) && cK (McLTC.GI j) &&
      iE (McLTC.G j) (McLTC.GI j)) = true ∧
    allN 5 (fun j => Nat.beq (McLTT.G j) idP && Nat.beq (McLTT.GI j) (McLTh.F (j + 6))) = true ∧
    allN 5 (fun j => Nat.beq (McLTR.G j) idP && Nat.beq (McLTR.GI j) (McLTl.F (j + 2))) = true ∧
    allN 4 (fun j => Nat.beq (McLTA.G j) idP && Nat.beq (McLTA.GI j) (McLTl.F (j + 7))) = true ∧
    McLTT.cnt = 729 ∧ McLTR.cnt = 243 ∧ McLTA.cnt = 81 ∧ McLTC.cnt = 30800 ∧
    penumHdK idP McLTT.cnt 800 McLTT.T McLTT.PL = true ∧
    penumHdK idP McLTR.cnt 300 McLTR.T McLTR.PL = true ∧
    penumHdK idP McLTA.cnt 200 McLTA.T McLTA.PL = true ∧
    penumHdK X McLTC.cnt 30800 McLTC.T McLTC.PL = true := by
  have h := base_ok
  simp only [Bool.and_eq_true, and_assoc] at h
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18,
    b19⟩ := h
  exact ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, Nat.eq_of_beq_eq_true b12,
    Nat.eq_of_beq_eq_true b13, Nat.eq_of_beq_eq_true b14, Nat.eq_of_beq_eq_true b15, b16, b17,
    b18, b19⟩

theorem hn : szOK 275 9 = true := base.1

theorem hidc : canonK 275 9 (mask 9) (275 * 9) idP = true := base.2.1

theorem hidA : idA 275 = unpack 275 9 idP := (idK_sound base.2.2.1).symm

theorem hid : idT 275 = ⟪idP⟫ := by rw [idT_tabT, hidA]

theorem thF {k : Nat} (hk : k < 11) : canonK 275 9 (mask 9) (275 * 9) (McLTh.F k) = true ∧
    canonK 275 9 (mask 9) (275 * 9) (McLThI k) = true ∧
    invEqK 275 9 (mask 9) (275 * 9) (McLTh.F k) (McLThI k) = true := by
  have h := allN_spec base.2.2.2.1 k hk
  simp only [Bool.and_eq_true, and_assoc] at h
  exact h

theorem tlF {k : Nat} (hk : k < 15) : canonK 275 9 (mask 9) (275 * 9) (McLTl.F k) = true ∧
    canonK 275 9 (mask 9) (275 * 9) (McLTlI k) = true ∧
    invEqK 275 9 (mask 9) (275 * 9) (McLTl.F k) (McLTlI k) = true := by
  have h := allN_spec base.2.2.2.2.1 k hk
  simp only [Bool.and_eq_true, and_assoc] at h
  exact h

theorem outF : canonK 275 9 (mask 9) (275 * 9) (McLCT.F 0) = true ∧
    canonK 275 9 (mask 9) (275 * 9) (McLTO 0) = true ∧
    invEqK 275 9 (mask 9) (275 * 9) (McLCT.F 0) (McLTO 0) = true :=
  ⟨base.2.2.2.2.2.1, base.2.2.2.2.2.2.1, base.2.2.2.2.2.2.2.1⟩

theorem pgF {j : Nat} (hj : j < 2) : McLTC.G j = McLC.S j ∧
    canonK 275 9 (mask 9) (275 * 9) (McLTC.G j) = true ∧
    canonK 275 9 (mask 9) (275 * 9) (McLTC.GI j) = true ∧
    invEqK 275 9 (mask 9) (275 * 9) (McLTC.G j) (McLTC.GI j) = true := by
  have h := allN_spec base.2.2.2.2.2.2.2.2.1 j hj
  simp only [Bool.and_eq_true, and_assoc] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, h.2⟩

theorem tG {j : Nat} (hj : j < 5) : McLTT.G j = idP ∧ McLTT.GI j = McLTh.F (j + 6) := by
  have h := allN_spec base.2.2.2.2.2.2.2.2.2.1 j hj
  simp only [Bool.and_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem rG {j : Nat} (hj : j < 5) : McLTR.G j = idP ∧ McLTR.GI j = McLTl.F (j + 2) := by
  have h := allN_spec base.2.2.2.2.2.2.2.2.2.2.1 j hj
  simp only [Bool.and_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem aG {j : Nat} (hj : j < 4) : McLTA.G j = idP ∧ McLTA.GI j = McLTl.F (j + 7) := by
  have h := allN_spec base.2.2.2.2.2.2.2.2.2.2.2.1 j hj
  simp only [Bool.and_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem cT : McLTT.cnt = 729 := base.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem cR : McLTR.cnt = 243 := base.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem cA : McLTA.cnt = 81 := base.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem cC : McLTC.cnt = 30800 := base.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem hdT : penumHdK idP McLTT.cnt 800 McLTT.T McLTT.PL = true :=
  base.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem hdR : penumHdK idP McLTR.cnt 300 McLTR.T McLTR.PL = true :=
  base.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem hdA : penumHdK idP McLTA.cnt 200 McLTA.T McLTA.PL = true :=
  base.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem hdC : penumHdK X McLTC.cnt 30800 McLTC.T McLTC.PL = true :=
  base.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem th_tab {k : Nat} (hk : k < 11) : threeTbl k = ⟪McLTh.F k⟫ := by
  have h := CFSG.KC.Misc.HexFlat.hexT_sound McLTh.all (by norm_num) k hk
  rw [← McLTh.eq] at h
  unfold threeTbl
  rw [← h, tabT_natArr]

theorem tl_tab {k : Nat} (hk : k < 15) : tlTbl k = ⟪McLTl.F k⟫ := by
  have h := CFSG.KC.Misc.HexFlat.hexT_sound McLTl.all (by norm_num) k hk
  rw [← McLTl.eq] at h
  unfold tlTbl
  rw [← h, tabT_natArr]

theorem out_tab : mclOuterTbl = ⟪McLCT.F 0⟫ := by
  have h := CFSG.KC.Misc.HexFlat.hexT_sound McLCT.all (by norm_num) 0 (by norm_num)
  rw [← McLCT.eq] at h
  change mclCentTbl 0 = _
  unfold mclCentTbl
  rw [← h, tabT_natArr]

theorem inv_tab {p q : Nat} (h : invEqK 275 9 (mask 9) (275 * 9) p q = true) :
    invT 275 ⟪p⟫ = ⟪q⟫ := invT_unpack (by norm_num) h

theorem sift_eq' {p : Nat} (hp : canonK 275 9 (mask 9) (275 * 9) p = true) :
    mclSift ⟪p⟫ = sK p :=
  CertificateChecks.KernelSpor.McLTwo.sift_eq hp

theorem sylT_tabs : TabsOK 275 9 5 McLTT.GI sylowThreeGens.toArray := by
  refine ⟨by simp [sylowThreeGens], fun j hj => ?_⟩
  rw [(tG hj).2]
  refine ⟨?_, (thF (by omega)).1⟩
  rw [← th_tab (by omega)]
  simp [sylowThreeGens, getElem!_pos, hj]

theorem rG_tabs : TabsOK 275 9 5 McLTR.GI rGens3 := by
  refine ⟨by simp [rGens3], fun j hj => ?_⟩
  rw [(rG hj).2]
  refine ⟨?_, (tlF (by omega)).1⟩
  rw [← tl_tab (by omega)]
  simp [rGens3, getElem!_pos, hj]

theorem aG_tabs : TabsOK 275 9 4 McLTA.GI aGens3 := by
  refine ⟨by simp [aGens3], fun j hj => ?_⟩
  rw [(aG hj).2]
  refine ⟨?_, (tlF (by omega)).1⟩
  rw [← tl_tab (by omega)]
  simp [aGens3, getElem!_pos, hj]

theorem pg_tabs : TabsOK 275 9 2 McLTC.G mclPGTbls := by
  refine ⟨rfl, fun j hj => ⟨?_, (pgF hj).2.1⟩⟩
  have hb := McLK.binds.2.2.2.2.1 j (by omega)
  rw [(pgF hj).1]
  interval_cases j
  · change tabT ((CFSG.Sporadic.Schreier.mclStrongArrs)[0]!) = _
    rw [hb]
  · change tabT ((CFSG.Sporadic.Schreier.mclStrongArrs)[1]!) = _
    rw [hb]

theorem pgi_tabs : TabsOK 275 9 2 McLTC.GI mclPGInvTbls :=
  TabsOK_inv pg_tabs fun j hj => ⟨(pgF hj).2.2.2, (pgF hj).2.2.1⟩

theorem slice_pe {n w k cnt : Nat} {G GI T PL POS SRT SRI : Nat → Nat}
    (h : penumSlK n w (mask w) (n * w) true G GI k cnt T PL POS SRT SRI 0 cnt = true) :
    ∀ i < cnt, penumPtK n w (mask w) (n * w) true G GI k cnt T PL POS SRT SRI i = true :=
  fun i hi => penumSl_spec h i (Nat.zero_le _) (by omega) hi

theorem slice_hs {cnt : Nat} {T HS HSI : Nat → Nat}
    (h : slK cnt (hsortPtK 275 9 (mask 9) cnt T HS HSI) 0 cnt = true) :
    ∀ i < cnt, hsortPtK 275 9 (mask 9) cnt T HS HSI i = true :=
  fun i hi => slK_spec h i (Nat.zero_le _) (by omega) hi

theorem slice_cl {cnt K : Nat} {T S CL : Nat → Nat}
    (h : slK (Nat.mul cnt K) (findPtK cnt T (prodQK 275 9 (mask 9) K T S) CL) 0 (Nat.mul cnt K) =
      true) :
    ∀ c < cnt * K, findPtK cnt T (prodQK 275 9 (mask 9) K T S) CL c = true :=
  fun c hc => slK_spec h c (Nat.zero_le _) (by rw [Nat.zero_add]; exact hc) hc

theorem recT : (penumSlK 275 9 (mask 9) (275 * 9) true McLTT.G McLTT.GI 5 McLTT.cnt McLTT.T McLTT.PL
      McLTT.POS McLTT.SRT McLTT.SRI 0 McLTT.cnt = true) ∧
    slK McLTT.cnt (hsortPtK 275 9 (mask 9) McLTT.cnt McLTT.T McLTT.HS McLTT.HSI) 0 McLTT.cnt =
      true ∧
    slK (Nat.mul McLTT.cnt 10) (findPtK McLTT.cnt McLTT.T
      (prodQK 275 9 (mask 9) 10 McLTT.T (bothK 5 McLTT.GI (fun j => McLThI (j + 6))))
      McLTClT) 0 (Nat.mul McLTT.cnt 10) = true := by
  have h := recT_ok
  simp only [Bool.and_eq_true, and_assoc] at h
  exact h

theorem recR : (penumSlK 275 9 (mask 9) (275 * 9) true McLTR.G McLTR.GI 5 McLTR.cnt McLTR.T McLTR.PL
      McLTR.POS McLTR.SRT McLTR.SRI 0 McLTR.cnt = true) ∧
    slK McLTR.cnt (hsortPtK 275 9 (mask 9) McLTR.cnt McLTR.T McLTR.HS McLTR.HSI) 0 McLTR.cnt =
      true ∧
    slK (Nat.mul McLTR.cnt 10) (findPtK McLTR.cnt McLTR.T
      (prodQK 275 9 (mask 9) 10 McLTR.T (bothK 5 McLTR.GI (fun j => McLTlI (j + 2))))
      McLTClR) 0 (Nat.mul McLTR.cnt 10) = true := by
  have h := recR_ok
  simp only [Bool.and_eq_true, and_assoc] at h
  exact h

theorem recA : (penumSlK 275 9 (mask 9) (275 * 9) true McLTA.G McLTA.GI 4 McLTA.cnt McLTA.T McLTA.PL
      McLTA.POS McLTA.SRT McLTA.SRI 0 McLTA.cnt = true) ∧
    slK McLTA.cnt (hsortPtK 275 9 (mask 9) McLTA.cnt McLTA.T McLTA.HS McLTA.HSI) 0 McLTA.cnt =
      true ∧
    slK (Nat.mul McLTA.cnt 8) (findPtK McLTA.cnt McLTA.T
      (prodQK 275 9 (mask 9) 8 McLTA.T (bothK 4 McLTA.GI (fun j => McLTlI (j + 7))))
      McLTClA) 0 (Nat.mul McLTA.cnt 8) = true := by
  have h := recA_ok
  simp only [Bool.and_eq_true, and_assoc] at h
  exact h

theorem eT : enumT = hRec 275 9 McLTT.cnt McLTT.T McLTT.PL ∧
    mulTreeOK 275 sylowThreeGens.toArray (hRec 275 9 McLTT.cnt McLTT.T McLTT.PL).1
      (hRec 275 9 McLTT.cnt McLTT.T McLTT.PL).2.1 (hRec 275 9 McLTT.cnt McLTT.T McLTT.PL).2.2 =
        true ∧
    hkeysDistinct 275 (hRec 275 9 McLTT.cnt McLTT.T McLTT.PL).1.toList = true :=
  mulH_sound hn (fun j hj => (tG hj).1) sylT_tabs hdT (slice_pe recT.1) (slice_hs recT.2.1)

theorem eR : enumR3 = hRec 275 9 McLTR.cnt McLTR.T McLTR.PL ∧
    mulTreeOK 275 rGens3 (hRec 275 9 McLTR.cnt McLTR.T McLTR.PL).1
      (hRec 275 9 McLTR.cnt McLTR.T McLTR.PL).2.1 (hRec 275 9 McLTR.cnt McLTR.T McLTR.PL).2.2 =
        true ∧
    hkeysDistinct 275 (hRec 275 9 McLTR.cnt McLTR.T McLTR.PL).1.toList = true :=
  mulH_sound hn (fun j hj => (rG hj).1) rG_tabs hdR (slice_pe recR.1) (slice_hs recR.2.1)

theorem eA : enumA3 = hRec 275 9 McLTA.cnt McLTA.T McLTA.PL ∧
    mulTreeOK 275 aGens3 (hRec 275 9 McLTA.cnt McLTA.T McLTA.PL).1
      (hRec 275 9 McLTA.cnt McLTA.T McLTA.PL).2.1 (hRec 275 9 McLTA.cnt McLTA.T McLTA.PL).2.2 =
        true ∧
    hkeysDistinct 275 (hRec 275 9 McLTA.cnt McLTA.T McLTA.PL).1.toList = true :=
  mulH_sound hn (fun j hj => (aG hj).1) aG_tabs hdA (slice_pe recA.1) (slice_hs recA.2.1)

theorem tT : ∀ i < McLTT.cnt, canonK 275 9 (mask 9) (275 * 9) (McLTT.T i) = true :=
  fun i hi => penumPt_canon (slice_pe recT.1 i hi)
theorem tR : ∀ i < McLTR.cnt, canonK 275 9 (mask 9) (275 * 9) (McLTR.T i) = true :=
  fun i hi => penumPt_canon (slice_pe recR.1 i hi)
theorem tA : ∀ i < McLTA.cnt, canonK 275 9 (mask 9) (275 * 9) (McLTA.T i) = true :=
  fun i hi => penumPt_canon (slice_pe recA.1 i hi)

theorem subEnum_of {k cnt cap ord : Nat} {G GI GJ T PL POS SRT SRI HS HSI CL : Nat → Nat}
    {sg : Array Table} (hG : ∀ j < k, G j = idP) (hg : TabsOK 275 9 k GI sg)
    (hgj : ∀ j < k, invEqK 275 9 (mask 9) (275 * 9) (GI j) (GJ j) = true ∧
      canonK 275 9 (mask 9) (275 * 9) (GJ j) = true)
    (hsift : ∀ j < k, sK (GI j) = true)
    (hh : penumHdK idP cnt cap T PL = true)
    (hp : ∀ i < cnt, penumPtK 275 9 (mask 9) (275 * 9) true G GI k cnt T PL POS SRT SRI i = true)
    (hs : ∀ i < cnt, hsortPtK 275 9 (mask 9) cnt T HS HSI i = true)
    (hcl : ∀ c < cnt * (k + k),
      findPtK cnt T (prodQK 275 9 (mask 9) (k + k) T (bothK k GI GJ)) CL c = true)
    (hm : cnt = ord) : subEnumOK 275 cap ord mclSift sg = true := by
  obtain ⟨e, ht, hd⟩ := mulH_sound hn hG hg hh hp hs
  have hT : ∀ i < cnt, canonK 275 9 (mask 9) (275 * 9) (T i) = true :=
    fun i hi => penumPt_canon (hp i hi)
  unfold subEnumOK
  simp only [Bool.and_eq_true]
  rw [e]
  refine ⟨⟨⟨⟨?_, ht⟩, closedOK_of hT (TabsOK_both hg hgj) hcl⟩, hd⟩, ?_⟩
  · rw [Array.all_eq_true]
    intro j hj
    have hj' : j < k := by rw [← hg.1]; exact hj
    have hx := (hg.2 j hj').1
    rw [getElem!_pos sg j hj] at hx
    rw [hx]
    obtain ⟨c1, c2⟩ := hgj j hj'
    have hc := (hg.2 j hj').2
    simp only [Bool.and_eq_true]
    refine ⟨⟨permOK_unpack hc c1, ?_⟩, ?_⟩
    · rw [sift_eq' hc]
      exact hsift j hj'
    · rw [invT_unpack (lt_of_canonK c2) c1]
      exact invOK_unpack hc c2 c1
  · rw [hRec_size, hm]
    exact beq_self_eq_true ord

theorem sifts : (∀ j < 5, sK (McLTh.F (j + 6)) = true) ∧ (∀ j < 5, sK (McLTl.F (j + 2)) = true) ∧
    (∀ j < 4, sK (McLTl.F (j + 7)) = true) ∧ sK (McLTl.F 0) = true ∧ sK (McLTl.F 1) = false ∧
    sK (pc (McLTl.F 1) (McLCT.F 0)) = true ∧ sK (McLTl.F 11) = true ∧ sK (McLTl.F 14) = false ∧
    sK (pc (McLTl.F 14) (McLCT.F 0)) = true := by
  have h := sifts_ok
  simp only [Bool.and_eq_true, and_assoc, Bool.not_eq_true'] at h
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h
  exact ⟨allN_spec a1, allN_spec a2, allN_spec a3, a4, a5, a6, a7, a8, a9⟩

theorem subT : subEnumOK 275 800 729 mclSift sylowThreeGens.toArray = true :=
  subEnum_of (fun j hj => (tG hj).1) sylT_tabs
    (fun j hj => by rw [(tG hj).2]; exact ⟨(thF (by omega)).2.2, (thF (by omega)).2.1⟩)
    (fun j hj => by rw [(tG hj).2]; exact sifts.1 j hj) hdT (slice_pe recT.1) (slice_hs recT.2.1)
    (slice_cl recT.2.2) cT

theorem subR : subEnumOK 275 300 243 mclSift rGens3 = true :=
  subEnum_of (fun j hj => (rG hj).1) rG_tabs
    (fun j hj => by rw [(rG hj).2]; exact ⟨(tlF (by omega)).2.2, (tlF (by omega)).2.1⟩)
    (fun j hj => by rw [(rG hj).2]; exact sifts.2.1 j hj) hdR (slice_pe recR.1) (slice_hs recR.2.1)
    (slice_cl recR.2.2) cR

theorem subA : subEnumOK 275 200 81 mclSift aGens3 = true :=
  subEnum_of (fun j hj => (aG hj).1) aG_tabs
    (fun j hj => by rw [(aG hj).2]; exact ⟨(tlF (by omega)).2.2, (tlF (by omega)).2.1⟩)
    (fun j hj => by rw [(aG hj).2]; exact sifts.2.2.1 j hj) hdA (slice_pe recA.1)
    (slice_hs recA.2.1) (slice_cl recA.2.2) cA

end CertificateChecks.KernelSpor.McLTK

end
