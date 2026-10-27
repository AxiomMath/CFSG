module

public import Certificates.Kernel.Sporadic.OddCore.Suz27215A
public import Certificates.Kernel.Sporadic.OddCore.Suz27215B0
public import Certificates.Kernel.Sporadic.OddCore.Suz27215B1
public import Certificates.Kernel.Sporadic.OddCore.Suz27215B2
public import Certificates.Kernel.Sporadic.OddCore.Suz27215B3
public import Certificates.Kernel.Sporadic.OddCore.Suz27215C0
public import Certificates.Kernel.Sporadic.OddCore.Suz27215C1
public import Certificates.Kernel.Sporadic.OddCore.Suz27215C2
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue
public import CFSG.Certificates.Kernel.CoverScanSound
public import CFSG.Certificates.Kernel.L34KSnd.Tab
public import CFSG.Certificates.Kernel.L34ScanSound
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Sporadic.SuzOddCore.InvArrays
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.HeAutKSound
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelSpor.S27215.aAll CertificateChecks.KernelSpor.S27215.aSl 7
#kon_join CertificateChecks.KernelSpor.S27215.bAll CertificateChecks.KernelSpor.S27215.bSl 56
#kon_join CertificateChecks.KernelSpor.S27215.cAll CertificateChecks.KernelSpor.S27215.cSl 40

namespace CertificateChecks.KernelSpor.S27215

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.BfsPin
open CFSG.KC.L34K CFSG.KC.L34KSnd CFSG.KC.CoverScan
open CFSG.PSL3Four.Native CFSG.EvenSporadicStandard.SuzOuter CertificateChecks.KernelSpor

theorem hsz : szOK 1782 11 = true := by decide

theorem cn_iff (p : Nat) : cn p = canonK 1782 11 (mask 11) (1782 * 11) p := rfl

theorem gen_parts : SOA.k = 5 ∧ ∀ j < 5, SOA.G j = SuzInvT3.F (20 + j) ∧ cn (SOA.G j) = true ∧
    cn (SOA.GI j) = true ∧ pc (SOA.G j) (SOA.GI j) = e := by
  obtain ⟨h1, h2⟩ := andT kGens
  refine ⟨Nat.eq_of_beq_eq_true h1, fun j hj => ?_⟩
  obtain ⟨a, h⟩ := andT (CFSG.KS.Raw.Orb.allN_iff.1 h2 j hj)
  obtain ⟨b, h⟩ := andT h
  obtain ⟨c, d⟩ := andT h
  exact ⟨Nat.eq_of_beq_eq_true a, b, c, Nat.eq_of_beq_eq_true d⟩

theorem gensC_size : gensC.size = 5 := by
  simp [gensC, CFSG.Sporadic.SuzOddCore.invInnerGenArrs, CFSG.Sporadic.SuzOddCore.invInnerGenCounts]

theorem map_toArray_get {α β : Type} [Inhabited β] (f : α → β) (l : List α) {j : Nat}
    (hj : j < l.length) (d : α) : (l.map f).toArray[j]! = f (l.getD j d) := by
  rw [getElem!_pos _ j (by simpa using hj)]
  simp [List.getElem?_eq_getElem hj]

theorem gensC_get {j : Nat} (hj : j < 5) : gensC[j]! = unpack 1782 11 (SOA.G j) := by
  unfold gensC CFSG.Sporadic.SuzOddCore.invInnerGenArrs
  rw [getElem!_pos _ j (by simpa [CFSG.Sporadic.SuzOddCore.invInnerGenCounts] using hj)]
  simp only [Array.getElem_ofFn]
  have e1 : CFSG.Sporadic.SuzOddCore.invInnerStart 3 + j = 20 + j := by
    simp [CFSG.Sporadic.SuzOddCore.invInnerStart, CFSG.Sporadic.SuzOddCore.invFullGenCounts,
      CFSG.Sporadic.SuzOddCore.invFullStrongCounts]
  rw [e1, SuzInv.run_eq3 (by omega), (gen_parts.2 j hj).1]

theorem ginv_parts : (∀ k < 5, (gensC.map (invTab 1782))[k]! = unpack 1782 11 (SOA.GI k)) ∧
    invsOK 1782 gensC (gensC.map (invTab 1782)) = true :=
  invsOK_of_pcomp gensC_size (fun k hk => gensC_get hk) fun k hk =>
    ⟨(gen_parts.2 k hk).2.1, (gen_parts.2 k hk).2.2.1, (gen_parts.2 k hk).2.2.2⟩

theorem gensOK_C : GensOK 1782 11 5 SOA.G gensC :=
  ⟨gensC_size, fun j hj => ⟨gensC_get hj, (gen_parts.2 j hj).2.1⟩⟩

theorem gensOK_CI : GensOK 1782 11 5 SOA.GI (gensC.map (invTab 1782)) :=
  ⟨by rw [Array.size_map, gensC_size], fun j hj => ⟨ginv_parts.1 j hj, (gen_parts.2 j hj).2.2.1⟩⟩

theorem letK_parts {j : Nat} (hj : j < 10) :
    letterTab j = unpack 1782 11 (letK j) ∧ cn (letK j) = true := by
  unfold letterTab letK
  by_cases h : j < 5
  · have hb : Nat.blt j 5 = true := Nat.blt_eq.mpr h
    rw [if_pos h, hb]
    exact ⟨gensC_get h, (gen_parts.2 j h).2.1⟩
  · have hb : Nat.blt j 5 = false := by
      cases e : Nat.blt j 5
      · rfl
      · exact absurd (Nat.blt_eq.mp e) h
    rw [if_neg h, hb]
    have h5 : j - 5 < 5 := by omega
    have e2 : Nat.sub j 5 = j - 5 := rfl
    rw [e2, ← map_get (invTab 1782) (by rw [gensC_size]; exact h5), ginv_parts.1 _ h5]
    exact ⟨rfl, (gen_parts.2 _ h5).2.2.1⟩

theorem wfK_cons (G : Nat → Nat) (l : Nat) (w : List Nat) :
    wfK G (l :: w) = pc (G l) (wfK G w) := by
  change strictN (wfK G w) (fun acc => pc (G l) acc) = _
  rw [CFSG.KS.PEnum.strictN_app']

theorem wordTab_eq {gs : Nat → Tab} {G : Nat → Nat} :
    ∀ w : List Nat, (∀ j ∈ w, gs j = unpack 1782 11 (G j) ∧ cn (G j) = true) →
      wordTab gs w = unpack 1782 11 (wfK G w) ∧ cn (wfK G w) = true
  | [], _ => ⟨idTab_unpack' hsz, canon_pidn hsz⟩
  | l :: w, h => by
    obtain ⟨ih1, ih2⟩ := wordTab_eq w fun j hj => h j (List.mem_cons_of_mem _ hj)
    obtain ⟨hl1, hl2⟩ := h l List.mem_cons_self
    have e1 : wordTab gs (l :: w) = comp 1782 (gs l) (wordTab gs w) := rfl
    rw [e1, ih1, hl1, wfK_cons, comp_unpack' hl2 ih2]
    exact ⟨rfl, canonK_pcomp hl2 ih2⟩

theorem p_parts : SOP.k = 3 ∧ ∀ j < 3, SOP.G j = wfK letK (wordsP.getD j []) ∧
    cn (SOP.G j) = true := by
  obtain ⟨h1, h2⟩ := andT kP
  refine ⟨Nat.eq_of_beq_eq_true h1, fun j hj => ?_⟩
  obtain ⟨a, b⟩ := andT (CFSG.KS.Raw.Orb.allN_iff.1 h2 j hj)
  exact ⟨Nat.eq_of_beq_eq_true a, b⟩

theorem gensP_size : gensP.size = 3 := by simp [gensP, wordsP]

theorem gensP_get {j : Nat} (hj : j < 3) : gensP[j]! = unpack 1782 11 (SOP.G j) := by
  have hl : ∀ k ∈ wordsP.getD j [], k < 10 := by
    interval_cases j <;> decide
  unfold gensP
  rw [map_toArray_get _ _ (by simpa [wordsP] using hj) [], (p_parts.2 j hj).1]
  exact (wordTab_eq _ fun k hk => letK_parts (hl k hk)).1

theorem gensOK_P : GensOK 1782 11 3 SOP.G gensP :=
  ⟨gensP_size, fun j hj => ⟨gensP_get hj, (p_parts.2 j hj).2⟩⟩

theorem repTab_eq {k : Nat} (hk : k < 3) :
    repTab k = unpack 1782 11 (wfK SOP.G (repWords.getD k [])) := by
  have hl : ∀ j ∈ repWords.getD k [], j < 3 := by
    interval_cases k <;> decide
  exact (wordTab_eq _ fun j hj => ⟨gensP_get (hl j hj), (p_parts.2 j (hl j hj)).2⟩).1

theorem hd_parts : (SOP.cnt = 256 ∧ penumHdK e SOP.cnt 256 SOP.T SOP.PL = true) ∧
    (SOA.cnt = 315 ∧ penumHdK (wfK SOP.G (repWords.getD 0 [])) SOA.cnt 315 SOA.T SOA.PL = true) ∧
    (SOB.cnt = 2520 ∧
      penumHdK (wfK SOP.G (repWords.getD 1 [])) SOB.cnt 2520 SOB.T SOB.PL = true) ∧
    (SOC.cnt = 1800 ∧
      penumHdK (wfK SOP.G (repWords.getD 2 [])) SOC.cnt 1800 SOC.T SOC.PL = true) ∧
    (SOE.cnt = 128 ∧ SOE.k = 4 ∧ penumHdK e SOE.cnt 128 SOE.T SOE.PL = true) ∧
    ∀ j < 4, cn (SOE.G j) = true ∧
      SOE.G j = pc (SOA.T (pairsE.getD j (0, 0)).1) (SOA.T (pairsE.getD j (0, 0)).2) := by
  obtain ⟨hP, h⟩ := andT kHd
  obtain ⟨hA, h⟩ := andT h
  obtain ⟨hB, h⟩ := andT h
  obtain ⟨hC, h⟩ := andT h
  obtain ⟨hE, hEG⟩ := andT h
  obtain ⟨p1, p2⟩ := andT hP
  obtain ⟨a1, a2⟩ := andT hA
  obtain ⟨b1, b2⟩ := andT hB
  obtain ⟨c1, c2⟩ := andT hC
  obtain ⟨e1, h⟩ := andT hE
  obtain ⟨e2, e3⟩ := andT h
  refine ⟨⟨Nat.eq_of_beq_eq_true p1, p2⟩, ⟨Nat.eq_of_beq_eq_true a1, a2⟩,
    ⟨Nat.eq_of_beq_eq_true b1, b2⟩, ⟨Nat.eq_of_beq_eq_true c1, c2⟩,
    ⟨Nat.eq_of_beq_eq_true e1, Nat.eq_of_beq_eq_true e2, e3⟩, fun j hj => ?_⟩
  obtain ⟨g1, g2⟩ := andT (CFSG.KS.Raw.Orb.allN_iff.1 hEG j hj)
  exact ⟨g1, Nat.eq_of_beq_eq_true g2⟩

theorem share_parts : SOB.k = 5 ∧ SOC.k = 5 ∧ ∀ j < 5, SOB.G j = SOA.G j ∧ SOB.GI j = SOA.GI j ∧
    SOC.G j = SOA.G j ∧ SOC.GI j = SOA.GI j := by
  obtain ⟨h1, h2⟩ := andT kShare
  obtain ⟨b, c⟩ := andT h1
  refine ⟨Nat.eq_of_beq_eq_true b, Nat.eq_of_beq_eq_true c, fun j hj => ?_⟩
  obtain ⟨x1, h⟩ := andT (CFSG.KS.Raw.Orb.allN_iff.1 h2 j hj)
  obtain ⟨x2, h⟩ := andT h
  obtain ⟨x3, x4⟩ := andT h
  exact ⟨Nat.eq_of_beq_eq_true x1, Nat.eq_of_beq_eq_true x2, Nat.eq_of_beq_eq_true x3,
    Nat.eq_of_beq_eq_true x4⟩

theorem slices_spec {conj : Bool} {G GI T PL POS SRT SRI : Nat → Nat} {k cnt K : Nat}
    (hc : cnt = 45 * K)
    (h : ∀ s < K, penumSlK 1782 11 (mask 11) (1782 * 11) conj G GI k cnt T PL POS SRT SRI
      (Nat.mul s 45) 45 = true) :
    ∀ i < cnt, penumPtK 1782 11 (mask 11) (1782 * 11) conj G GI k cnt T PL POS SRT SRI i =
      true := by
  intro i hi
  refine penumSl_spec (h (i / 45) (by omega)) i ?_ ?_ hi
  · change i / 45 * 45 ≤ i
    omega
  · change i < i / 45 * 45 + 45
    omega

theorem ptA : ∀ i < SOA.cnt, penumPtK 1782 11 (mask 11) (1782 * 11) true SOA.G SOA.GI 5 SOA.cnt
    SOA.T SOA.PL SOA.POS SOA.SRT SOA.SRI i = true :=
  slices_spec (K := 7) (by rw [hd_parts.2.1.1]) fun s hs => aAll s hs

theorem ptB : ∀ i < SOB.cnt, penumPtK 1782 11 (mask 11) (1782 * 11) true SOB.G SOB.GI 5 SOB.cnt
    SOB.T SOB.PL SOB.POS SOB.SRT SOB.SRI i = true :=
  slices_spec (K := 56) (by rw [hd_parts.2.2.1.1]) fun s hs => bAll s hs

theorem ptC : ∀ i < SOC.cnt, penumPtK 1782 11 (mask 11) (1782 * 11) true SOC.G SOC.GI 5 SOC.cnt
    SOC.T SOC.PL SOC.POS SOC.SRT SOC.SRI i = true :=
  slices_spec (K := 40) (by rw [hd_parts.2.2.2.1.1]) fun s hs => cAll s hs

theorem ptP : ∀ i < SOP.cnt, penumPtK 1782 11 (mask 11) (1782 * 11) false SOP.G SOP.GI 3 SOP.cnt
    SOP.T SOP.PL SOP.POS SOP.SRT SOP.SRI i = true := fun i hi =>
  penumSl_spec pSl0 i (Nat.zero_le _) (by rw [hd_parts.1.1] at hi; exact hi) hi

theorem ptE : ∀ i < SOE.cnt, penumPtK 1782 11 (mask 11) (1782 * 11) false SOE.G SOE.GI 4 SOE.cnt
    SOE.T SOE.PL SOE.POS SOE.SRT SOE.SRI i = true := fun i hi =>
  penumSl_spec eSl0 i (Nat.zero_le _) (by rw [hd_parts.2.2.2.2.1.1] at hi; exact hi) hi

theorem gensOK_B : GensOK 1782 11 5 SOB.G gensC :=
  ⟨gensC_size, fun j hj => by rw [(share_parts.2.2 j hj).1]; exact gensOK_C.2 j hj⟩

theorem gensOK_BI : GensOK 1782 11 5 SOB.GI (gensC.map (invTab 1782)) :=
  ⟨gensOK_CI.1, fun j hj => by rw [(share_parts.2.2 j hj).2.1]; exact gensOK_CI.2 j hj⟩

theorem gensOK_Cc : GensOK 1782 11 5 SOC.G gensC :=
  ⟨gensC_size, fun j hj => by rw [(share_parts.2.2 j hj).2.2.1]; exact gensOK_C.2 j hj⟩

theorem gensOK_CcI : GensOK 1782 11 5 SOC.GI (gensC.map (invTab 1782)) :=
  ⟨gensOK_CI.1, fun j hj => by rw [(share_parts.2.2 j hj).2.2.2]; exact gensOK_CI.2 j hj⟩

theorem eP : enumBFS 1782 gensP 256 = penumRec 1782 11 SOP.cnt SOP.T SOP.PL ∧
    enumOK 1782 gensP (penumRec 1782 11 SOP.cnt SOP.T SOP.PL) = true :=
  penumK_left_sound (cap := 256) hsz gensOK_P hd_parts.1.2 ptP

theorem eA : orbitBFS 1782 gensC (gensC.map (invTab 1782)) (repTab 0) 315 =
      penumRec 1782 11 SOA.cnt SOA.T SOA.PL ∧
    treeOK (conjStep 1782 gensC (gensC.map (invTab 1782))) gensC.size (repTab 0)
      (penumRec 1782 11 SOA.cnt SOA.T SOA.PL) = true :=
  penumK_conj_sound (cap := 315) hsz gensOK_C gensOK_CI (repTab_eq (k := 0) (by decide))
    hd_parts.2.1.2 ptA

theorem eB : orbitBFS 1782 gensC (gensC.map (invTab 1782)) (repTab 1) 2520 =
      penumRec 1782 11 SOB.cnt SOB.T SOB.PL ∧
    treeOK (conjStep 1782 gensC (gensC.map (invTab 1782))) gensC.size (repTab 1)
      (penumRec 1782 11 SOB.cnt SOB.T SOB.PL) = true :=
  penumK_conj_sound (cap := 2520) hsz gensOK_B gensOK_BI (repTab_eq (k := 1) (by decide))
    hd_parts.2.2.1.2 ptB

theorem eC : orbitBFS 1782 gensC (gensC.map (invTab 1782)) (repTab 2) 1800 =
      penumRec 1782 11 SOC.cnt SOC.T SOC.PL ∧
    treeOK (conjStep 1782 gensC (gensC.map (invTab 1782))) gensC.size (repTab 2)
      (penumRec 1782 11 SOC.cnt SOC.T SOC.PL) = true :=
  penumK_conj_sound (cap := 1800) hsz gensOK_Cc gensOK_CcI (repTab_eq (k := 2) (by decide))
    hd_parts.2.2.2.1.2 ptC

theorem penumRec_tabs (n w cnt : Nat) (T PL : Nat → Nat) :
    (penumRec n w cnt T PL).tabs = pts n w cnt T :=
  rfl

theorem gensE_size (IA : Enum) : (gensE IA).size = 4 := by simp [gensE, pairsE]

theorem gensOK_E : GensOK 1782 11 4 SOE.G (gensE (penumRec 1782 11 SOA.cnt SOA.T SOA.PL)) := by
  refine ⟨gensE_size _, fun j hj => ⟨?_, (hd_parts.2.2.2.2.2 j hj).1⟩⟩
  have hp : ∀ j < 4, (pairsE.getD j (0, 0)).1 < 315 ∧ (pairsE.getD j (0, 0)).2 < 315 := by
    decide
  have hc : SOA.cnt = 315 := hd_parts.2.1.1
  obtain ⟨h1, h2⟩ := hp j hj
  have ca := penumPt_canon (ptA _ (by rw [hc]; exact h1))
  have cb := penumPt_canon (ptA _ (by rw [hc]; exact h2))
  unfold gensE
  rw [map_toArray_get _ _ (by simpa [pairsE] using hj) (0, 0), (hd_parts.2.2.2.2.2 j hj).2]
  simp only [penumRec_tabs]
  rw [CFSG.KC.L34Scan.pts_get' (by rw [hc]; exact h1), CFSG.KC.L34Scan.pts_get' (by rw [hc]; exact h2)]
  exact comp_unpack' ca cb

theorem eE : enumBFS 1782 (gensE (penumRec 1782 11 SOA.cnt SOA.T SOA.PL)) 128 =
      penumRec 1782 11 SOE.cnt SOE.T SOE.PL ∧
    enumOK 1782 (gensE (penumRec 1782 11 SOA.cnt SOA.T SOA.PL))
      (penumRec 1782 11 SOE.cnt SOE.T SOE.PL) = true :=
  penumK_left_sound (cap := 128) hsz gensOK_E hd_parts.2.2.2.2.1.2.2 ptE

theorem canonP : ∀ i < SOP.cnt, canonK 1782 11 (mask 11) (1782 * 11) (SOP.T i) = true :=
  fun i hi => penumPt_canon (ptP i hi)

theorem cover : coverOK 1782 (pts 1782 11 SOP.cnt SOP.T)
    #[pts 1782 11 SOA.cnt SOA.T, pts 1782 11 SOB.cnt SOB.T, pts 1782 11 SOC.cnt SOC.T] = true := by
  refine coverOK_of (M := 3) (ON := ON) (OT := OT) (W := fun i => r32 SOW i) ⟨rfl, fun o ho => ?_⟩
    canonP fun i hi => ?_
  · interval_cases o <;> rfl
  · have h := covSl0
    unfold covSl at h
    rw [hd_parts.1.1] at hi
    exact CFSG.KS.Raw.Orb.allN_iff.1 h i hi

theorem check27215 : suzOuterCheck = true := by
  have hsizes : allBelow 5 (fun j => gensC[j]!.size == 1782) = true :=
    CFSG.KS.BfsReplay.allBelow_iff.2 fun j hj => by rw [gensC_get hj, size_unpack]; rfl
  simp only [suzOuterCheck]
  rw [eA.1, eB.1, eC.1, eP.1, eE.1]
  unfold suzOuterCheckWith orbitOK
  rw [eP.2, eE.2, eA.2, eB.2, eC.2, ginv_parts.2, hsizes]
  simp only [penumRec_tabs, size_pts]
  rw [cover, hd_parts.1.1, hd_parts.2.1.1, hd_parts.2.2.1.1, hd_parts.2.2.2.1.1,
    hd_parts.2.2.2.2.1.1, gensC_size]
  rfl

end CertificateChecks.KernelSpor.S27215

end
