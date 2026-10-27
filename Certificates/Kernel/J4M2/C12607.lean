module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4GamData
public meta import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4GamData
public import Certificates.Kernel.J4M2.C12607Checks
public import Certificates.Kernel.J4M2.C12608
public import Certificates.Kernel.SporSch.J4S11.Facts
public import Certificates.Kernel.SporSch.J4S.RealK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Gam

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KS.SporSch.J4B CFSG.KS.SporSch.J4E CFSG.Sporadic.J4Schreier
  CertificateChecks.KernelSporSch.J4E7 CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

theorem wfN_of {X : Array Nat} (h : rowsOK X = true) : WfN X := by
  unfold rowsOK at h
  rw [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  refine ⟨h.1, fun i hi => ?_⟩
  have hi' : i < X.size := by rw [h.1]; exact hi
  rw [getElem!_pos X i hi']
  exact Nat.le_of_ble_eq_true (h.2 _ (Array.getElem_mem_toList hi'))

theorem rows : rowsOK gamZ0 = true ∧ rowsOK gamAFwd = true ∧ rowsOK gamABwd = true ∧
    rowsOK gamBFwd = true ∧ rowsOK gamBBwd = true ∧ rowsOK gamZFwd = true ∧
    rowsOK gamZBwd = true := by
  have h := rows_ok
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem eqO {X Y : Array Nat} {x y : Nat} (hX : WfN X ∧ encN X = x) (hY : WfN Y ∧ encN Y = y)
    (h : Nat.beq x y = true) : O.eq X Y = true := by
  have e : X = Y := enc_inj hX.1 hY.1 (by rw [hX.2, hY.2]; exact Nat.eq_of_beq_eq_true h)
  change (X == Y) = true
  rw [e]
  exact beq_self_eq_true _

theorem pZ0 : PairOK gamZ0P Z0P.1 Z0P.2 := ⟨⟨wfN_of rows.1, rfl⟩, ⟨wfN_of rows.1, rfl⟩⟩

theorem pAn : PairOK An A A :=
  ⟨CertificateChecks.KernelSporSch.J4Real.hA, CertificateChecks.KernelSporSch.J4Real.hA⟩

theorem pBn : PairOK Bn B Bi :=
  ⟨CertificateChecks.KernelSporSch.J4Real.hB, CertificateChecks.KernelSporSch.J4Real.hB3⟩

theorem pH : PairOK gamHP HP.1 HP.2 := wordP_ok' hK pAn pBn gamWord (by decide)

theorem pJ : PairOK gamJP JP.1 JP.2 := powP_ok hK hH2 20

theorem pG : PairOK gamGP GP.1 GP.2 :=
  mulP_ok hK (powP_ok hK (mulP_ok hK pZ0 (mulP_ok hK (mulP_ok hK pH pJ) (invP_ok pH))) 6) pH

theorem pCj {P : Pair} {p : Nat × Nat} (hP : PairOK P p.1 p.2) :
    PairOK (gamConjP P) (cjP p).1 (cjP p).2 :=
  mulP_ok hK (mulP_ok hK pG hP) (invP_ok pG)

theorem pC1 : PairOK gamC1P C1P.1 C1P.2 := mulP_ok hK (powP_ok hK hQY 10) hH1

theorem pA : PairOK gamAP GA.1 GA.2 := ⟨⟨wfN_of rows.2.1, rfl⟩, ⟨wfN_of rows.2.2.1, rfl⟩⟩

theorem pB : PairOK gamBP GB.1 GB.2 :=
  ⟨⟨wfN_of rows.2.2.2.1, rfl⟩, ⟨wfN_of rows.2.2.2.2.1, rfl⟩⟩

theorem pZ : PairOK gamZP GZ.1 GZ.2 :=
  ⟨⟨wfN_of rows.2.2.2.2.2.1, rfl⟩, ⟨wfN_of rows.2.2.2.2.2.2, rfl⟩⟩

theorem eqP_and {p q : Nat × Nat} (h : eqP p q = true) :
    Nat.beq p.1 q.1 = true ∧ Nat.beq p.2 q.2 = true :=
  andB_iff.1 h

theorem gamZ0OK_ok : gamZ0OK = true := by
  have hw := wfN_of rows.1
  have hn := CertificateChecks.KernelJ4M2.natRows_enc gamZ0 rows.1
  have e1 : CertificateChecks.KernelJ4M2.encN gamZ0 = ZM := by
    have e : CertificateChecks.KernelJ4M2.encN gamZ0 = pk gamZ0 := by
      unfold CertificateChecks.KernelJ4M2.encN pk
      congr 1
      funext i acc
      simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
    rw [e]
    exact Nat.eq_of_beq_eq_true z0_chk
  have hz : CFSG.Quasithin.J4M2.zM = gamZ0.map natV2 :=
    CFSG.Sporadic.J4.eqRows_iff.1 (by
      rw [eqRows_eq CertificateChecks.KernelJ4M2.zM_enc.1 hn.1, CertificateChecks.KernelJ4M2.zM_enc.2,
        hn.2, e1]
      exact Nat.beq_refl _)
  unfold gamZ0OK
  rw [hz, Array.size_map, hw.1]
  simp only [beq_self_eq_true, Bool.true_and, List.all_eq_true]
  intro i hi
  rw [CertificateChecks.KernelJ4M2.get!_map natV2 gamZ0 (by rw [hw.1]; exact List.mem_range.1 hi)]
  exact CFSG.Sporadic.J4.Native.V2.beq_iff.2 rfl

theorem gamOK_ok : gamOK = true := by
  have wZ := wfN_of rows.1
  have ca := eqP_and ca_chk
  have cb := eqP_and cb_chk
  have cz := eqP_and cz_chk
  unfold gamOK
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨gamZ0OK_ok, eq_one_sound hK wZ wZ zz_chk⟩, eqO (pCj pJ).1 ⟨wZ, rfl⟩ j_chk⟩,
    eqO (mulP_ok hK pC1 pJ).1 (mulP_ok hK pJ pC1).1 c_chk⟩, eqO (pCj pC1).1 pA.1 ca.1⟩,
    eqO (pCj pC1).2 pA.2 ca.2⟩, eqO (pCj hH2).1 pB.1 cb.1⟩, eqO (pCj hH2).2 pB.2 cb.2⟩,
    eqO (pCj hQZ).1 pZ.1 cz.1⟩, eqO (pCj hQZ).2 pZ.2 cz.2⟩

open CFSG.AGLEmbeddingD2.Wilson.NormalizerAction in
theorem c12607 : gamOK = true := gamOK_ok

end CertificateChecks.KernelJ4Gam

end
