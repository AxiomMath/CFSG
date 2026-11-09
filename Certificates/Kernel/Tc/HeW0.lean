module

public import Certificates.Kernel.Tc.HeW1
import CFSG.Certificates.Kernel.Common.Harness
meta import Certificates.Kernel.Tc.HeSrc

namespace CertificateChecks.KernelTc.He

open CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He

meta def arrsQ : Array (Array Nat) :=
  #[heThreeArr ((((heTcWs.getD 2 []).drop 87).take 58).take 20),
    heThreeArr (((((heTcWs.getD 2 []).drop 87).take 58).drop 20).take 19),
    heThreeArr ((((heTcWs.getD 2 []).drop 87).take 58).drop 39),
    heThreeArr (((heTcWs.getD 0 []).drop 174).take 16), heThreeArr (heTcWs.getD 14 []),
    heThreeArr (((heTcWs.getD 2 []).drop 87).take 58)]

end CertificateChecks.KernelTc.He

public section

#kmisc_packarrs CertificateChecks.KernelTc.He.HWQ CertificateChecks.KernelTc.He.arrsQ 14

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTc.He

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Mathieu CFSG.KC.HeLoc
  CertificateChecks.KernelLC.HeFix

@[expose] def wY : List Int := ((heTcWs.getD 2 []).drop 87).take 58

@[expose] def wZ : List Int := ((heTcWs.getD 0 []).drop 174).take 16

@[expose] def qcs : List (List Int) :=
  [wY.take 20, (wY.drop 20).take 19, wY.drop 39, wZ, heTcWs.getD 14 []]

@[expose] noncomputable def qOK (k : Nat) : Bool := Nat.beq (wordC (qcs.getD k [])) (HWQ k)

#kc_each CertificateChecks.KernelTc.He.qOK 0 5

theorem cQc : bAnd(canonK 8330 14 (mask 14) (8330 * 14) (HWQ 2),
    bAnd(canonK 8330 14 (mask 14) (8330 * 14) (HWQ 4),
      canonK 8330 14 (mask 14) (8330 * 14) (HWQ 5))) = true := by
  quickRfl

theorem kY : Nat.beq (pcompC 8330 14 (mask 14) (HWQ 0) (pcompC 8330 14 (mask 14) (HWQ 1) (HWQ 2)))
    (HWQ 5) = true := by
  quickRfl

theorem kQ : bAnd(Nat.beq (pcompC 8330 14 (mask 14) (HWX 1) (pcompC 8330 14 (mask 14) (HWQ 5)
      (pcompC 8330 14 (mask 14) (HWQ 5) (pcompC 8330 14 (mask 14) (HWQ 3) (HT 7))))) (HT 0),
    bAnd(Nat.beq (pcompC 8330 14 (mask 14) (HT 6) (pcompC 8330 14 (mask 14) (HT 7)
      (pcompC 8330 14 (mask 14) (HWX 1) (pcompC 8330 14 (mask 14) (HT 6) (HWQ 4))))) (HT 1),
      Nat.beq (pcompC 8330 14 (mask 14) (HWQ 4) (pcompC 8330 14 (mask 14) (HWX 2)
        (pcompC 8330 14 (mask 14) (HWQ 5) (pcompC 8330 14 (mask 14) (HWX 0) (HWX 1))))) (HT 2)))
    = true := by
  quickRfl

theorem kQ' : bAnd(Nat.beq (pcompC 8330 14 (mask 14) (HT 9) (pcompC 8330 14 (mask 14) (HWQ 4)
      (pcompC 8330 14 (mask 14) (HWQ 5) (HWQ 5)))) (HT 3),
    bAnd(Nat.beq (pcompC 8330 14 (mask 14) (HT 10) (pcompC 8330 14 (mask 14) (HWX 0)
      (pcompC 8330 14 (mask 14) (HWX 0) (HT 6)))) (HT 4),
      Nat.beq (pcompC 8330 14 (mask 14) (HT 7) (pcompC 8330 14 (mask 14) (HWX 0)
        (pcompC 8330 14 (mask 14) (HWX 1) (pcompC 8330 14 (mask 14) (HT 6)
          (pcompC 8330 14 (mask 14) (HWQ 5) (HWX 0)))))) (HT 5))) = true := by
  quickRfl

theorem kI0 : allN 8 (fun j => bAnd(szOK 8330 14, bAnd(lettersK 2 (heTcWs.getD j []),
    invEqK 8330 14 (mask 14) (8330 * 14) (HT j) (HTI j)))) = true := by
  quickRfl

theorem eQ (k : Nat) (h : qOK k = true) :
    wordK 8330 14 (mask 14) (pidn 8330 14) L2 L2I (qcs.getD k []) = HWQ k := by
  unfold qOK at h
  rw [wordC_eq] at h
  exact Nat.eq_of_beq_eq_true h

theorem cQd : canonK 8330 14 (mask 14) (8330 * 14) (HWQ 2) = true ∧
    canonK 8330 14 (mask 14) (8330 * 14) (HWQ 4) = true ∧
    canonK 8330 14 (mask 14) (8330 * 14) (HWQ 5) = true := by
  have hc := cQc
  simp only [bAnd_iff] at hc
  exact hc

theorem eY : wordK 8330 14 (mask 14) (pidn 8330 14) L2 L2I wY = HWQ 5 := by
  have e : wY = qcs.getD 0 [] ++ (qcs.getD 1 [] ++ qcs.getD 2 []) := rfl
  have h1 := appK (eQ 1 qOK1) (eQ 2 qOK2) cQd.1
  have hy := Nat.eq_of_beq_eq_true kY
  rw [CFSG.KS.PK.pcompC_eq, CFSG.KS.PK.pcompC_eq] at hy
  rw [e, (appK (eQ 0 qOK0) h1.1 h1.2).1, hy]

theorem eZ : wordK 8330 14 (mask 14) (pidn 8330 14) L2 L2I wZ = HWQ 3 := eQ 3 qOK3

theorem eA0 : wordK 8330 14 (mask 14) (pidn 8330 14) L2 L2I (heTcWs.getD 14 []) = HWQ 4 :=
  eQ 4 qOK4

theorem eQP : pcomp 8330 14 (mask 14) (HWX 1) (pcomp 8330 14 (mask 14) (HWQ 5)
      (pcomp 8330 14 (mask 14) (HWQ 5) (pcomp 8330 14 (mask 14) (HWQ 3) (HT 7)))) = HT 0 ∧
    pcomp 8330 14 (mask 14) (HT 6) (pcomp 8330 14 (mask 14) (HT 7)
      (pcomp 8330 14 (mask 14) (HWX 1) (pcomp 8330 14 (mask 14) (HT 6) (HWQ 4)))) = HT 1 ∧
    pcomp 8330 14 (mask 14) (HWQ 4) (pcomp 8330 14 (mask 14) (HWX 2)
      (pcomp 8330 14 (mask 14) (HWQ 5) (pcomp 8330 14 (mask 14) (HWX 0) (HWX 1)))) = HT 2 ∧
    pcomp 8330 14 (mask 14) (HT 9) (pcomp 8330 14 (mask 14) (HWQ 4)
      (pcomp 8330 14 (mask 14) (HWQ 5) (HWQ 5))) = HT 3 ∧
    pcomp 8330 14 (mask 14) (HT 10) (pcomp 8330 14 (mask 14) (HWX 0)
      (pcomp 8330 14 (mask 14) (HWX 0) (HT 6))) = HT 4 ∧
    pcomp 8330 14 (mask 14) (HT 7) (pcomp 8330 14 (mask 14) (HWX 0)
      (pcomp 8330 14 (mask 14) (HWX 1) (pcomp 8330 14 (mask 14) (HT 6)
        (pcomp 8330 14 (mask 14) (HWQ 5) (HWX 0))))) = HT 5 := by
  have hc := kQ
  have hc' := kQ'
  simp only [bAnd_iff, CFSG.KS.PK.pcompC_eq] at hc hc'
  obtain ⟨h0, h1, h2⟩ := hc
  obtain ⟨h3, h4, h5⟩ := hc'
  exact ⟨Nat.eq_of_beq_eq_true h0, Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2,
    Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5⟩

theorem wOK0 : wOK 0 = true := by
  have e : heTcWs.getD 0 [] = wX.getD 1 [] ++ (wY ++ (wY ++ (wZ ++ heTcWs.getD 7 []))) := rfl
  refine wOK_of ?_ (allN_spec kI0 0 (by decide))
  have h3 := appK eZ eR2 cT.2.1
  have h2 := appK eY h3.1 h3.2
  have h1 := appK eY h2.1 h2.2
  rw [e, (appK eX1 h1.1 h1.2).1, eQP.1]

theorem wOK1 : wOK 1 = true := by
  have e : heTcWs.getD 1 [] = heTcWs.getD 6 [] ++ (heTcWs.getD 7 [] ++ (wX.getD 1 [] ++
      (heTcWs.getD 6 [] ++ heTcWs.getD 14 []))) := rfl
  refine wOK_of ?_ (allN_spec kI0 1 (by decide))
  have h3 := appK eR1 eA0 cQd.2.1
  have h2 := appK eX1 h3.1 h3.2
  have h1 := appK eR2 h2.1 h2.2
  rw [e, (appK eR1 h1.1 h1.2).1, eQP.2.1]

theorem wOK2 : wOK 2 = true := by
  have e : heTcWs.getD 2 [] = heTcWs.getD 14 [] ++ (wX.getD 2 [] ++ (wY ++
      (wX.getD 0 [] ++ wX.getD 1 []))) := rfl
  refine wOK_of ?_ (allN_spec kI0 2 (by decide))
  have h3 := appK eX0 eX1 cT.2.2.2.2.1
  have h2 := appK eY h3.1 h3.2
  have h1 := appK eX2 h2.1 h2.2
  rw [e, (appK eA0 h1.1 h1.2).1, eQP.2.2.1]

theorem wOK3 : wOK 3 = true := by
  have e : heTcWs.getD 3 [] = heTcWs.getD 9 [] ++ (heTcWs.getD 14 [] ++ (wY ++ wY)) := rfl
  refine wOK_of ?_ (allN_spec kI0 3 (by decide))
  have h2 := appK eY eY cQd.2.2
  have h1 := appK eA0 h2.1 h2.2
  rw [e, (appK eW9 h1.1 h1.2).1, eQP.2.2.2.1]

theorem wOK4 : wOK 4 = true := by
  have e : heTcWs.getD 4 [] = heTcWs.getD 10 [] ++ (wX.getD 0 [] ++ (wX.getD 0 [] ++
      heTcWs.getD 6 [])) := rfl
  refine wOK_of ?_ (allN_spec kI0 4 (by decide))
  have h2 := appK eX0 eR1 cT.1
  have h1 := appK eX0 h2.1 h2.2
  rw [e, (appK eW10 h1.1 h1.2).1, eQP.2.2.2.2.1]

theorem wOK5 : wOK 5 = true := by
  have e : heTcWs.getD 5 [] = heTcWs.getD 7 [] ++ (wX.getD 0 [] ++ (wX.getD 1 [] ++
      (heTcWs.getD 6 [] ++ (wY ++ wX.getD 0 [])))) := rfl
  refine wOK_of ?_ (allN_spec kI0 5 (by decide))
  have h4 := appK eY eX0 cT.2.2.2.1
  have h3 := appK eR1 h4.1 h4.2
  have h2 := appK eX1 h3.1 h3.2
  have h1 := appK eX0 h2.1 h2.2
  rw [e, (appK eR2 h1.1 h1.2).1, eQP.2.2.2.2.2]

theorem wOK6 : wOK 6 = true := wOK_of eR1 (allN_spec kI0 6 (by decide))

theorem wOK7 : wOK 7 = true := wOK_of eR2 (allN_spec kI0 7 (by decide))

end CertificateChecks.KernelTc.He

end
