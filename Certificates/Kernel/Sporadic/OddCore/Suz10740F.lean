module

public import Certificates.Kernel.Sporadic.OddCore.Suz10740
public import Certificates.Kernel.Sporadic.OddCore.Suz26990F
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.S26990

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.L34KSnd
open CertificateChecks.KernelSpor.OddCore CFSG.EvenSporadicStandard.Solomon78
open CFSG.EvenSporadicStandard.Induction
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzOddCore CFSG.PSL3Four.Native
open CFSG.Certificates.Native
open CFSG.KLie.CT (andB orB notB)

theorem lettersN : lettersOK 2 suzWordN = true ∧ lettersOK 2 suzWordD = true := by
  constructor <;> decide +kernel

theorem check10740 : suzE0Check = true := by
  have h := k10740
  rw [strictB_app, strictB_app, strictB_app, strictB_app, strictB_app, strictB_app,
    strictB_app] at h
  unfold e0K at h
  obtain ⟨hlN, hok⟩ := andB_iff.1 k10740N
  obtain ⟨cN, cNi, pN⟩ := ok_spec hok
  obtain ⟨-, -, -, -, -, pD, -, -, -, cT⟩ := all_parts
  have cS := pD.1
  have cA := inv_parts.1.1
  have cB := inv_parts.2.1
  have hN : suzArrN = unpack 1782 11 (W3 suzWordN) := by
    unfold suzArrN
    exact w3_eq hlN
  have hI := inv_u hN pN
  have hNi : suzArrNi = unpack 1782 11 (pinv (W3 suzWordN)) := by
    unfold suzArrNi
    exact hI.1
  have hInv : isInvA 1782 suzArrN suzArrNi = true := by
    unfold suzArrNi
    exact hI.2
  have cE1 := cpc (cpc cN cT) cNi
  have hE1 : suzArrE1 = unpack 1782 11 (pc (pc (W3 suzWordN) (SuzTP 0)) (pinv (W3 suzWordN))) := by
    unfold suzArrE1
    rw [hN, hNi, t0_eq, compA_u cN cT, compA_u (cpc cN cT) cNi]
  have hS : suzArrSigma = unpack 1782 11 (W3 suzWordD) := by
    unfold suzArrSigma
    exact w3_eq letters.2.2.2.1
  unfold suzE0Check suzCommutes
  rw [lettersN.1, lettersN.2, hInv, hN, hNi, hE1, hS, pa_eq, pb_eq, t0_eq, hidA]
  generalize pc (pc (W3 suzWordN) (SuzTP 0)) (pinv (W3 suzWordN)) = e1 at cE1 h ⊢
  generalize pinv (W3 suzWordN) = ni at cNi h ⊢
  generalize W3 suzWordN = n at cN h ⊢
  generalize SuzTP 0 = t at cT h ⊢
  generalize W3 suzWordD = s at cS h ⊢
  generalize PA = a at cA h ⊢
  generalize PB = b at cB h ⊢
  have ce := cE
  generalize e = z at ce h ⊢
  obtain ⟨h1, h⟩ := andB_iff.1 h
  obtain ⟨h2, h⟩ := andB_iff.1 h
  obtain ⟨h3, h⟩ := andB_iff.1 h
  obtain ⟨h4, h⟩ := andB_iff.1 h
  obtain ⟨h5, h⟩ := andB_iff.1 h
  obtain ⟨h6, h⟩ := andB_iff.1 h
  obtain ⟨h7, h⟩ := andB_iff.1 h
  obtain ⟨h8, h⟩ := andB_iff.1 h
  obtain ⟨h9, h⟩ := andB_iff.1 h
  obtain ⟨h10, h⟩ := andB_iff.1 h
  obtain ⟨h11, h12⟩ := andB_iff.1 h
  rw [notB_iff] at h2 h7 h12
  rw [compA_u cN cN, compA_u cN (cpc cN cN), eqA_u (cpc cN (cpc cN cN)) ce, eqA_u cN ce,
    compA_u cN cA, compA_u cA cN, eqA_u (cpc cN cA) (cpc cA cN),
    compA_u cN cB, compA_u cB cN, eqA_u (cpc cN cB) (cpc cB cN),
    compA_u cE1 cE1, eqA_u (cpc cE1 cE1) ce,
    compA_u cT cE1, compA_u cE1 cT, eqA_u (cpc cT cE1) (cpc cE1 cT), eqA_u cE1 cT,
    compA_u cN cE1, compA_u (cpc cN cE1) cNi, eqA_u (cpc (cpc cN cE1) cNi) (cpc cT cE1),
    compA_u cE1 cA, compA_u cA cE1, eqA_u (cpc cE1 cA) (cpc cA cE1),
    compA_u cE1 cB, compA_u cB cE1, eqA_u (cpc cE1 cB) (cpc cB cE1),
    compA_u cS cT, compA_u cT cS, eqA_u (cpc cS cT) (cpc cT cS),
    compA_u cS cE1, compA_u cE1 cS, eqA_u (cpc cS cE1) (cpc cE1 cS)]
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
  rfl

end CertificateChecks.KernelSpor.S26990

end
