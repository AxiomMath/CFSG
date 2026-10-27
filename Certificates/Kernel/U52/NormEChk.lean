module

public import Certificates.Kernel.U52.NormChk
public import Certificates.Kernel.U52.LettersF
public import Certificates.Kernel.U52.NormEData
public import Certificates.Data.Kernel.U52.NormE
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelU52

open CFSG.ASVolI CFSG.KC.Enum CFSG.KS CFSG.KS.WordF CFSG.KS.U52N CertificateChecks.KernelU52.N
  CertificateChecks.KernelU52.NE CertificateChecks.KernelU52F

@[expose] noncomputable def eKL (j : Nat) : List Nat :=
  (burnsideF48t_u52eKhW.getD j []).map (evFK 462 9 (mask 9) (pidn 462 9) LFP LFPI)

@[expose] noncomputable def eRisX : List Nat :=
  burnsideF48t_u52eXW.map fun w => evFK 462 9 (mask 9) (pidn 462 9) LFP LFPI (burnsideF48s_eInvW w)

@[expose] noncomputable def eRisY : List Nat :=
  burnsideF48t_u52eYW.map fun w => evFK 462 9 (mask 9) (pidn 462 9) LFP LFPI (burnsideF48s_eInvW w)

@[expose] noncomputable def nS0 : List Nat :=
  burnsideF48t_u52SW.map (evFK 462 9 (mask 9) (pidn 462 9) LP LPI)

@[expose] noncomputable def eTest1 (e : Nat) : Bool :=
  hatT 462 9 (mask 9) 165 (eKL 0) [] e && hatT 462 9 (mask 9) 165 (eKL 1) [] e &&
    hatT 462 9 (mask 9) 165 (eKL 2) eRisX e

@[expose] noncomputable def eTest2 (e : Nat) : Bool :=
  hatT 462 9 (mask 9) 0 (eKL 2) eRisY e && hatT 462 9 (mask 9) 0 (eKL 3) [] e

theorem eKh : allN 4 (fun j => khOK 462 9 (mask 9) (pidn 462 9) (eKL j) nKL) = true := by
  quickRfl

theorem eF : (Nat.beq (pcomp 462 9 (mask 9) (LFP 4) (LFP 4)) (pidn 462 9) &&
    nKG.all (fun g => memN (pcomp 462 9 (mask 9) (pcomp 462 9 (mask 9) (LFP 4) g) (LFP 4)) nKL)) =
      true := by
  quickRfl

theorem eT1 : (elems 462 9 (mask 9) (pidn 462 9) SVP1 EWP1).all
    (fun e => eTest1 e && eTest1 (pcomp 462 9 (mask 9) (LFP 4) e)) = true := by
  quickRfl

theorem eT2 : (elems 462 9 (mask 9) (pidn 462 9) SVP2 EWP2).all
    (fun e => eTest2 e && eTest2 (pcomp 462 9 (mask 9) (LFP 4) e)) = true := by
  quickRfl

theorem eTB : SBK.length = 36 ∧ SBW.length = 36 ∧ allN 36 (fun i =>
    hatB 462 9 (mask 9) (pidn 462 9) nKL nS0 ((elems 462 9 (mask 9) (pidn 462 9) SVB EWB).getD i 0)
      (SBK.getD i 0) (SBW.getD i []) &&
    hatF 462 9 (mask 9) nKL [eKL 0, eKL 1, eKL 2, eKL 3]
      (pcomp 462 9 (mask 9) (LFP 4) ((elems 462 9 (mask 9) (pidn 462 9) SVB EWB).getD i 0))) =
      true := by
  refine ⟨by decide +kernel, by decide +kernel, by quickRfl⟩

end CertificateChecks.KernelU52

end
