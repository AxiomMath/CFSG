module

public import Certificates.Kernel.MaxD2.McLP.Glue
public import Certificates.Kernel.MaxD2.McLP.NonComm
public import CFSG.Certificates.Kernel.MaxD2.HeisNonComm

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMaxD2.McLP

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MaxD2 CFSG.KS.PEnum CFSG.KS.Row
open Certificates.MaxD2Perm Certificates.MaxD2Heis

theorem mcl_nonComm : checkHNonComm mclFiveDataP = true := by
  have k : (Nat.blt 1 NE.k && (Nat.blt 3 NE.k && notInK RE.cnt RE.T
      (pcomp 275 9 (mask 9) (pcomp 275 9 (mask 9)
        (pcomp 275 9 (mask 9) (NE.G 1) (NE.G 3)) (NGI 1)) (NGI 3)))) = true := by
    rw [← ncK.eq_1]
    exact k_nc
  simp only [Bool.and_eq_true] at k
  obtain ⟨h1, h2, h3⟩ := k
  exact checkHNonComm_of hypsH (Nat.blt_eq.mp h1) (Nat.blt_eq.mp h2) h3

end CertificateChecks.KernelMaxD2.McLP

end
