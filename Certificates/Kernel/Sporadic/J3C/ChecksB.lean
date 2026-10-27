module

public import Certificates.Kernel.Sporadic.J3C.Checks
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000
set_option Elab.async false

public section

namespace CertificateChecks.KernelSpor.J3C

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.PC CFSG.KS.CentReg CFSG.KS.Raw
  CFSG.ClassicalInvolution.J3Data CertificateChecks.KernelSchreierFam.J3Cq

theorem klInv : invK KLr 20520 4 = true := by quickRfl

theorem rc1 : Nat.beq (rcnt (SY.LR 1)) 1 = true := by quickRfl

theorem rc2 : Nat.beq (rcnt (SY.LR 2)) 1 = true := by quickRfl

theorem cwLet :
    List.all conjWordsAB (fun w => List.all w fun z => Nat.blt (sgnL z) 4) = true := by
  decide +kernel

theorem klInvNeg : invK (fun l => KLr (List.getD [0, 3, 2, 1] l 0)) 20520 4 = false := by
  decide +kernel

end CertificateChecks.KernelSpor.J3C

end
