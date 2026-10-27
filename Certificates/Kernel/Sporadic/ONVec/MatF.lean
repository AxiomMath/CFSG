module

public import Certificates.Kernel.Sporadic.ONVec.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONVec

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CertificateChecks.KernelSpor

theorem formAK : allN 154 (fun i => Nat.beq (mv RA (mv CM (ONV.CA i))) (at0 CM i)) = true := by
  quickRfl
theorem formBK : allN 154 (fun i => Nat.beq (mv RB (mv CM (ONV.CB i))) (at0 CM i)) = true := by
  quickRfl

end CertificateChecks.KernelSpor.ONVec

end
