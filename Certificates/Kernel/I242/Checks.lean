module

public import Certificates.Data.Kernel.Fi22.I242
public import Certificates.Kernel.I242.Text
public import Certificates.Kernel.I242.YData
public import Certificates.Kernel.Sporadic.Fi22.F1OuterT
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelI242

open CFSG.KC.Enum CFSG.KC.I242 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.HardMathSupport.Solomon.Coordinator

theorem kId : idK 3510 12 (mask 12) = true := by quickRfl

theorem kQA : bAnd(cn (CertificateChecks.KernelSpor.Fi22OutT.L 1), cn (H.F 1)) = true := by
  quickRfl

theorem kParts : allN 6 (partsK H.F (CertificateChecks.KernelSpor.Fi22OutT.L 1)) = true := by
  quickRfl

theorem kD : allN 12 (fun j => permOK 3510 12 (mask 12) (3510 * 12)
    (dK H.F (CertificateChecks.KernelSpor.Fi22OutT.L 1) j)
    (dIK H.F (CertificateChecks.KernelSpor.Fi22OutT.L 1) j)) = true := by
  quickRfl

theorem kY : allN 8 (fun r => wordEqK 3510 12 (mask 12) (pidn 3510 12)
    (dK H.F (CertificateChecks.KernelSpor.Fi22OutT.L 1))
    (dIK H.F (CertificateChecks.KernelSpor.Fi22OutT.L 1)) 12 (i242Words.getD r []) (Y.S r)) = true := by
  quickRfl

end CertificateChecks.KernelI242

end
