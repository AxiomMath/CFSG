module

public import Certificates.Kernel.LocalComp.L34SData
public import Certificates.Kernel.LocalComp.L34RDefs
public import Certificates.Data.Kernel.L34Graph
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34Graph

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34Graph CFSG.KC.L34W
open CertificateChecks.KernelLC CertificateChecks.KernelLC.L34X
open CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.KLie.CT (andB notB)

theorem kBits22210 : bitsOK = true := by quickRfl

theorem kDec22210 : decK L34R.G = true := by quickRfl

theorem kGraph22210 : graphK L34R.G (L34O.T 1) (L34O.T 2) (L34O.T 3) = true := by quickRfl

end CertificateChecks.KernelLC.L34Graph

end
