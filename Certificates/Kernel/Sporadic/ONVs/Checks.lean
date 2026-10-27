module

public import Certificates.Kernel.Sporadic.ONC.Defs
public import Certificates.Kernel.Sporadic.ONVs.Data
public import Certificates.Data.Kernel.Spor.ONVsK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONVs

open CFSG.KS CFSG.KS.ON CFSG.KS.PEnum CFSG.KS.ONVs CertificateChecks.KernelSpor
  CertificateChecks.KernelSpor.ONC

theorem vs_ok : vsCheck LJ (fun x => tab ONW2.NEG x) (fun x => r32 LF x) OVS.D = true := by
  quickRfl

end CertificateChecks.KernelSpor.ONVs

end
