module

public import Certificates.Kernel.Sporadic.Co1Row26683.Data
public import Certificates.Data.Kernel.Spor.Co1Row26683K
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Co1Row26683

open CFSG.KS.Co1Row26683 CertificateChecks.KernelSpor

@[expose] noncomputable def ch26683S (s : Nat) : Bool :=
  sSl (nthN C26683.GK) C26683.RP C26683.NOP C26683.QP C26683.QIP C26683.NC s

end CertificateChecks.KernelSpor.Co1Row26683

#kc_each CertificateChecks.KernelSpor.Co1Row26683.ch26683S 0 16

end
