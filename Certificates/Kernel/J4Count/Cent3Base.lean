
module

public import Certificates.Kernel.J4Count.Cent3Checks
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Certificates.Kernel.J4FiveSound
public import Certificates.Data.J4M2.Orbit

@[expose] public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Count.FixCE

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Quasithin.J4M2 CFSG.KC.J4Cent3 CFSG.KC.J4Five CFSG.KC.J4Q
open CFSG.KD.J4FixCE CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs CertificateChecks.KernelJ4Count.Cent3
open Equiv

theorem ZE_lt {i : ℕ} (hi : i < 24) : getN 0 ZE i < 24 := (fixOK_spec ce_fix i hi).1

end CertificateChecks.KernelJ4Count.FixCE

end
