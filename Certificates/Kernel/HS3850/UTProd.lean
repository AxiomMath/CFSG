module

public import Certificates.Kernel.HS3850.UTDefs
public import Certificates.Kernel.LocalQT.Tc.Gen
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.ConjOrb
public import Certificates.Data.Kernel.PkPow

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelHS3850.UT

open CFSG.KD.LQT.C4126 CFSG.KC.LQT.SV

theorem ksort : sortAllSV 1024 (fun k => kk (SY.E k)) KS KR = true := by quickRfl

end CertificateChecks.KernelHS3850.UT

end
