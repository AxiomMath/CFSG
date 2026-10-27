module

public import Certificates.Kernel.SporSch.HN.FixK.Tab13608
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelSporSch.HN13608

open CFSG.KC.LL.HNX CFSG.KD.HN13608 CFSG.KD.LgHNX CFSG.KD.HNXK

theorem consts : dotConstsOK MS REP ONES L1 MR = true := by quickRfl

end CertificateChecks.KernelSporSch.HN13608

end
