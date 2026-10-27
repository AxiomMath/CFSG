module

public import Certificates.Kernel.SporSch.PairHS.Aut4052Fns
public import Certificates.Kernel.SporSch.Ru.RowsGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_b2 CertificateChecks.KernelSporSch.PHSA CertificateChecks.KernelSporSch.PHSA.bindG 0 3 5
#kss_b2all CertificateChecks.KernelSporSch.PHSA CertificateChecks.KernelSporSch.PHSA.bindG 3 5

namespace CertificateChecks.KernelSporSch.PHSA

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CertificateChecks.KernelSporSch

theorem perm : permB = true := by quickRfl
theorem small : smallB = true := by quickRfl
theorem a0_01 : Nat.beq (a0P 0) 1 = true := by quickRfl
theorem vSum : Nat.beq (sumN 25 vAt) 2 = true := by quickRfl

end CertificateChecks.KernelSporSch.PHSA

end
