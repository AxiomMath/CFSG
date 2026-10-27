module

public import Certificates.Kernel.SporSch.PairJ3.C81Fns
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_b2 CertificateChecks.KernelSporSch.PJ3C81 CertificateChecks.KernelSporSch.PJ3C81.sB 0 2 2

namespace CertificateChecks.KernelSporSch.PJ3C81

open CFSG.KC.Enum

theorem o1_all : allN 960 o1At = true := by quickRfl

theorem o2_all : allN 1224 o2At = true := by quickRfl

theorem pt_all : allN 6156 ptAt = true := by quickRfl

theorem small : smallB = true := by quickRfl

end CertificateChecks.KernelSporSch.PJ3C81

end
