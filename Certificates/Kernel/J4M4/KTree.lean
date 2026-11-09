module

public import Certificates.Kernel.J4M4.DefsK
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4M4

#kc_each CertificateChecks.KernelJ4M4.layKK 0 10

theorem headKK_ok : headKK = true := by quickRfl

theorem headK_ok : headK = true := headK_eq.trans headKK_ok

theorem layK0 : layK 0 = true := (layK_eq 0).trans layKK0
theorem layK1 : layK 1 = true := (layK_eq 1).trans layKK1
theorem layK2 : layK 2 = true := (layK_eq 2).trans layKK2
theorem layK3 : layK 3 = true := (layK_eq 3).trans layKK3
theorem layK4 : layK 4 = true := (layK_eq 4).trans layKK4
theorem layK5 : layK 5 = true := (layK_eq 5).trans layKK5
theorem layK6 : layK 6 = true := (layK_eq 6).trans layKK6
theorem layK7 : layK 7 = true := (layK_eq 7).trans layKK7
theorem layK8 : layK 8 = true := (layK_eq 8).trans layKK8
theorem layK9 : layK 9 = true := (layK_eq 9).trans layKK9

end CertificateChecks.KernelJ4M4
