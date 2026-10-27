module

public import Certificates.Kernel.SporSch.PairHS.HS2272Fns
public import Certificates.Kernel.SporSch.Ru.RowsGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HS72

theorem valid : validB = true := by quickRfl
theorem u_ok : uB = true := by quickRfl
theorem stab : stabB = true := by quickRfl
theorem rep_a : repA = true := by quickRfl
theorem wd_ok : wdB = true := by quickRfl
theorem sort_ok : sortB = true := by quickRfl

end CertificateChecks.KernelSporSch.HS72

#kss_each CertificateChecks.KernelSporSch.HS72.HSR CertificateChecks.KernelSporSch.HS72.recB 4
#kss_each CertificateChecks.KernelSporSch.HS72.HSF CertificateChecks.KernelSporSch.HS72.cfB 4
#kss_each CertificateChecks.KernelSporSch.HS72.HSD4 CertificateChecks.KernelSporSch.HS72.dataB 4

end
