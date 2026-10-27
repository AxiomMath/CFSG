module

public import Certificates.Kernel.Sporadic.OddCore.HND0
meta import CFSG.Sporadic.HNOddCore.InvArrays
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.HNT.PL CFSG.Sporadic.HNOddCore.InvData.pleftText
#ks_lines CertificateChecks.KernelSpor.HNT.PL CFSG.Sporadic.HNOddCore.InvData.pleftTabs

namespace CertificateChecks.KernelSpor.HND

open CFSG.Sporadic.HNOddCore CFSG.Sporadic.HNOddCore.InvData CFSG.Sporadic.HNOddCore.Native
open CFSG.KS.DecLines

theorem pl_eq : pleftTabs = (HNT.PL.E.map List.toArray).toArray := by
  unfold pleftTabs; rw [HNT.PL.eq]; exact linesOf_of_chk HNT.PL.ok

theorem pl_shape : (pleftTabs.size == 14 && allSize pleftTabs 16384) = true := by
  rw [pl_eq]; exact shape_of (by decide +kernel)

end CertificateChecks.KernelSpor.HND

end
