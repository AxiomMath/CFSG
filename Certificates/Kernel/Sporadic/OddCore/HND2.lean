module

public import Certificates.Kernel.Sporadic.OddCore.HND0
meta import CFSG.Sporadic.HNOddCore.InvArrays
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.HNT.S6 CFSG.Sporadic.HNOddCore.InvData.s6Text
#ks_lines CertificateChecks.KernelSpor.HNT.S6 CFSG.Sporadic.HNOddCore.InvData.s6Perms
#ks_chars CertificateChecks.KernelSpor.HNT.VL CFSG.Sporadic.HNOddCore.InvData.vleftText
#ks_lines CertificateChecks.KernelSpor.HNT.VL CFSG.Sporadic.HNOddCore.InvData.vleftTabs

namespace CertificateChecks.KernelSpor.HND

open CFSG.Sporadic.HNOddCore CFSG.Sporadic.HNOddCore.InvData CFSG.Sporadic.HNOddCore.Native
open CFSG.KS.DecLines

theorem s6_eq : s6Perms = (HNT.S6.E.map List.toArray).toArray := by
  unfold s6Perms; rw [HNT.S6.eq]; exact linesOf_of_chk HNT.S6.ok
theorem vl_eq : vleftTabs = (HNT.VL.E.map List.toArray).toArray := by
  unfold vleftTabs; rw [HNT.VL.eq]; exact linesOf_of_chk HNT.VL.ok

theorem s6_shape : (s6Perms.size == 12 && allSize s6Perms 8800) = true := by
  rw [s6_eq]; exact shape_of (by decide +kernel)
theorem vl_shape : (vleftTabs.size == 10 && allSize vleftTabs 4608) = true := by
  rw [vl_eq]; exact shape_of (by decide +kernel)

end CertificateChecks.KernelSpor.HND

end
