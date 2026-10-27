module

public import Certificates.Kernel.Sporadic.OddCore.HND0
meta import CFSG.Sporadic.HNOddCore.InvArrays
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.HNT.CL CFSG.Sporadic.HNOddCore.InvData.cleftText
#ks_lines CertificateChecks.KernelSpor.HNT.CL CFSG.Sporadic.HNOddCore.InvData.cleftTabs

namespace CertificateChecks.KernelSpor.HND

open CFSG.Sporadic.HNOddCore CFSG.Sporadic.HNOddCore.InvData CFSG.Sporadic.HNOddCore.Native
open CFSG.KS.DecLines

theorem cl_eq : cleftTabs = (HNT.CL.E.map List.toArray).toArray := by
  unfold cleftTabs; rw [HNT.CL.eq]; exact linesOf_of_chk HNT.CL.ok

theorem cl_shape : (cleftTabs.size == 11 && allSize cleftTabs 14400) = true := by
  rw [cl_eq]; exact shape_of (by decide +kernel)

end CertificateChecks.KernelSpor.HND

end
