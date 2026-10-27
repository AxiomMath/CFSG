module

public import CFSG.Certificates.Kernel.Spor.MathieuSound
public import Certificates.Data.CFSGNative.Mathieu.M12
public import Certificates.Data.CFSGNative.Mathieu.M22
public import Certificates.Data.CFSGNative.Mathieu.M24
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelSpor.Mathieu

open CFSG.Sporadic.Mathieu.Native CFSG.KS.Mathieu

theorem m12K : mcheck 12 5 m12Data = true := by quickRfl

theorem m22K : mcheck 22 5 m22Data = true := by quickRfl

theorem m24K : mcheck 24 5 m24Data = true := by quickRfl

theorem m12 : check 12 m12Data = true := mcheck_sound (by decide) m12K

theorem m22 : check 22 m22Data = true := mcheck_sound (by decide) m22K

theorem m24 : check 24 m24Data = true := mcheck_sound (by decide) m24K

end CertificateChecks.KernelSpor.Mathieu

end
