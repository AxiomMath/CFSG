module

public import Certificates.Data.CFSGNative.F4.Unitary
public import CFSG.Certificates.Kernel.Common.Eval
meta import Certificates.Kernel.SmithEK.Gen

#kc_eval CertificateChecks.KernelSmithEK pts CertificateChecks.KernelSmithEK.ptsStep

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.F4.Native

theorem uPts_eq : uPts () = pts.L.toArray := by
  decide +kernel

end CertificateChecks.KernelSmithEK
