module

public import Certificates.Data.Kernel.SmithEKG
public import Certificates.Kernel.SmithEK.MData
public import Certificates.Kernel.SmithEK.Cols

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE.K

theorem c21260planes : planesK pb.P 4000037 = true := by
  decide +kernel

theorem c21260form : formInvK cs.L = true := by
  decide +kernel

end CertificateChecks.KernelSmithEK
