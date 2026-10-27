
module

public import Certificates.Kernel.Sporadic.L2C.AllBase

public import Certificates.Kernel.Sporadic.L2C.G1

public section

namespace CertificateChecks.KernelSpor.L2CG

open CFSG.KC.Enum CertificateChecks.KernelSpor.L2CK
open CertificateChecks.KernelSpor.L2G (nblt slices)

theorem base_true : CFSG.Sporadic.SuzRecog.LevelTwoCover.coverBaseOK = true :=
  coverBaseOK_true baseH

end CertificateChecks.KernelSpor.L2CG

end
