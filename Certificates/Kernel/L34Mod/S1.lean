module

public import Certificates.Data.Kernel.L34Mod
public import CFSG.Certificates.Kernel.Common.Cover

public section

namespace CertificateChecks.KernelL34Mod

open CFSG.KC.L34Mod

theorem s1_all : ∀ t, t < 65536 → s1 t = true := by
  kc_cover 512

end CertificateChecks.KernelL34Mod
