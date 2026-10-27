module

public import Certificates.Kernel.E64CC.Orb

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelE64CC

open CFSG.KC.E64CC CFSG.KC.Enum

theorem ix_ok : allN 28 (ixK CFSG.KD.E64CC.D MT.T MT.N) = true := by decide +kernel

theorem pi_ok : piK MT.T MT.N = true := by decide +kernel

theorem cl_ok : allN 14 (clK CFSG.KD.E64CC.D) = true := by decide +kernel

end CertificateChecks.KernelE64CC

end
