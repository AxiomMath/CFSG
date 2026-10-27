module

public import Certificates.Data.Kernel.Misc.OqBlk

public section

namespace CertificateChecks.KernelMisc.Oq

open CFSG.KC.Misc.Oq CFSG.KC.LQT.P

theorem blkU0 : allN 10 (okUs 0) = true := by decide +kernel

end CertificateChecks.KernelMisc.Oq

end
