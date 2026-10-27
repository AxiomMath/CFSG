module

public import Certificates.Data.Kernel.Misc.OqBlk

public section

namespace CertificateChecks.KernelMisc.Oq

open CFSG.KC.Misc.Oq CFSG.KC.LQT.P

theorem blkL : allN 9 okL = true := by decide +kernel

end CertificateChecks.KernelMisc.Oq

end
