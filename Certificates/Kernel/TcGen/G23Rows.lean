module

public import Certificates.Kernel.TcGen.Small3
public import Certificates.Kernel.Misc.Coset.C12042K
public import Certificates.Data.Kernel.LaneRows

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelTc.G23

open CFSG.KC.LaneRows CertificateChecks.KernelMiscCoset.C12042

theorem rowsA_K : rowsEqK lay A aL = true := by decide +kernel

theorem rowsB_K : rowsEqK lay B bL = true := by decide +kernel

end CertificateChecks.KernelTc.G23

end
