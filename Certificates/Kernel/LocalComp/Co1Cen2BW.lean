module

public import Certificates.Kernel.LocalComp.Co1Cen2BD
public import Certificates.Data.Kernel.Co1BTri
public import CFSG.Certificates.Kernel.Enum.Defs
public meta import Certificates.Kernel.Co1B.GenTri2045

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.Co1Cen2B

open CFSG.KC.Co1T CertificateChecks.KernelCo1B.Tri2045

@[expose] noncomputable def wsl (T P s : Nat) : Bool := triWK T TB.PT P (s * 128) 128

@[expose] noncomputable def wA : Nat → Bool := wsl (TB.T 12) (CFSG.KC.Enum.pidn 1365 11)
@[expose] noncomputable def wE : Nat → Bool := wsl TA.T1 (CFSG.KC.Enum.pidn 1365 11)
@[expose] noncomputable def wZ : Nat → Bool := wsl TA.T2 TA.PZ
@[expose] noncomputable def wC : Nat → Bool := wsl TA.T3 TA.PC

end CertificateChecks.KernelLC.Co1Cen2B

#kc_slices CertificateChecks.KernelLC.Co1Cen2B.WA CertificateChecks.KernelLC.Co1Cen2B.wA 11
#kc_slices CertificateChecks.KernelLC.Co1Cen2B.WE CertificateChecks.KernelLC.Co1Cen2B.wE 11
#kc_slices CertificateChecks.KernelLC.Co1Cen2B.WZ CertificateChecks.KernelLC.Co1Cen2B.wZ 11
#kc_slices CertificateChecks.KernelLC.Co1Cen2B.WC CertificateChecks.KernelLC.Co1Cen2B.wC 11

end
