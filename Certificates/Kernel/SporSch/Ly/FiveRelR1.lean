module

public import Certificates.Kernel.SporSch.Ly.FiveRelR0

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.LyFR

@[expose] noncomputable def relBlk1 (g : Nat) : Bool := relBlk (Nat.add 45 g)

end CertificateChecks.KernelSporSch.LyFR

#kss_each CertificateChecks.KernelSporSch.LyFRR1 CertificateChecks.KernelSporSch.LyFR.relBlk1 45

end
