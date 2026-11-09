module

public import Certificates.Kernel.LocalComp.Q47Pack
public import CFSG.Certificates.Kernel.Q47KTabSound
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.Q47

open CFSG.KC.Enum CFSG.KS CFSG.KC.HeAutK CFSG.KC.Q47K CertificateChecks.KernelLC

theorem kGenRowY : allN 2 (fun k => allN Q47Y.N (genRowK Q47Y.N Q47Y.G Q47Y.T Q47Y.E MPY 3 2 Nat.beq k)) =
    true := by
  quickRfl

theorem kGenRowN : allN 2 (fun k => allN Q47N.N (genRowK Q47N.N Q47N.G Q47N.T Q47N.E MPN 2 7 projK k)) =
    true := by
  quickRfl

end CertificateChecks.KernelLC.Q47

set_option Elab.async false

#kon_slices CertificateChecks.KernelLC.Q47.ob 0 35
#kon_join CertificateChecks.KernelLC.Q47.obAll CertificateChecks.KernelLC.Q47.ob 35

end
