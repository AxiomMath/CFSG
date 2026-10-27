module

public import Certificates.Kernel.LocalComp.Q47Pack
import Certificates.Kernel.Sporadic.ON.Gen

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.Q47

open CFSG.KC.Enum CFSG.KS CFSG.KC.HeAutK CFSG.KC.Q47K CertificateChecks.KernelLC

@[expose] noncomputable def rowY (b : Nat) : Bool :=
  allR (tableRowK Q47Y.N Q47Y.T Q47Y.S MPY 3 2 Nat.beq) (8 * b) 8

@[expose] noncomputable def rowN (b : Nat) : Bool :=
  allR (tableRowK Q47N.N Q47N.T Q47N.S MPN 2 7 projK) (16 * b) 16

end CertificateChecks.KernelLC.Q47

set_option Elab.async false

#kon_slices CertificateChecks.KernelLC.Q47.ob 0 35
#kon_join CertificateChecks.KernelLC.Q47.obAll CertificateChecks.KernelLC.Q47.ob 35
#kon_slices CertificateChecks.KernelLC.Q47.rowY 0 21
#kon_join CertificateChecks.KernelLC.Q47.rowYAll CertificateChecks.KernelLC.Q47.rowY 21
#kon_slices CertificateChecks.KernelLC.Q47.rowN 0 21
#kon_join CertificateChecks.KernelLC.Q47.rowNAll CertificateChecks.KernelLC.Q47.rowN 21

end
