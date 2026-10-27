module

public import Certificates.Kernel.HSStd.L34CentData
public import Certificates.Kernel.LocalComp.L34RDefs
public import Certificates.Data.Kernel.L34Inv
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Sporadic.ON.Gen

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelHSStd.L34C

open CFSG.KC.Enum CFSG.KC.L34K CFSG.KC.L34Inv CertificateChecks.KernelLC CertificateChecks.KernelLC.L34X

@[expose] noncomputable def cs (s : Nat) : Bool := centSl 42 6 L34R.T (RP 2) 1344 CC s

end CertificateChecks.KernelHSStd.L34C

#kon_slices CertificateChecks.KernelHSStd.L34C.cs 0 180
#kon_join CertificateChecks.KernelHSStd.L34C.csAll CertificateChecks.KernelHSStd.L34C.cs 180

namespace CertificateChecks.KernelHSStd.L34C

open CFSG.KC.Enum CFSG.KC.L34K CFSG.KC.L34Inv CertificateChecks.KernelLC CertificateChecks.KernelLC.L34X

theorem kEnds : (Nat.beq (CC 0) 0 && Nat.beq (CC 180) 240) = true := by quickRfl

theorem kList : centList 42 6 241920 L34R.T (RP 2) 240 X P = true := by quickRfl

theorem kHL : hl34K 42 6 240 P (RP 2) 360 (L34O.T 1) 280 (L34O.T 3) = true := by quickRfl

theorem kHFI : hfi34K 42 6 240 P (RP 2) 1008 (L34O.T 2) = true := by quickRfl

end CertificateChecks.KernelHSStd.L34C

end
