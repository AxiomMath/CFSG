module

public import Certificates.Kernel.SuzPump.PumpFuse
public import Certificates.Kernel.LocalQT.Tc.Gen
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000
set_option Elab.async false

public section

namespace CertificateChecks.KernelSuzPump

open CertificateChecks.KernelSpor

@[expose] noncomputable def el0B (b : Nat) : Bool := elB 0 SFC0.T b

@[expose] noncomputable def el3B (b : Nat) : Bool := elB 3 SFC3.T b

@[expose] noncomputable def el4B (b : Nat) : Bool := elB 4 SFC4.T b

end CertificateChecks.KernelSuzPump

#kqb_range CertificateChecks.KernelSuzPump.FE0 CertificateChecks.KernelSuzPump.el0B 0 6
#kqb_all CertificateChecks.KernelSuzPump.FE0 CertificateChecks.KernelSuzPump.el0B 6
#kqb_range CertificateChecks.KernelSuzPump.FE3 CertificateChecks.KernelSuzPump.el3B 0 6
#kqb_all CertificateChecks.KernelSuzPump.FE3 CertificateChecks.KernelSuzPump.el3B 6
#kqb_range CertificateChecks.KernelSuzPump.FE4 CertificateChecks.KernelSuzPump.el4B 0 6
#kqb_all CertificateChecks.KernelSuzPump.FE4 CertificateChecks.KernelSuzPump.el4B 6

end
