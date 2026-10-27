module

public import Certificates.Kernel.Sporadic.OddCore.S2301Rnd
import Certificates.Kernel.Co1B.GenTri2045
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.SuzOddCore.Arrays

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.S2301

@[expose] noncomputable def case0B (s : Nat) : Bool := caseB (nat_lit 0) s

end CertificateChecks.KernelSpor.S2301

#kc_slices CertificateChecks.KernelSpor.S2301.Rnd0 CertificateChecks.KernelSpor.S2301.case0B 10

end
