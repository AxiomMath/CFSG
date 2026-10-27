module

public import Certificates.Kernel.Sporadic.OddCore.S8147Rnd
import Certificates.Kernel.Co1B.GenTri2045
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.S8147

@[expose] noncomputable def case1B (s : Nat) : Bool := caseB (nat_lit 1) s

end CertificateChecks.KernelSpor.S8147

#kc_slices CertificateChecks.KernelSpor.S8147.Rnd1 CertificateChecks.KernelSpor.S8147.case1B 6

end
