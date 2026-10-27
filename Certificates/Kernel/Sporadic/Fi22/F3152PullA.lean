module

public import Certificates.Kernel.Sporadic.Fi22.F3152Data
public import Certificates.Kernel.Fi22Core.Data
public import Certificates.Kernel.Co1B.GenTri2045

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.F3152

open CFSG.KS.F3152

@[expose] noncomputable def pullSliceA (c : Nat) : Bool :=
  pullK (SL (nat_lit 3512)) CertificateChecks.KernelFi22C.LA (GL (nat_lit 0)) SL (nat_lit 54)
    (Nat.mul (nat_lit 54) c)

end CertificateChecks.KernelSpor.F3152

#kc_slices CertificateChecks.KernelSpor.F3152.PullA CertificateChecks.KernelSpor.F3152.pullSliceA 65

end
