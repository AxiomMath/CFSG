module

public import Certificates.Kernel.Sporadic.Fi22.F3152Data
public import Certificates.Kernel.Sporadic.Fi22.F3152Bind
public import Certificates.Kernel.Co1B.GenTri2045

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.F3152

open CFSG.KS.F3152

@[expose] noncomputable def lineSlice (c : Nat) : Bool :=
  linesK SL (nat_lit 54) (dropK (Nat.mul (nat_lit 54) c) T.CH) (Nat.mul (nat_lit 54) c)

end CertificateChecks.KernelSpor.F3152

#kc_slices CertificateChecks.KernelSpor.F3152.Lines CertificateChecks.KernelSpor.F3152.lineSlice 65

end
