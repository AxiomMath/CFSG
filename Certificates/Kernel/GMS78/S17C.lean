module

public import Certificates.Kernel.GMS78.S95Data
public import Certificates.Kernel.GMS78.P117Data
public import Certificates.Data.Kernel.GMS78RuSCent
public import Certificates.Kernel.LocalComp.BlockGen

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelGMS78.SD

open CFSG.KC.GMS

@[expose] noncomputable def a17tF0 (j : Nat) : Bool :=
  kAll17 GT DPR LIN DM DO1 (neGet 0 I171 j) (neGet 0 K171 j)

#lc_blocks a17tB0 a17tF0 279 1

end CertificateChecks.KernelGMS78.SD

end
