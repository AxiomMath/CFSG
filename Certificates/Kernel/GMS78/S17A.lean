module

public import Certificates.Kernel.GMS78.S95Data
public import Certificates.Kernel.GMS78.P117Data
public import Certificates.Data.Kernel.GMS78RuSCent
public import Certificates.Kernel.LocalComp.BlockGen

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelGMS78.SD

open CFSG.KC.GMS

@[expose] noncomputable def a17fF0 (j : Nat) : Bool :=
  kAll17 GT DPR LIN DM DO0 (neGet 0 I170 j) (neGet 0 K170 j)

#lc_blocks a17fB0 a17fF0 279 1

end CertificateChecks.KernelGMS78.SD

end
