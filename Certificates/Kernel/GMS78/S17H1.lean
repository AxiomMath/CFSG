module

public import Certificates.Kernel.GMS78.S95Data
public import Certificates.Kernel.GMS78.P117Data
public import Certificates.Kernel.GMS78.S17GData
public import Certificates.Data.Kernel.GMS78RuSGrp
public import Certificates.Kernel.LocalComp.BlockGen

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelGMS78.SD

open CFSG.KC.GMS

@[expose] noncomputable def a17tH (j : Nat) : Bool :=
  kAll17H GT DPR LIN DM DO1 I171 K171 G17 16 (Nat.add 279 j)

#lc_blocks a17tHB a17tH 279 1

end CertificateChecks.KernelGMS78.SD

end
