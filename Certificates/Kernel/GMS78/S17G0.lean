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

@[expose] noncomputable def g17fF (g : Nat) : Bool :=
  kGrpAt GT DPR LIN DM DO0 I170 K170 (neGet [] G17 g)

#lc_blocks g17fB g17fF 16 1

end CertificateChecks.KernelGMS78.SD

end
