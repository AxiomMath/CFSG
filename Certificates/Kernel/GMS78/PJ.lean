module

public import Certificates.Kernel.GMS78.P117Data
public import Certificates.Data.Kernel.GMS78RuP117
public import Certificates.Kernel.LocalComp.BlockGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelGMS78.SD

open CFSG.KC.GMS

@[expose] noncomputable def mP : Nat → Nat → Nat := sMulK GT DPR LIN DM DO1

@[expose] noncomputable def jmF (i : Nat) : Bool := kJM mP XS JM i

#lc_blocks jmB jmF 16384 64

end CertificateChecks.KernelGMS78.SD

end
