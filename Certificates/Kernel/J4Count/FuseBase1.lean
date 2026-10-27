
module

public import Certificates.Kernel.J4Count.FuseBase

public import Certificates.Kernel.J4Count.FuseChecks
public import Certificates.Kernel.J4Count.FixZKBase
public import Certificates.Kernel.SporSch.J4S.Regs
public import CFSG.Certificates.Kernel.SporSch.J4SPairSound
public import CFSG.Quasithin.H13.J4CentralizerBase1

@[expose] public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Count.Fuse

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KS.SporSch.J4B CFSG.Sporadic.J4Schreier
open CFSG.Quasithin.H13.J4 (uP vP dP tP cnjP conjEqP lettersOK)

end CertificateChecks.KernelJ4Count.Fuse

end
