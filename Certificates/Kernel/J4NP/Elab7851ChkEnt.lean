module

public import Certificates.Data.Kernel.J4NP.Elab7851
public import Certificates.Kernel.J4NP.Elab7851Data
public import Certificates.Kernel.J4Q.AllN

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4NP

open CFSG.KC.J4Q CFSG.KC.J4Loc CFSG.KC.J4NP CFSG.KD.J4NP

@[expose] noncomputable def ch7851e (k : Nat) : Bool := entBlk MK CMK PRK FMK 7507 ENT k

#j4q_all CFSG.KD.J4NP.ch7851E CertificateChecks.KernelJ4NP.ch7851e 235

end CertificateChecks.KernelJ4NP

end
