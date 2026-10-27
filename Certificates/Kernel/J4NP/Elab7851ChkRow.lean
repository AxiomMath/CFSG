module

public import Certificates.Data.Kernel.J4NP.Elab7851
public import Certificates.Kernel.J4NP.Elab7851Data
public import Certificates.Kernel.J4Q.MaskData
public import Certificates.Kernel.J4Q.AllN
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4NP

open CFSG.KC.J4Q CFSG.KC.J4Loc CFSG.KC.J4NP CFSG.KD.J4NP

theorem ch7851_pin : pinOK KK CFSG.KD.J4Q.mkTL = true := by quickRfl

theorem ch7851_xp : xpOK XP = true := by quickRfl

theorem ch7851_root : Nat.beq (lnS 191 MK 0) 0 = true := by quickRfl

@[expose] noncomputable def ch7851r (a : Nat) : Bool := rowOK KK CMK PRK FMK XP FL a

#j4q_all CFSG.KD.J4NP.ch7851R CertificateChecks.KernelJ4NP.ch7851r 191

end CertificateChecks.KernelJ4NP

end
