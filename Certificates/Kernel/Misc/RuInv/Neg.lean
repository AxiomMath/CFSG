module

public import Certificates.Kernel.Misc.RuInv.Gens
public import CFSG.Certificates.Kernel.Lie.CT.Core
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option Elab.async false

namespace CertificateChecks.KernelMisc.RuInv.Neg

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.RuInv CertificateChecks.KernelMisc.RuInv
open CFSG.KLie.CT (notB)

theorem reach : notB (reachK NX.n0 1 31) = true := by quickRfl

theorem keys : notB (keysK HS (Nat.lor (Nat.lor (Nat.shiftLeft (at11 PK.n0 0) 11) (at11 PK.n0 1))
    (Nat.shiftLeft (Nat.shiftRight PK.n0 22) 22)) 1391) = true := by quickRfl

theorem hash : notB (hashE E (fun j => HS (Nat.succ j)) 0) = true := by quickRfl

theorem rep : notB (Nat.beq (E 1) (powP AD.n2 10)) = true := by quickRfl

end CertificateChecks.KernelMisc.RuInv.Neg

end
