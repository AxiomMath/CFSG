module

public import Certificates.Kernel.Sporadic.He.Chain2112
public import CFSG.Certificates.Kernel.Spor.PresCard
public import CFSG.Certificates.Kernel.Orders.He.RelsBind
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.BfsPinUnpack
public import Mathlib

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.He2112

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.Pres
open CFSG.Sporadic.HeldB CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen TauCeti

@[expose] noncomputable def G (i : Nat) : Nat := nIf(Nat.beq i 0, HeC.S 0, HeC.S 1)

@[expose] noncomputable def GI (i : Nat) : Nat := nIf(Nat.beq i 0, HeC.SI 0, HeC.SI 1)

end CertificateChecks.KernelSpor.He2112

end
