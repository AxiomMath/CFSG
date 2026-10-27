module

public import Certificates.Kernel.Misc.RuBase.Data
public import CFSG.Certificates.Kernel.Misc.RuBaseSound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.RawSound

public section

namespace CertificateChecks.KernelMisc.RuBase

open CFSG.KC.Enum CFSG.KC.Misc.RuInv

@[expose] noncomputable def gen3 (a b c l : Nat) : Nat := nIf(Nat.beq l 0, a, nIf(Nat.beq l 1, b, c))

@[expose] noncomputable def GC : Nat → Nat := gen2 CD.n0 CD.n1

@[expose] noncomputable def HC : Nat → Nat := gen3 CD.n2 CD.n3 CD.n4

@[expose] noncomputable def HIC : Nat → Nat := gen3 CD.n5 CD.n6 CD.n7

@[expose] noncomputable def GL : Nat → Nat := gen3 LD.n0 LD.n1 LD.n2

@[expose] noncomputable def HL : Nat → Nat := gen2 LD.n3 LD.n4

@[expose] noncomputable def HIL : Nat → Nat := gen2 LD.n5 LD.n6

end CertificateChecks.KernelMisc.RuBase

end
