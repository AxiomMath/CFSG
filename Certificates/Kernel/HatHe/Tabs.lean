module

public import Certificates.Data.Kernel.HatHeK
public import Certificates.Kernel.HatHe.Data

public section

namespace CertificateChecks.KernelHatHe

open CFSG.KC.HatHe

@[expose] noncomputable def rd (w m P k : Nat) : Nat := fld(P, Nat.mul w k, m)

@[expose] noncomputable def E0 : Nat → Nat := rd 70 1180591620717411303423 CFSG.KD.HatHe.EP0
@[expose] noncomputable def Z0 : Nat → Nat := rd 70 1180591620717411303423 CFSG.KD.HatHe.ZP0
@[expose] noncomputable def PA0 : Nat → Nat := rd 32 4294967295 CFSG.KD.HatHe.PAP0
@[expose] noncomputable def SG0 : Nat → Nat := rd 16 65535 CFSG.KD.HatHe.SGP0
@[expose] noncomputable def CT0 : Nat → Nat := rd 16 65535 CFSG.KD.HatHe.CTP0
@[expose] noncomputable def MB0 : Nat → Nat := rd 16 65535 CFSG.KD.HatHe.MBP0
@[expose] noncomputable def E1 : Nat → Nat := rd 70 1180591620717411303423 CFSG.KD.HatHe.EP1
@[expose] noncomputable def Z1 : Nat → Nat := rd 70 1180591620717411303423 CFSG.KD.HatHe.ZP1
@[expose] noncomputable def PA1 : Nat → Nat := rd 32 4294967295 CFSG.KD.HatHe.PAP1
@[expose] noncomputable def SG1 : Nat → Nat := rd 16 65535 CFSG.KD.HatHe.SGP1
@[expose] noncomputable def CT1 : Nat → Nat := rd 16 65535 CFSG.KD.HatHe.CTP1
@[expose] noncomputable def MB1 : Nat → Nat := rd 16 65535 CFSG.KD.HatHe.MBP1

@[expose] noncomputable def W0 (j : Nat) : List Nat :=
  lsel (Nat.beq j 0) [4, 1, 4, 5, 4, 1, 4, 1]
    (lsel (Nat.beq j 1) [5, 1, 3, 4, 3, 8, 1, 4, 5] [4, 1, 3, 8, 3, 1, 4])

@[expose] noncomputable def W1 (j : Nat) : List Nat :=
  lsel (Nat.beq j 0) [1, 8, 8, 3, 8, 3, 8, 2] (lsel (Nat.beq j 1) [2, 8, 2, 3, 8, 3, 1]
    (lsel (Nat.beq j 2) [2, 1, 2, 1, 8, 3, 8, 3] [8, 8, 2, 3, 1]))

@[expose] noncomputable def dW0 : List Nat := [5, 3, 4, 8, 3, 1, 4, 8, 1]

@[expose] noncomputable def dR0 : List Nat := [1, 8, 4, 1, 3, 8, 4, 3, 5]

@[expose] noncomputable def dW1 : List Nat := [2, 1, 8, 1, 2, 8, 3, 8, 3, 2]

@[expose] noncomputable def dR1 : List Nat := [2, 3, 8, 3, 8, 2, 1, 8, 1, 2]

end CertificateChecks.KernelHatHe

end
