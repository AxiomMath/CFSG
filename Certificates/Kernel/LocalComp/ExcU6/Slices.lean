module

public import Certificates.Kernel.LocalComp.ExcU6.Data2
public import Certificates.Kernel.LocalComp.ExcU6.Data3
public import Certificates.Kernel.LocalComp.ExcU6.DataS
public import Certificates.Kernel.UnitarySix.ASTQ
public import Certificates.Data.Kernel.Child3

public section

namespace CertificateChecks.KernelLC.ExcU6

open CFSG.KC.Enum CFSG.KC.Child3 CertificateChecks.KernelU6

@[expose] noncomputable def sl2 (s : Nat) : Bool :=
  allBlk (Nat.mul 16 s) (fun j => bIf(Nat.blt j R2.N, repK 693 10 Q2.S Q2.SI 8 R2.CS R2.OFF R2.CI
    R2.E R2.P R2.L R2.K R2.S R2.SI R2.N 600 j, true)) 16

@[expose] noncomputable def sl3 (s : Nat) : Bool :=
  allBlk (Nat.mul 16 s) (fun j => bIf(Nat.blt j R3.N, repK 693 10 Q3.S Q3.SI 11 R3.CS R3.OFF R3.CI
    R3.E R3.P R3.L R3.K R3.S R3.SI R3.N 600 j, true)) 16

@[expose] noncomputable def slS (s : Nat) : Bool :=
  allBlk (Nat.mul 16 s) (fun j => bIf(Nat.blt j RS.N, repK 693 10 SQ.S SQ.SI 13 RS.CS RS.OFF RS.CI
    RS.E RS.P RS.L RS.K RS.S RS.SI RS.N 100 j, true)) 16

end CertificateChecks.KernelLC.ExcU6

end
