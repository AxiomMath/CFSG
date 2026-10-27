module

public import Certificates.Kernel.LocalComp.ExcO8E.DataSE
public import Certificates.Kernel.LocalComp.ExcO8E.Data48
public import Certificates.Kernel.LocalComp.ExcO8E.Data16
public import Certificates.Data.Kernel.Child3

public section

namespace CertificateChecks.KernelLC.ExcO8E

open CFSG.KC.Enum CFSG.KC.Child3

@[expose] noncomputable def slE (s : Nat) : Bool :=
  allBlk (Nat.mul 16 s) (fun j => bIf(Nat.blt j RE.N, repK 480 9 SE.S SE.SI 4 RE.CS RE.OFF RE.CI
    RE.E RE.P RE.L RE.K RE.S RE.SI RE.N 600 j, true)) 16

@[expose] noncomputable def sl48 (s : Nat) : Bool :=
  allBlk (Nat.mul 16 s) (fun j => bIf(Nat.blt j R48.N, repK 480 9 Q48.S Q48.SI 6 R48.CS R48.OFF
    R48.CI R48.E R48.P R48.L R48.K R48.S R48.SI R48.N 600 j, true)) 16

@[expose] noncomputable def sl16 (s : Nat) : Bool :=
  allBlk (Nat.mul 16 s) (fun j => bIf(Nat.blt j R16.N, repK 480 9 Q16.S Q16.SI 5 R16.CS R16.OFF
    R16.CI R16.E R16.P R16.L R16.K R16.S R16.SI R16.N 600 j, true)) 16

end CertificateChecks.KernelLC.ExcO8E

end
