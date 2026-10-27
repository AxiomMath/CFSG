module

public import Certificates.Kernel.TitsOver.Three.SEnum0
public import Certificates.Kernel.TitsOver.Three.SEnum1
public import Certificates.Kernel.TitsOver.Three.SEnum2
public import Certificates.Kernel.TitsOver.Three.SEnum3
public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CertificateChecks.KernelTitsOver.Three

open CFSG.KC.Enum

@[expose] noncomputable def ST (k q : Nat) : Nat :=
  nIf(Nat.beq k 0, S0E.T q, nIf(Nat.beq k 1, S1E.T q, nIf(Nat.beq k 2, S2E.T q, S3E.T q)))

@[expose] noncomputable def SC (k : Nat) : Nat :=
  nIf(Nat.beq k 0, S0E.cnt, nIf(Nat.beq k 1, S1E.cnt, nIf(Nat.beq k 2, S2E.cnt, S3E.cnt)))

end CertificateChecks.KernelTitsOver.Three

end
