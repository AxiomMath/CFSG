module

public import Certificates.Data.Kernel.Ly6117.Check
public import Certificates.Kernel.LyE81.Data
public import CFSG.Sporadic.Recognition.LyonsFinalLyInputs
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import Certificates.Kernel.Sporadic.RawGen
public import CFSG.Certificates.CosetTableShort
public import Mathlib

public section

set_option maxRecDepth 400000

#kc_repo #kc_items_root CertificateChecks.KernelLy6117.GD "Certificates/Kernel/Ly6117/data/gens.items"
  92425 8428617172528635650

#ks_chars CertificateChecks.KernelLy6117.LyK CFSG.Sporadic.Recognition.LyonsSims.LyFinal.kText

namespace CertificateChecks.KernelLy6117

open CFSG.KC.Enum CertificateChecks.KernelLyE81

@[expose] noncomputable def G (i : Nat) : Nat :=
  nIf(Nat.beq i 0, C, nIf(Nat.beq i 1, D, nIf(Nat.beq i 2, GD 0, nIf(Nat.beq i 3, GD 1,
    nIf(Nat.beq i 4, GD 2, GD 3)))))

@[expose] noncomputable def GI (i : Nat) : Nat := nIf(Nat.beq i 1, GD 4, G i)

@[expose] noncomputable def CDx (i : Nat) : Nat :=
  nIf(Nat.beq i 0, C, nIf(Nat.beq i 1, D, CFSG.KD.OrdLy.ONE))

@[expose] noncomputable def CDIx (i : Nat) : Nat :=
  nIf(Nat.beq i 0, C, nIf(Nat.beq i 1, GD 4, CFSG.KD.OrdLy.ONE))

end CertificateChecks.KernelLy6117

end
