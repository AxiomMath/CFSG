module

public import Certificates.Kernel.LocalQT.SV.C4134S
public import Certificates.Kernel.Sporadic.He.Gens2112
public import Certificates.Data.Kernel.Misc.CentPt
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelSchreierFam.He260000

open CFSG.KC.Enum CFSG.KS CFSG.KS.Pres CFSG.KC.Misc.CentPt CertificateChecks.KernelSpor

@[expose] noncomputable def GS (i : Nat) : Nat := HeC.S (i % 9)

@[expose] noncomputable def GSI (i : Nat) : Nat := HeC.SI (i % 9)

@[expose] def w3 : List (Nat × Bool) :=
  [(6, true), (7, true), (1, false), (1, false), (6, true), (1, true), (1, true), (4, false),
    (8, true), (3, true), (4, true), (0, true), (4, true), (6, true), (8, true), (3, true)]

@[expose] def w20 : List (Nat × Bool) :=
  [(4, true), (0, true), (1, true), (5, true), (4, true), (1, true), (0, true), (4, false),
    (3, true), (4, false), (4, false), (4, false), (8, true), (7, true), (3, true), (8, true)]

theorem cent : centPtK 8330 14 2048 CFSG.KD.LQT.C4134.SY.E [3, 20] [0] 1 = true := by
  decide +kernel

theorem word3 : Nat.beq (CFSG.KD.LQT.C4134.SY.E 3) (wordPK 8330 14 GS GSI w3) = true := by
  decide +kernel

theorem word20 : Nat.beq (CFSG.KD.LQT.C4134.SY.E 20) (wordPK 8330 14 GS GSI w20) = true := by
  decide +kernel

end CertificateChecks.KernelSchreierFam.He260000

end
