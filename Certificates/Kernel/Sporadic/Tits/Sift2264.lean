module

public import Certificates.Kernel.Sporadic.Tits.Words2264
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Tits2264

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def siftD (P : Nat) : Bool :=
  siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsD.LR TitsD.TRI TitsD.BP 6 0 P

@[expose] noncomputable def tdt (j : Nat) : Nat :=
  pcomp 1755 11 (mask 11) (G 1) (pcomp 1755 11 (mask 11) (TitsD.S j) (GI 1))

@[expose] noncomputable def toSift (k : Nat) : Nat :=
  nIf(Nat.beq k 0, G 0, nIf(Nat.beq k 1, G 2, nIf(Nat.beq k 2, G 3,
  nIf(Nat.beq k 3, pcomp 1755 11 (mask 11) (G 1) (G 1), nIf(Nat.beq k 4, tdt 0,
  nIf(Nat.beq k 5, tdt 1, nIf(Nat.beq k 6, TitsP.S 0, TitsP.S 1)))))))

theorem siftOK : allN 8 (fun k => bAnd(siftD (toSift k), permC (toSift k))) = true := by
  quickRfl

end CertificateChecks.KernelSpor.Tits2264

end
