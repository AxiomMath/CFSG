module

public import Certificates.Kernel.Sporadic.Tits.LocJ
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.TitsJT

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CertificateChecks.KernelSpor

@[expose] noncomputable def siftJ (G : Nat) : Bool :=
  siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsJ.LR TitsJ.TRI TitsJ.BP 4 0 G

@[expose] noncomputable def Z : Nat :=
  wordK 1755 11 (mask 11) (pidn 1755 11) TitsD.S TitsD.SI CFSG.Sporadic.Schreier.Tits.titsCenterWord

@[expose] noncomputable def C0 : Nat :=
  wordK 1755 11 (mask 11) (pidn 1755 11) TitsD.S TitsD.SI [3, 4, 13]

@[expose] noncomputable def C : Nat := pcomp 1755 11 (mask 11) C0 C0

@[expose] noncomputable def CI : Nat := pinvS 1755 11 (mask 11) C

@[expose] noncomputable def G (k : Nat) : Nat :=
  nIf(Nat.blt k 3, TitsD.S (nIf(Nat.beq k 0, 2, nIf(Nat.beq k 1, 3, 12))), C)

@[expose] noncomputable def GI (k : Nat) : Nat :=
  nIf(Nat.blt k 3, TitsD.SI (nIf(Nat.beq k 0, 2, nIf(Nat.beq k 1, 3, 12))), CI)

theorem sizeK : Nat.beq (rcnt (TitsJ.LR 0) * rcnt (TitsJ.LR 1) * rcnt (TitsJ.LR 2) *
    rcnt (TitsJ.LR 3)) 512 = true := by quickRfl

theorem zW : wordEqK 1755 11 (mask 11) (pidn 1755 11) TitsD.S TitsD.SI 13
    CFSG.Sporadic.Schreier.Tits.titsCenterWord Z = true := by quickRfl
theorem zC : canonK 1755 11 (mask 11) (1755 * 11) Z = true := by quickRfl
theorem zS : siftJ Z = true := by quickRfl

theorem cW : wordEqK 1755 11 (mask 11) (pidn 1755 11) TitsD.S TitsD.SI 13 [3, 4, 13] C0 = true := by
  quickRfl
theorem cC : canonK 1755 11 (mask 11) (1755 * 11) C0 = true := by quickRfl
theorem c5 : Nat.beq (pcomp 1755 11 (mask 11) (pcomp 1755 11 (mask 11) (pcomp 1755 11 (mask 11)
    (pcomp 1755 11 (mask 11) C C) C) C) C) (pidn 1755 11) = true := by quickRfl

theorem canG : allN 4 (fun k => canonK 1755 11 (mask 11) (1755 * 11) (G k)) = true := by quickRfl
theorem canGI : allN 4 (fun k => canonK 1755 11 (mask 11) (1755 * 11) (GI k)) = true := by quickRfl
theorem permGK : allN 4 (fun k => permOK 1755 11 (mask 11) (1755 * 11) (G k) (GI k)) = true := by
  quickRfl
theorem canS : allN 4 (fun k => canonK 1755 11 (mask 11) (1755 * 11) (TitsJ.S k)) = true := by
  quickRfl

theorem nK : allN 4 (fun k => allN 4 (fun j =>
    siftJ (pcomp 1755 11 (mask 11) (pcomp 1755 11 (mask 11) (G k) (TitsJ.S j)) (GI k)))) = true := by
  quickRfl

end CertificateChecks.KernelMisc.TitsJT

end
