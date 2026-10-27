module

public import Certificates.Kernel.OmegaEight.E4O8MembersK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.Q125

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEight
open CertificateChecks.KernelO8

@[expose] noncomputable def threeK (T : Nat) : Bool :=
  bAnd(pm T, bAnd(Nat.beq (pc T (pc T T)) pid, bAnd(e4Norms e4L e4U om0V T,
    Bool.not (Nat.beq (pc T e4U) (pc e4U T)))))

@[expose] noncomputable def twK (k : Nat) : Bool :=
  strictB (wO (e4WW k)) fun W => Nat.beq (pc W (mainK 0)) (pc (mainK 0) W)

theorem kThreeW125 : lettersK 17 (CFSG.ClassicalInvolution.Q3.TL4.E4O8.threeW ()) = true := by
  quickRfl

theorem kThree125 : threeK (wO (CFSG.ClassicalInvolution.Q3.TL4.E4O8.threeW ())) = true := by
  quickRfl

theorem kTw125 : bAnd(twK 1, bAnd(twK 3, twK 4)) = true := by quickRfl

end CertificateChecks.KernelO8.Q125

end
