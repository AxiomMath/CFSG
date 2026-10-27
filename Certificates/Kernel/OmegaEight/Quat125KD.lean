module

public import Certificates.Kernel.OmegaEight.Quat125K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.Q125

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEight
open CertificateChecks.KernelO8

theorem kRange125 : allRoots roots (fun e => rootB e fun i k _ _ _ =>
    bAnd(Nat.blt i 8192, Nat.blt k 64)) = true := by quickRfl

theorem kLook125 : strictB (ycK saCodes yIdxT) (fun YP => strictB (tyLK YP q125Ty 1) fun L1 =>
    allN 38 fun k => bIf(Nat.beq (q125Ty k) 1, Nat.beq (lookL L1 (saAtK YP k)) (Nat.succ k),
      true)) = true := by quickRfl

theorem kLink125 : bAnd(Nat.beq (pc (AP.S 8) (mainK 0)) (pc (mainK 0) (AP.S 8)),
    Nat.beq (pc (AP.S 9) (mainK 0)) (pc (mainK 0) (AP.S 9))) = true := by quickRfl

theorem neg125Range : Bool.not (allRoots roots (fun e => rootB e fun i k _ _ _ =>
    bAnd(Nat.blt i 8192, Nat.blt k 10))) = true := by quickRfl

theorem neg125Look : Bool.not (strictB (ycK saCodes yIdxT) (fun YP => strictB (tyLK YP q125Ty 1)
    fun L1 => allN 38 fun k => bIf(Nat.beq (q125Ty k) 1,
      Nat.beq (lookL L1 (saAtK YP k)) (Nat.add k 2), true))) = true := by quickRfl

end CertificateChecks.KernelO8.Q125

end
