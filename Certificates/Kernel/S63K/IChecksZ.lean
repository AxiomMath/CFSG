module

public import Certificates.Kernel.S63K.IDefs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelS63.ID

open CFSG.KC.S63K CFSG.KC.Enum CFSG.KS.SporSch.M24

theorem invG : (allN 8 fun k => Nat.beq (Nat.mod (CFSG.KC.F2W.mulW 24 (G k) (G k))
    (Nat.shiftLeft 1 576)) idM) = true := by
  quickRfl

theorem roots : bAnd(Nat.beq (ZP 0) (Nat.mod (wordK G idM [6, 0, 6, 0, 6, 0, 6, 0])
    (Nat.shiftLeft 1 576)), Nat.beq (TP 0) (Nat.mod (wordK G idM [6, 0, 6, 1, 6, 0, 6, 1])
    (Nat.shiftLeft 1 576))) = true := by
  quickRfl

theorem ztree : (allN 819 fun i => treeAtK cj ZP ZQ 8 i) = true := by quickRfl

theorem zdist : (allN 819 fun k => distAtK ZP ZS 819 k) = true := by quickRfl

#kc_each CertificateChecks.KernelS63.ID.ch21111U 0 4

theorem neg : bAnd(bIf(Nat.beq (ZP 0) (Nat.mod (wordK G idM [6, 0, 6, 1, 6, 0, 6, 1])
      (Nat.shiftLeft 1 576)), false, true),
    bAnd(bIf(treeAtK cj TP (fun i => Nat.add (TQ i) 1) 8 5, false, true),
    bAnd(bIf(treeAtK cj TP (fun i => Nat.mul 8 i) 8 5, false, true),
    bAnd(bIf(distAtK TP (fun k => nIf(Nat.beq k 0, TS 1, nIf(Nat.beq k 1, TS 0, TS k))) 68796 0,
      false, true),
    bAnd(bIf(tagAtK idM ZP 819 TP 68796 (CertificateChecks.KernelS63.HD.TP 1) 0, false, true),
      bIf(tagAtK idM ZP 819 TP 68796 (CertificateChecks.KernelS63.HD.TP 1) (Nat.add (UT 1) 1),
        false, true)))))) = true := by
  quickRfl

end CertificateChecks.KernelS63.ID

end
