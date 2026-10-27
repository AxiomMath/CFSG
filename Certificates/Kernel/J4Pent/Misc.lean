module

public import Certificates.Kernel.J4Pent.Defs
public import CFSG.Certificates.Kernel.Common.Cover
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Pent

open CFSG.KC.J4Pent CFSG.KD.J4Pent CFSG.KC.J4Q CFSG.KD.J4Q

theorem wf_ok : bAnd(allLt (Nat.shiftLeft 1 NL) 112 R,
    bAnd(allB (allLt (Nat.shiftLeft 1 NL) 112) Z, bAnd(Nat.beq (lenK Z) 4,
      bAnd(allB stepWf WS, Nat.beq (lenK WS) 41)))) = true := by quickRfl

theorem incr_ok : incrS ONES R = true := by quickRfl

theorem ties_ok : ∀ t < 6720, tieF t = true := by kc_cover 512

theorem fxl_ok : bAnd(incrP FXL none, bAnd(allB (fun p => memN p.1 (tiesAt p.2).1) FXL,
    bAnd(allB (fun p => Nat.blt 0 p.2) FXL, Nat.beq (lenK FXL) fixTotal))) = true := by
  quickRfl

theorem sum_ok : (fun r => Nat.beq (Nat.add (Nat.mul (Nat.sub NL r.2) 6720) r.1) 173067389)
    (runSum FXL 0 0) = true := by quickRfl

theorem des_ok : bAnd(incrP (mapP DL) none,
    bAnd(allB (fun l => bIf(Nat.beq l LF, true, anyB (fun p => Nat.beq p.1 l) WD)) DL,
    bAnd(Nat.beq (vecJ rm (laneV R LF) (getN one XG 0)) (laneV R LF),
    bAnd(Nat.beq (lenK WD) 30, Nat.beq (lenK D4) 30)))) = true := by quickRfl

theorem wit_ok : ∀ j < 30, witF j = true := by kc_cover 30

end CertificateChecks.KernelJ4Pent

end
