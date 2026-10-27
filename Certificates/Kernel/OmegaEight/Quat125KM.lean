module

public import Certificates.Kernel.OmegaEight.Roots127K
public import Certificates.Kernel.OmegaEight.E4O8NbrK
public import Certificates.Kernel.OmegaEight.E4O8MembersData
public import Certificates.Kernel.OmegaEight.Quat125Data
public import Certificates.Data.Kernel.O8.QuatO8M
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.Q125

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEight
open CertificateChecks.KernelO8

theorem kWLet125 : rowsLetK e4MR = true := by quickRfl

theorem kMB125 : allN 6300 (fun k => Nat.blt (MT k) (Nat.shiftLeft 1 240)) = true := by quickRfl

theorem kOmS125 : allN 8 (fun j => Nat.beq (OmP.S j) (AP.S j)) = true := by quickRfl

theorem kFixM125 : strictB (fixMK e4U om0V 240) (fun M => allN 240 fun p =>
    Nat.beq (nIf(bitK M p, 1, 0)) (nIf(bAnd(Nat.beq (pg 9 511 e4U p) p,
      Nat.beq (pg 9 511 om0V p) p), 1, 0))) = true := by quickRfl

theorem negFixM125 :Bool.not (strictB (fixMK e4U om0V 240) (fun M => allN 240 fun p =>
    Nat.beq (nIf(bitK M p, 0, 1)) (nIf(bAnd(Nat.beq (pg 9 511 e4U p) p,
      Nat.beq (pg 9 511 om0V p) p), 1, 0)))) = true := by quickRfl

theorem negWLet125 :Bool.not (rowsLetK (([9], (0, 0)) :: e4MR)) = true := by quickRfl

theorem neg125MB : Bool.not (allN 6300 (fun k => Nat.blt (MT k) (Nat.shiftLeft 1 239))) = true := by
  quickRfl

theorem neg125OmS : Bool.not (allN 8 (fun j => Nat.beq (OmP.S j) (AP.S (Nat.succ j)))) = true := by
  quickRfl

end CertificateChecks.KernelO8.Q125

end
