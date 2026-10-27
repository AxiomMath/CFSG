module

public import Certificates.Kernel.SporSch.Co3.StabIt
public import CFSG.Certificates.Kernel.Lie.CT.Core
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co3SIC.Neg

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CertificateChecks.KernelSpor
open CFSG.KLie.CT (notB)

theorem neg_root : notB (levelK 276 9 (mask 9) (276 * 9) (mask (276 * 9)) (pidn 276 9) S SI TR TRI 8
    (pg 9 (mask 9) BP 4) (stepsAt 276 9 S 8 BP 5) (LR 5)) = true := by quickRfl

theorem neg_steps : notB (levelK 276 9 (mask 9) (276 * 9) (mask (276 * 9)) (pidn 276 9) S SI TR TRI 8
    (pg 9 (mask 9) BP 0) (stepsAt 276 9 S 8 BP 1) (LR 0)) = true := by quickRfl

theorem neg_lines : notB (allN 7 (fun j => Nat.beq (S j) (Co3SI.L (Nat.succ j)))) = true := by
  quickRfl

theorem neg_sift :
    notB (Co3C.sift (Nat.lor 1 (Nat.shiftLeft (Nat.shiftRight (pidn 276 9) 18) 18))) = true := by
  quickRfl

theorem neg_lev5 : notB (Nat.beq (rpt 9 (mask 9) (LR 5) 1) 108) = true := by quickRfl

end CertificateChecks.KernelSporSch.Co3SIC.Neg

end
