module

public import Certificates.Data.Kernel.Misc.A7Cnt
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelA7Cnt

open CFSG.KD.A7Cnt CFSG.KD.A7Nat CFSG.KC.Ord CFSG.KC.LQT.P

theorem hLK_true : hLK = true := by
  quickRfl

theorem c1K_true : c1K = true := by
  quickRfl

theorem stK_1 : Nat.beq (stK f1L) 168 = true := by
  quickRfl

theorem stK_2 : Nat.beq (stK f2L) 168 = true := by
  quickRfl

theorem repK_true : repK = true := by
  quickRfl

theorem fxK_true : fxK = true := by
  quickRfl

theorem normK_72 : Nat.beq normK 72 = true := by
  quickRfl

theorem k1_120 : Nat.beq k1 120 = true := by
  quickRfl

theorem k2_72 : Nat.beq k2 72 = true := by
  quickRfl

theorem k3_360 : Nat.beq k3 360 = true := by
  quickRfl

theorem k4_145 : Nat.beq k4 145 = true := by
  quickRfl

theorem k5_1225 : Nat.beq k5 1225 = true := by
  quickRfl

theorem k6_721 : Nat.beq k6 721 = true := by
  quickRfl

theorem centK_24 : Nat.beq centK 24 = true := by
  quickRfl

theorem invK_true : invK = true := by
  quickRfl

end CertificateChecks.KernelA7Cnt

end
