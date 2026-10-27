module

public import Certificates.Data.Kernel.Misc.A7Nat
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelA7Nat

open CFSG.KD.A7Nat CFSG.KC.Ord

theorem stabK_2 : Nat.beq (stabK 33) 120 = true := by
  quickRfl

theorem stabK_4 : Nat.beq (stabK 33825) 72 = true := by
  quickRfl

theorem stabK_6 : Nat.beq (stabK 34636833) 360 = true := by
  quickRfl

theorem orbK_true : orbK = true := by
  quickRfl

theorem s0K_true : s0K = true := by
  quickRfl

theorem fixK_true : fixK = true := by
  quickRfl

theorem uK_1 : uK 15 33825 = true := by
  quickRfl

theorem uK_2 : uK 48 34603008 = true := by
  quickRfl

theorem uK_3 : uK 112 34636833 = true := by
  quickRfl

theorem cenK_true : cenK = true := by
  quickRfl

theorem yK_true : yK = true := by
  quickRfl

end CertificateChecks.KernelA7Nat

end
