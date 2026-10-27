module

public import Certificates.Kernel.Tits8074.Data
public import Certificates.Data.Kernel.Tits8074
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelT8074

open CFSG.KC.Tits8074

theorem w0 : walk L zc x0 0 = true := by quickRfl
theorem w1 : walk L zc x1 110 = true := by quickRfl
theorem w2 : walk L zc x2 220 = true := by quickRfl
theorem w3 : walk L zc x3 330 = true := by quickRfl
theorem w4 : walk L zc x4 440 = true := by quickRfl
theorem w5 : walk L zc x5 550 = true := by quickRfl
theorem w6 : walk L zc x6 660 = true := by quickRfl
theorem w7 : walk L zc x7 770 = true := by quickRfl
theorem w8 : walk L zc x8 880 = true := by quickRfl
theorem w9 : walk L zc x9 990 = true := by quickRfl
theorem w10 : walk L zc x10 1100 = true := by quickRfl
theorem w11 : walk L zc x11 1210 = true := by quickRfl
theorem w12 : walk L zc x12 1320 = true := by quickRfl
theorem w13 : walk L zc x13 1430 = true := by quickRfl
theorem w14 : walk L zc x14 1540 = true := by quickRfl
theorem w15 : walk L zc x15 1650 = true := by quickRfl

theorem good : Nat.beq (nGood x0 + nGood x1 + nGood x2 + nGood x3 + nGood x4 + nGood x5 +
    nGood x6 + nGood x7 + nGood x8 + nGood x9 + nGood x10 + nGood x11 + nGood x12 + nGood x13 +
    nGood x14 + nGood x15) 216 = true := by
  quickRfl

end CertificateChecks.KernelT8074

end
