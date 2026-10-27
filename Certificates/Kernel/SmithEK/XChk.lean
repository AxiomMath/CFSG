module

public import Certificates.Data.Kernel.SmithEKX
public import Certificates.Kernel.SmithEK.XData

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE CFSG.SmithE.K

theorem c21264len : ix.D.length = 675 := by
  decide +kernel

theorem c21264co : ixCo pn.CP = true := by
  decide +kernel

theorem c21264valid : ixValid pn.CP (s2K pn.CL) [0, 1, 4, 10, 3]
    [(2, 0, 1, 4, 10), (5, 0, 4, 1, 10), (6, 0, 10, 1, 4), (7, 1, 10, 4, 3), (8, 0, 4, 3, 6),
      (9, 0, 1, 10, 8), (11, 1, 10, 4, 9), (12, 0, 11, 1, 4), (13, 0, 11, 1, 8), (14, 0, 10, 1, 8),
      (15, 0, 7, 1, 8), (16, 0, 4, 10, 3), (17, 0, 7, 1, 4), (18, 0, 7, 1, 16), (19, 0, 11, 1, 16),
      (20, 0, 10, 1, 16)] = true := by
  decide +kernel

theorem c21264frame :
    (Nat.xor ivAll (Nat.shiftLeft 1 0)).testBit 1 = true ∧
      (Nat.xor ivAll (ivLn pn.LI pn.LM 0 1)).testBit 4 = true ∧
      (Nat.xor ivAll (Nat.lor (ivLn pn.LI pn.LM 0 1)
        (Nat.lor (ivLn pn.LI pn.LM 0 4) (ivLn pn.LI pn.LM 1 4)))).testBit 10 = true ∧
      (Nat.land (Nat.xor (ivLn pn.LI pn.LM 0 1) (Nat.lor (Nat.shiftLeft 1 0)
        (Nat.shiftLeft 1 1))) (Nat.xor ivAll (ivLn pn.LI pn.LM 4 10))).testBit 3 = true := by
  decide +kernel

end CertificateChecks.KernelSmithEK
