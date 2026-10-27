module

public import Certificates.Kernel.J4TreeNode.Sext
public import CFSG.Certificates.Kernel.J4TreeNode.Sound

public section

namespace CFSG.KC.J4TreeN

open CFSG.KC.J4Q CFSG.KD.J4Q CertificateChecks.KernelJ4Q

theorem sx_ok : ∀ t < 2048,
    tabs.sx.testBit t = (CFSG.ASVolI.burnsideJ4NP_sextArr ())[t]?.getD false := by
  intro t ht
  rw [Nat.eq_of_beq_eq_true sx_check, ← zMasks_eq]
  exact sxOf_testBit _ t ht

end CFSG.KC.J4TreeN
