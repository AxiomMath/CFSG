module

public import Certificates.Kernel.Misc.KGroups.M11Checks
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.KGNeg

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.Clos CFSG.KC.Misc.KG CFSG.GH74.KGroups.M11
open CertificateChecks.KernelMisc.M11K

theorem ord_wrong : notB (orB (ordK 11 (AG 0) 4) (ordK 11 (AG 1) 2)) = true := by quickRfl

theorem pair_wrong : notB (pairK 11 (AG 0) (AG 1) [([false, true], 10)]) = true := by quickRfl

theorem cl_short : notB (allN 7920 (inC3At 11 E (AG 0) CLA.dropLast)) = true := by quickRfl

theorem e9_wrong : notB (e9K 11 (CLX.filter fun c => cubeOne 11 c)) = true := by quickRfl

theorem cent3_wrong : notB (cent3K 11 (one 11) CLX) = true := by quickRfl

theorem cent_wrong : notB (allN 7920 (centAt 11 E (AG 0) (AG 0))) = true := by quickRfl

theorem tree_wrong : notB (allR 0 16 (treeAt (mul 11) (one 11) AG 2 E fun k => PA (k + 1))) =
    true := by quickRfl

theorem closed_wrong : notB (allR 0 16 (closedAt (mul 11) AG 2 7920 E fun k => CT (k + 1))) =
    true := by quickRfl

theorem sort_wrong : notB (allN 7920 (sortAt 7920 E fun i => SG (Nat.xor i 1))) = true := by
  quickRfl

end CertificateChecks.KernelMisc.KGNeg

end
