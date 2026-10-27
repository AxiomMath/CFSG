module

public import Certificates.Kernel.E8K.U33Tabs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelE8K.U33

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.Clos CFSG.KC.Misc.M22 CFSG.KC.E8K

theorem genB : allN 6 (wordAt 28 (nthL A) 3 (nthW sw) (nthL G)) = true := by quickRfl
theorem treeB : allN 64 (treeAt (mul 28) (one 28) (nthL G) 6 (nthL E) (nthL PA)) = true := by
  quickRfl
theorem sortB : allN 64 (sortAt 64 (nthL E) (nthL SG)) = true := by quickRfl
theorem closedB : allN 64 (closedAt (mul 28) (nthL G) 6 64 (nthL E) (nthL CT)) = true := by
  quickRfl
theorem invB : allN 64 (invAt 28 (nthL E) (nthL MK)) = true := by quickRfl
theorem pairB : allN 64 (pairAt 28 64 (nthL E) (nthL MK) (nthL R)) = true := by quickRfl
theorem triB : allN 64 (triAt 64 (nthL MK) (nthL R) W) = true := by quickRfl
theorem witB : allW W (witAt 28 (nthL A) 3 2 64 (nthL E) (nthL MK) (nthL R)) = true := by
  quickRfl

end CertificateChecks.KernelE8K.U33

end
