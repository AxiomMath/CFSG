module

public import Certificates.Kernel.E8K.L33Tabs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelE8K.L33

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.Clos CFSG.KC.Misc.M22 CFSG.KC.E8K

theorem genB : allN 5 (wordAt 26 (nthL A) 3 (nthW sw) (nthL G)) = true := by quickRfl
theorem treeB : allN 32 (treeAt (mul 26) (one 26) (nthL G) 5 (nthL E) (nthL PA)) = true := by
  quickRfl
theorem sortB : allN 32 (sortAt 32 (nthL E) (nthL SG)) = true := by quickRfl
theorem closedB : allN 32 (closedAt (mul 26) (nthL G) 5 32 (nthL E) (nthL CT)) = true := by
  quickRfl
theorem invB : allN 32 (invAt 26 (nthL E) (nthL MK)) = true := by quickRfl
theorem pairB : allN 32 (pairAt 26 32 (nthL E) (nthL MK) (nthL R)) = true := by quickRfl
theorem triB : allN 32 (triAt 32 (nthL MK) (nthL R) W) = true := by quickRfl
theorem witB : allW W (witAt 26 (nthL A) 3 2 32 (nthL E) (nthL MK) (nthL R)) = true := by
  quickRfl

end CertificateChecks.KernelE8K.L33

end
