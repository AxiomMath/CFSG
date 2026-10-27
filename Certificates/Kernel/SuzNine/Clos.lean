module

public import Certificates.Kernel.SuzNine.Data
public import Certificates.Data.Kernel.SuzNine.Defs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 500

public section

namespace CertificateChecks.KernelSuzNine

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.Clos CFSG.KC.SuzNine

theorem u_tree : allN 8192 (treeAt actK idKey UGT 4 UE UPA) = true := by quickRfl
theorem u_sort : allN 8192 (sortAt 8192 UE USG) = true := by quickRfl
theorem u_closed : allN 8192 (closedAt actK UGT 4 8192 UE UCT) = true := by quickRfl
theorem u_cen : allN 8192 (cenOK UE UCT 120) = true := by quickRfl
end CertificateChecks.KernelSuzNine

end
