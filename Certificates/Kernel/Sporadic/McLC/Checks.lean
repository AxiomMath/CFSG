module

public import Certificates.Kernel.Sporadic.McLC.Defs
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Sporadic.ON.Gen

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.McLC

open CFSG.KC.Enum

theorem kOK_ok : kOK = true := by quickRfl
theorem wordOK_ok : allN 3 (fun j => wordOK (Nat.add j 2)) = true := by quickRfl
theorem invL_ok : invL = true := by quickRfl
theorem tree_ok : allN 3 tree = true := by quickRfl
theorem schR_ok : allN 2 (fun i => schR (Nat.succ i)) = true := by quickRfl
theorem term_ok : term = true := by quickRfl
theorem trAll_ok : trAll = true := by quickRfl
theorem repOK_ok : repOK = true := by quickRfl

end CertificateChecks.KernelSpor.McLC

#kon_slices CertificateChecks.KernelSpor.McLC.sch0 0 5

end
