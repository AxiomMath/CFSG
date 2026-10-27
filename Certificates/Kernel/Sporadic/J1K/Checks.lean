module

public import Certificates.Kernel.Sporadic.J1K.Defs
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Sporadic.ON.Gen

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.J1K

theorem orbHd_ok : orbHd = true := by quickRfl
theorem orbPt_ok : orbPt = true := by quickRfl
theorem orbSort_ok : orbSort = true := by quickRfl
theorem projSort_ok : projSort = true := by quickRfl
theorem invAB_ok : invAB = true := by quickRfl
theorem wordsOK_ok : wordsOK = true := by quickRfl
theorem invL_ok : invL = true := by quickRfl
theorem tree0_ok : tree0 = true := by quickRfl
theorem tree1_ok : tree1 = true := by quickRfl
theorem sch1_ok : sch1 = true := by quickRfl
theorem term_ok : term = true := by quickRfl
theorem subPt_ok : subPt = true := by quickRfl
theorem subRep_ok : subRep = true := by quickRfl
theorem subTree_ok : CFSG.KC.Enum.allN 21 subTree = true := by quickRfl
theorem imAt_ok : CFSG.KC.Enum.allN 21 imAt = true := by quickRfl
theorem der_ok : der = true := by quickRfl

end CertificateChecks.KernelSpor.J1K

#kon_slices CertificateChecks.KernelSpor.J1K.sch0 0 28

end
