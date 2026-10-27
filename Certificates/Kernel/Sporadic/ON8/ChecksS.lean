module

public import Certificates.Kernel.Sporadic.ON8.Defs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Sporadic.ON5.Defs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON8

theorem rel_ok : relOK = true := by quickRfl

theorem wit_ok : witOK = true := by quickRfl

theorem blk_ok : blkOK = true := by quickRfl

theorem v_sift : CertificateChecks.KernelSpor.ON3.siftM vK = true := by quickRfl

end CertificateChecks.KernelSpor.ON8

#kon_slices CertificateChecks.KernelSpor.ON8.mSel 0 20

end
