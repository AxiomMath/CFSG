module

public import Certificates.Kernel.K36K.M22.Data
public import Certificates.Data.Kernel.K36K.Planes
public import Certificates.Data.K36SporM22
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000
set_option trace.profiler true
set_option trace.profiler.threshold 10

namespace CertificateChecks.KernelK36K.M22

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.CoreD2K CFSG.KS.K36K
open Certificates.CoreD2Perm Certificates.K36Spor

theorem k_sz : szOK 22 5 = true := by quickRfl
theorem k_gens : gensK 22 5 (vOf m22SData) GP GPI EG GT GTI = true := by quickRfl
theorem k_cen : cenK 22 5 m22SData.base.p m22SData.base.eW.length EG = true := by quickRfl
theorem k_v : vK 22 5 m22SData.base.p (EG 0) (EG (m22SData.ys.getD 0 0)) = true := by quickRfl
theorem k_cent : centSK 22 5 m22SData EG GT = true := by quickRfl
theorem k_words : wordsSK 22 5 m22SData GP GT GTI = true := by quickRfl

end CertificateChecks.KernelK36K.M22

end
