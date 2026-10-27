module

public import Certificates.Kernel.K36K.J2.Data
public import Certificates.Kernel.CoreD2K.J2.Data
public import Certificates.Data.Kernel.K36K.Planes
public import Certificates.Data.Kernel.Spor.PEnum
public import Certificates.Data.K36SporJ2
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option trace.profiler true
set_option trace.profiler.threshold 10

namespace CertificateChecks.KernelK36K.J2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.CoreD2K CFSG.KS.K36K
open Certificates.CoreD2Perm Certificates.K36Spor
open CertificateChecks.KernelCoreD2K.J2 (GP GPI)

theorem k3_gens : gensK 315 9 (vOf j2SData3) GP GPI RE3.G GT3 GTI3 = true := by quickRfl
theorem k3_ek : Nat.beq RE3.k j2SData3.base.eW.length = true := by quickRfl
theorem k3_eh : penumHdK (pidn 315 9) RE3.cnt 27 RE3.T RE3.PL = true := by quickRfl
theorem k3_ecnt : Nat.beq RE3.cnt 27 = true := by quickRfl
theorem k3_esl : penumSlK 315 9 (mask 9) (315 * 9) false RE3.G RE3.GI RE3.k RE3.cnt RE3.T RE3.PL
    RE3.POS RE3.SRT RE3.SRI 0 27 = true := by quickRfl
theorem k3_nab : nabK 315 9 j2SData3.base.eW.length RE3.G = true := by quickRfl
theorem k3_cen : cenK 315 9 j2SData3.base.p j2SData3.base.eW.length RE3.G = true := by quickRfl
theorem k3_lines : linesK 315 9 j2SData3.base.p (vOf j2SData3) RE3.G = true := by quickRfl
theorem k3_cent : centSK 315 9 j2SData3 RE3.G GT3 = true := by quickRfl
theorem k3_words : wordsSK 315 9 j2SData3 GP GT3 GTI3 = true := by quickRfl

theorem k5_gens : gensK 315 9 (vOf j2SData5) GP GPI EG5 GT5 GTI5 = true := by quickRfl
theorem k5_cen : cenK 315 9 j2SData5.base.p j2SData5.base.eW.length EG5 = true := by quickRfl
theorem k5_v : vK 315 9 j2SData5.base.p (EG5 0) (EG5 (j2SData5.ys.getD 0 0)) = true := by quickRfl
theorem k5_cent : centSK 315 9 j2SData5 EG5 GT5 = true := by quickRfl
theorem k5_words : wordsSK 315 9 j2SData5 GP GT5 GTI5 = true := by quickRfl

end CertificateChecks.KernelK36K.J2

end
