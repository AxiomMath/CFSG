module

public import Certificates.Kernel.UnitarySix.Sec3.C3920
public import Certificates.Kernel.UnitarySix.Sec3.K3920
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Enum CFSG.Monster.B.Co2
open CFSG.EvenSmallLie.UnitarySix.YamadaSec3 CFSG.EvenSmallLie.UnitarySix.YamadaHAut

theorem cA4_size : rcnt (CA4.LR 0) = 8 := by decide +kernel

set_option maxRecDepth 400000 in
theorem kL1_4 : l1Run 4 = true := by quickRfl
set_option maxRecDepth 400000 in
theorem kL1_5 : l1Run 5 = true := by quickRfl
set_option maxRecDepth 400000 in
theorem kL1_6 : l1Run 6 = true := by quickRfl
set_option maxRecDepth 400000 in
theorem kL1_7 : l1Run 7 = true := by quickRfl

end CertificateChecks.KernelU6.Sec3
