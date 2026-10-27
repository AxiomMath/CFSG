module

public import Certificates.Kernel.LocalComp.L34FCent.Defs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.L34Aut
public import Certificates.Kernel.LocalComp.L34SChk

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34FCent

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.L34K
open CFSG.KLie.CT (andB orB notB)

theorem kc0 : fcent6126 0 15 = true := by quickRfl

theorem kc1 : fcent6126 15 15 = true := by quickRfl

theorem kc2 : fcent6126 30 15 = true := by quickRfl

theorem kc3 : fcent6126 45 15 = true := by quickRfl

theorem kc4 : fcent6126 60 15 = true := by quickRfl

theorem kc5 : fcent6126 75 15 = true := by quickRfl

theorem kc6 : fcent6126 90 15 = true := by quickRfl

theorem kc7 : fcent6126 105 15 = true := by quickRfl

theorem kc8 : fcent6126 120 15 = true := by quickRfl

theorem kc9 : fcent6126 135 15 = true := by quickRfl

theorem kc10 : fcent6126 150 15 = true := by quickRfl

theorem kc11 : fcent6126 165 15 = true := by quickRfl

theorem kconj : fconj6126 = true := by quickRfl

end CertificateChecks.KernelLC.L34FCent

end
