module

public import Certificates.Data.Kernel.Fi22.LHK
public import Certificates.Kernel.Fi22LH.Sel
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22LH

open CFSG.KS.Fi22LH CFSG.KD.Fi22LH

theorem fix_0 : fixSl R Z 0 = true := by quickRfl
theorem fix_1 : fixSl R Z 1 = true := by quickRfl
theorem fix_2 : fixSl R Z 2 = true := by quickRfl
theorem fix_3 : fixSl R Z 3 = true := by quickRfl
theorem fix_4 : fixSl R Z 4 = true := by quickRfl
theorem fix_5 : fixSl R Z 5 = true := by quickRfl
theorem bi_ok : biK be bi = true := by quickRfl

end CertificateChecks.KernelFi22LH
