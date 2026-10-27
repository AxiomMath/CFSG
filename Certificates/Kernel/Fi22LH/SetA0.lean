module

public import Certificates.Data.Kernel.Fi22.LHK
public import Certificates.Kernel.Fi22LH.Sel
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22LH

open CFSG.KS.Fi22LH CFSG.KD.Fi22LH

theorem setA_0 : setSl QA al be 0 = true := by quickRfl
theorem setA_1 : setSl QA al be 1 = true := by quickRfl
theorem setA_2 : setSl QA al be 2 = true := by quickRfl
theorem setA_3 : setSl QA al be 3 = true := by quickRfl
theorem setA_4 : setSl QA al be 4 = true := by quickRfl
theorem setA_5 : setSl QA al be 5 = true := by quickRfl
theorem setA_6 : setSl QA al be 6 = true := by quickRfl
theorem setA_7 : setSl QA al be 7 = true := by quickRfl
theorem setA_8 : setSl QA al be 8 = true := by quickRfl
theorem setA_9 : setSl QA al be 9 = true := by quickRfl

end CertificateChecks.KernelFi22LH
