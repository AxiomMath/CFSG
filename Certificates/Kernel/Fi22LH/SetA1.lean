module

public import Certificates.Data.Kernel.Fi22.LHK
public import Certificates.Kernel.Fi22LH.Sel
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22LH

open CFSG.KS.Fi22LH CFSG.KD.Fi22LH

theorem setA_10 : setSl QA al be 10 = true := by quickRfl
theorem setA_11 : setSl QA al be 11 = true := by quickRfl
theorem setA_12 : setSl QA al be 12 = true := by quickRfl
theorem setA_13 : setSl QA al be 13 = true := by quickRfl
theorem setA_14 : setSl QA al be 14 = true := by quickRfl
theorem setA_15 : setSl QA al be 15 = true := by quickRfl
theorem setA_16 : setSl QA al be 16 = true := by quickRfl
theorem setA_17 : setSl QA al be 17 = true := by quickRfl
theorem setA_18 : setSl QA al be 18 = true := by quickRfl
theorem setA_19 : setSl QA al be 19 = true := by quickRfl

end CertificateChecks.KernelFi22LH
