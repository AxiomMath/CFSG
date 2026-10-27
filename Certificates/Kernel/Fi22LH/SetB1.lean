module

public import Certificates.Data.Kernel.Fi22.LHK
public import Certificates.Kernel.Fi22LH.Sel
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22LH

open CFSG.KS.Fi22LH CFSG.KD.Fi22LH

theorem setB_10 : setSl QB al be 10 = true := by quickRfl
theorem setB_11 : setSl QB al be 11 = true := by quickRfl
theorem setB_12 : setSl QB al be 12 = true := by quickRfl
theorem setB_13 : setSl QB al be 13 = true := by quickRfl
theorem setB_14 : setSl QB al be 14 = true := by quickRfl
theorem setB_15 : setSl QB al be 15 = true := by quickRfl
theorem setB_16 : setSl QB al be 16 = true := by quickRfl
theorem setB_17 : setSl QB al be 17 = true := by quickRfl
theorem setB_18 : setSl QB al be 18 = true := by quickRfl
theorem setB_19 : setSl QB al be 19 = true := by quickRfl

end CertificateChecks.KernelFi22LH
