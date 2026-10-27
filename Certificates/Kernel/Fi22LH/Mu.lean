module

public import Certificates.Data.Kernel.Fi22.LHK
public import Certificates.Kernel.Fi22LH.Sel
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22LH

open CFSG.KS.Fi22LH CFSG.KD.Fi22LH

theorem mu_0 : muSlW R Z P QA lb0 (fd mt 0 16383) 0 = true := by quickRfl
theorem mu_1 : muSlW R Z P QA lb0 (fd mt 0 16383) 1 = true := by quickRfl
theorem mu_2 : muSlW R Z P QA lb0 (fd mt 0 16383) 2 = true := by quickRfl
theorem mu_3 : muSlW R Z P QA lb0 (fd mt 0 16383) 3 = true := by quickRfl
theorem mu_tree : muTreeW R Z P QA M G mq (fd mt 70 1023) = true := by quickRfl
theorem ml_ok : mlK mq ml (fd mt 70 1023) = true := by quickRfl

end CertificateChecks.KernelFi22LH
