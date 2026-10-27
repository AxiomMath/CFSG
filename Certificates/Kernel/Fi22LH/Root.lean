module

public import Certificates.Data.Kernel.Fi22.LHK
public import Certificates.Kernel.Fi22LH.Sel
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22LH

open CFSG.KS.Fi22LH CFSG.KD.Fi22LH

theorem root_0 : rootW R X lb0 rq0 = true := by quickRfl
theorem root_1 : rootW R Y lb1 rq1 = true := by quickRfl
theorem comm_0 : commK R X lb0 cq0 = true := by quickRfl
theorem comm_1 : commK R Y lb1 cq1 = true := by quickRfl
theorem dom_0 : domSlW R lb1 0 = true := by quickRfl
theorem dom_1 : domSlW R lb1 1 = true := by quickRfl
theorem dom_2 : domSlW R lb1 2 = true := by quickRfl
theorem dom_3 : domSlW R lb1 3 = true := by quickRfl

end CertificateChecks.KernelFi22LH
