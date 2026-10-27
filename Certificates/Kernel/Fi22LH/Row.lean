module

public import Certificates.Data.Kernel.Fi22.LHK
public import Certificates.Kernel.Fi22LH.Sel
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22LH

open CFSG.KS.Fi22LH CFSG.KD.Fi22LH

theorem row_0 : rowSlW R P QA lb0 0 = true := by quickRfl
theorem row_1 : rowSlW R P QA lb0 1 = true := by quickRfl
theorem row_2 : rowSlW R P QA lb0 2 = true := by quickRfl
theorem row_3 : rowSlW R P QA lb0 3 = true := by quickRfl
theorem row_4 : rowSlW R P QA lb0 4 = true := by quickRfl
theorem row_5 : rowSlW R P QA lb0 5 = true := by quickRfl
theorem row_6 : rowSlW R P QA lb0 6 = true := by quickRfl
theorem row_7 : rowSlW R P QA lb0 7 = true := by quickRfl
theorem rowInv : rowInvK P QA (bs lb0) = true := by quickRfl
theorem up_ok : upK up = true := by quickRfl
theorem star : starW al eb lb0 lb1 h0 h1 h2 up pd = true := by quickRfl
theorem fail : failK R al eb h1 = true := by quickRfl
theorem swap : swapK R C QA QB u lb0 lb1 (fd mt 42 16383) (fd mt 56 16383) = true := by quickRfl

end CertificateChecks.KernelFi22LH
