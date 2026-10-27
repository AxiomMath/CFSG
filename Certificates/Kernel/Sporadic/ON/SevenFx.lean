module

public import Certificates.Kernel.Sporadic.ON.SevenDefs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option Elab.async false

namespace CertificateChecks.KernelSpor.ON

theorem fx0 : fxOK 0 = true := by quickRfl
theorem fx1 : fxOK 1 = true := by quickRfl
theorem fx2 : fxOK 2 = true := by quickRfl
theorem fx3 : fxOK 3 = true := by quickRfl
theorem fx4 : fxOK 4 = true := by quickRfl
theorem fx5 : fxOK 5 = true := by quickRfl
theorem fx6 : fxOK 6 = true := by quickRfl
theorem fx7 : fxOK 7 = true := by quickRfl
theorem cu0 : cuOK 0 = true := by quickRfl
theorem cu1 : cuOK 1 = true := by quickRfl
theorem cu2 : cuOK 2 = true := by quickRfl
theorem cu3 : cuOK 3 = true := by quickRfl
theorem cu4 : cuOK 4 = true := by quickRfl
theorem cu5 : cuOK 5 = true := by quickRfl
theorem cu6 : cuOK 6 = true := by quickRfl
theorem cu7 : cuOK 7 = true := by quickRfl

end CertificateChecks.KernelSpor.ON

end
