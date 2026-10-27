module

public import Certificates.Kernel.Misc.GL52.ClsTab
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.GL52K

open CFSG.KC.Misc.GLM CFSG.KC.Ord

theorem nOK_a : ∀ i < 3, ∀ j < 9, nOK i j = true := by
  intro i hi j hj
  interval_cases i <;> interval_cases j <;> quickRfl

theorem nOK_b : ∀ i < 3, ∀ j < 9, nOK (i + 3) j = true := by
  intro i hi j hj
  interval_cases i <;> interval_cases j <;> quickRfl

theorem nOK_c : ∀ i < 3, ∀ j < 9, nOK (i + 6) j = true := by
  intro i hi j hj
  interval_cases i <;> interval_cases j <;> quickRfl

end CertificateChecks.KernelMisc.GL52K

end
