module

public import Certificates.Kernel.E6WK.Data
public import Certificates.Kernel.E6Div.Data
public import Certificates.Data.Kernel.E6Div
import all Certificates.Data.Kernel.E6Div
import all Certificates.Data.Kernel.E6WK
import all Certificates.Data.TwE6WeylKill
import all CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeChar

public section

namespace CertificateChecks.KernelE6Div

open CFSG.KC.E6Div
open CFSG.KD.E6WK (vp ir)
open CFSG.KD.E6Div (wit w0)

set_option maxHeartbeats 0 in
theorem w0_check : w0Check vp ir w0 = true := by
  decide +kernel

end CertificateChecks.KernelE6Div
