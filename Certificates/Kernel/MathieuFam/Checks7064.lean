module

public import Certificates.Data.Kernel.Spor.Mathieu
public import CFSG.Quasithin.Background.HMathieuM21Inputs
import CFSG.Certificates.Kernel.Common.Harness
import Init.Data.Array.Basic
import Init.Data.List.Basic

public section

namespace CertificateChecks.KernelMathieuFam

open CFSG.KS.Mathieu CFSG.Quasithin.H.Mathieu

theorem m21K : mcheck 21 5 m21Data = true := by quickRfl

set_option maxHeartbeats 4000000 in
theorem m21ArrsK : inAutOK m21AArr = true ∧ inAutOK m21BArr = true := by
  decide +kernel

end CertificateChecks.KernelMathieuFam

end
