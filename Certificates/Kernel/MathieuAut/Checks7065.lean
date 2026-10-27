module

public import CFSG.Quasithin.Background.HMathieuNormInputs

public section

namespace CertificateChecks.KernelMathieuAut

open CFSG.Quasithin.H.Mathieu

set_option maxHeartbeats 4000000 in
theorem m23ArrsK : inAutOK m23AArr = true ∧ inAutOK m23BArr = true := by
  decide +kernel

end CertificateChecks.KernelMathieuAut

end
