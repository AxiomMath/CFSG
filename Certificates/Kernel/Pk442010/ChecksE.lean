module

public import Certificates.Kernel.Pk442010.Grp

set_option maxRecDepth 400000
set_option maxHeartbeats 0

public section

namespace CertificateChecks.KernelPk442010

open CFSG.KC.Enum CFSG.KS CFSG.KC.A45Cls CFSG.KC.Pk442010

theorem eWit : eWK CP.N CP.T csW rR rB eW = true ∧ eAllK CP.N CP.T CP.S csW rR rB eW = true := by
  decide +kernel

theorem e9 : e9K CP.N CP.T eW = true := by decide +kernel

theorem eG : eGK CP.N CP.T CP.S g0L eW = true := by decide +kernel

end CertificateChecks.KernelPk442010

end
