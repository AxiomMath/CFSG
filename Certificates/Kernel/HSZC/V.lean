module

public import CFSG.Certificates.Kernel.Enum.ZCH
public import Certificates.Kernel.HSZC.Data

public section

namespace CertificateChecks.HSZCK

open CFSG.KC.Enum CFSG.KD.HSZC

theorem v0 : vRange OT 0 0 0 RO 100 7 127 PM zP zPI vP vC H2 H2 7 21161 14 = true := by
  decide +kernel

end CertificateChecks.HSZCK

end
