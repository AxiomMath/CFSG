module

public import CFSG.Certificates.Kernel.Enum.ZChkI
public import Certificates.Kernel.HSZC.Data

public section

namespace CertificateChecks.HSZCK

open CFSG.KC.Enum CFSG.KD.HSZC

theorem w3 : zRangeI OT 0 0 0 RO 100 7 127 700 PM 15 32767 ZW ZL 8 9069 3023 = true := by
  decide +kernel

end CertificateChecks.HSZCK

end
