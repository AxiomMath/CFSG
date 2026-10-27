module

public import CFSG.Certificates.Kernel.Enum.Defs
public import Certificates.Kernel.HSZC.Data

public section

namespace CertificateChecks.HSZCK

open CFSG.KC.Enum CFSG.KD.HSZC

theorem l10 : lRange OT 0 0 0 RO 100 7 127 700 PM 15 32767 NL A AI B BI 19250 1925 = true := by
  decide +kernel

end CertificateChecks.HSZCK

end
