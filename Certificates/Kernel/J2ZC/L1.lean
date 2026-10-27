module

public import CFSG.Certificates.Kernel.Enum.ZChk
public import Certificates.Kernel.J2ZC.Data

public section

namespace CertificateChecks.J2ZCK

open CFSG.KC.Enum CFSG.KD.J2ZC

theorem l1 : lRange OT 0 0 0 RO 315 9 511 2835 PM 12 4095 NL A AI B BI 315 315 = true := by
  decide +kernel
theorem z1 : zRange OT 0 0 0 RO 315 9 511 2835 PM 12 4095 NL zP zPI 3 315 315 = true := by
  decide +kernel

end CertificateChecks.J2ZCK

end
