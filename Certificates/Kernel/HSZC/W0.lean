module

public import CFSG.Certificates.Kernel.Enum.ZChkI
public import Certificates.Kernel.HSZC.Data

public section

namespace CertificateChecks.HSZCK

open CFSG.KC.Enum CFSG.KD.HSZC

theorem z_letters : allN ZL (fun k => Nat.blt (wl ZW k) 2) = true := by decide +kernel
theorem w0 : zRangeI OT 0 0 0 RO 100 7 127 700 PM 15 32767 ZW ZL 8 0 3023 = true := by
  decide +kernel

end CertificateChecks.HSZCK

end
