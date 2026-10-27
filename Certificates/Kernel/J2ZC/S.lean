module

public import Certificates.Kernel.J2ZC.Data
public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CertificateChecks.J2ZCK

open CFSG.KC.Enum CFSG.KD.J2ZC

theorem s0 : sRange ET 0 0 0 RE 315 9 511 2835 PM 12 4095 NS IDN gS 3 true OT 0 0 0 RO NL false 0
    (fun _ => 0) 0 (fun _ => 0) 0 0 128 = true := by
  decide +kernel

end CertificateChecks.J2ZCK

end
