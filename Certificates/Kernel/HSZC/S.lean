module

public import CFSG.Certificates.Kernel.Enum.Defs
public import Certificates.Kernel.HSZC.Data

public section

namespace CertificateChecks.HSZCK

open CFSG.KC.Enum CFSG.KD.HSZC

theorem s0 : sRange ET 0 0 0 RE 100 7 127 700 PM 15 32767 NS IDN gS 3 true OT 0 0 0 RO NL false 0
    (fun _ => 0) 0 (fun _ => 0) 0 0 512 = true := by
  decide +kernel

end CertificateChecks.HSZCK

end
