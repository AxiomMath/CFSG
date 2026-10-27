module

public import Certificates.Data.Kernel.SUSmall.Defs
public import Certificates.Kernel.SUSmall.Data

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.SUSmall

open CFSG.KC.SUSmall Certificates.SUSmall CFSG.StandardType.HdRo7SU.Small

theorem cat7_ok : catOK cat7 K7 33 = true := by decide +kernel

theorem none7_ok : NW7.all (noneOK cat7 K7 33) = true := by decide +kernel

theorem out7_ok : OW7.all (outOK cat7 K7 33) = true := by decide +kernel

theorem surv7_ok : survOK 33 SV7 DV7 NW7 OW7 = true := by decide +kernel

theorem subs7_ok : subsOK SV7 AL7 NW7 OW7 = true := by decide +kernel

theorem al7_ok : alOK K7 33 AL7 smAllowed7 = true := by decide +kernel

theorem cover7_ok : coverOK 7 K7 = true := by decide +kernel

theorem cat8_ok : catOK cat8 K8 44 = true := by decide +kernel

theorem none8_ok : NW8.all (noneOK cat8 K8 44) = true := by decide +kernel

theorem out8_ok : OW8.all (outOK cat8 K8 44) = true := by decide +kernel

theorem surv8_ok : survOK 44 SV8 DV8 NW8 OW8 = true := by decide +kernel

theorem subs8_ok : subsOK SV8 AL8 NW8 OW8 = true := by decide +kernel

theorem al8_ok : alOK K8 44 AL8 smAllowed8 = true := by decide +kernel

theorem cover8_ok : coverOK 8 K8 = true := by decide +kernel

end CFSG.KD.SUSmall

end
