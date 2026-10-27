module

public import Certificates.Data.Kernel.G24Wit.K
public import Certificates.Kernel.Misc.G24Data

public section

namespace CFSG.KC.G24Wit

theorem ch733006_wit : witK CFSG.KD.Misc.G24.Gb = true := by
  decide +kernel

end CFSG.KC.G24Wit
