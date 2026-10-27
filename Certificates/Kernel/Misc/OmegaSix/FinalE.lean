module

public import CFSG.Certificates.Kernel.Misc.OmegaSixESound
public import Certificates.Kernel.Misc.OmegaSix.Final
public import Certificates.Kernel.Misc.OmegaSix.ChecksE

public section

namespace CFSG.KD.OmegaSix

open CFSG.CGT.Foote82.OmegaSix CFSG.KC.OmegaSix

theorem enumCheck_ok : CFSG.CGT.Foote82.OmegaSix.enumCheck () = true :=
  enumM_of oMatA oMatB oHead oTab

theorem relCheck_ok : relCheck () = true := relM_of oMatA oMatB oRelM

end CFSG.KD.OmegaSix

end
