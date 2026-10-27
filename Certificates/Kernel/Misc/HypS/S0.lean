module

public import Certificates.Kernel.Misc.HypData
public import Certificates.Kernel.Misc.HypD.LB
public import Certificates.Kernel.Misc.HypD.LI
public import Certificates.Kernel.Misc.XiD.HS
public import Certificates.Kernel.Misc.LinesData
public import Certificates.Data.Kernel.Misc.HypRunE
import CFSG.Certificates.Kernel.Common.Cover
import CFSG.Certificates.Kernel.Misc.HypSoundEarly

public section

set_option maxRecDepth 200000

namespace CFSG.KD.Misc.Hyp

open CFSG.KC.Misc.Hyp CFSG.KD.Misc.Lines CFSG.KD.Misc.Xi

theorem searchAllE0 : ∀ i < 128, searchKE PB LB HS LI NL RES (0 + i) 1 = true := by kc_cover 1

theorem searchAll0 : ∀ i < 128, searchK PB LB HS LI NL RES (0 + i) 1 = true :=
  fun i hi => searchK_of_searchKE (searchAllE0 i hi)

end CFSG.KD.Misc.Hyp

end
