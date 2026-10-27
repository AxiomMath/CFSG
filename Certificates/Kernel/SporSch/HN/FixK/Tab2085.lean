module

public import Certificates.Kernel.SporSch.HN.FixK.Tab
public import Certificates.Kernel.SporSch.HN.Pt2085Data
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_items_root CFSG.KD.HNXK.FIX2085
  "Certificates/Kernel/SporSch/HN/data/hnx_fix2085.bin" 40 5635073903040881300

public noncomputable section

namespace CFSG.KD.HNXK

@[expose] def fix2085 (k : Nat) : Bool := fixOk CFSG.KD.HNPt2085.GF FIX2085 0 k

end CFSG.KD.HNXK

end
