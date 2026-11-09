module

public meta import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Kernel.SporSch.HN.GenNTree
import Certificates.Kernel.Misc.OmegaSix.MaxGen

namespace CFSG.KD.OmegaSix.GenX

meta def recM1 : List Nat :=
  (String.splitOn (include_str "MaxRec1.0.txt") ",").map String.toNat!

end CFSG.KD.OmegaSix.GenX

#kss_ntree CFSG.KD.OmegaSix.RM1 CFSG.KD.OmegaSix.GenX.recM1
